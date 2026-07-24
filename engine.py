debug = False
depth_debug = False
performance_debug = False

from board import (WHITE, BLACK, PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING, sq, lsb_index, popcount,
                    piece_value, piece_square_table_king, NONE_PIECE)
from attacks import KNIGHT_ATTACKS, KING_ATTACKS, PAWN_ATTACKS, FILE_MASKS, PASSED_PAWN_MASK_WHITE, PASSED_PAWN_MASK_BLACK
from moves import (EN_PASSANT, opposite, is_in_check, generate_legal_moves,
                    generate_legal_captures, make_move, unmake_move)
from magic import (BISHOP_MASKS, BISHOP_MAGICS, BISHOP_SHIFTS, BISHOP_TABLES,
                    ROOK_MASKS, ROOK_MAGICS, ROOK_SHIFTS, ROOK_TABLES,
                    get_bishop_attacks, get_rook_attacks, get_queen_attacks)
from board import FULL
from zobrist import ZOBRIST_EP_FILE, ZOBRIST_TURN, compute_pawn_hash
import time
import sys
import cProfile
import pstats

TT_SIZE_BITS = 22
TT_SIZE = 1 << TT_SIZE_BITS
TT_MASK = TT_SIZE - 1

TT_HASH  = [0] * TT_SIZE
TT_DEPTH = [-1] * TT_SIZE
TT_SCORE = [0.0] * TT_SIZE
TT_BOUND = [0] * TT_SIZE
TT_GEN   = [0] * TT_SIZE
TT_MOVE  = [-1] * TT_SIZE
TT_GENERATION = 0
SEARCH_START = 0
SEARCH_LIMIT = 0
move_stack = []
KILLER = [[None, None] for _ in range(128)]
HISTORY = [[0 for _ in range(64)] for _ in range(64)]
STATIC_EVAL = [0.0] * 128
CORR_HIST_BITS = 16
CORR_HIST_SIZE = 1 << CORR_HIST_BITS
CORR_HIST_MASK = CORR_HIST_SIZE - 1
CORRECTION_HISTORY = [[0.0] * CORR_HIST_SIZE for _ in range(2)]
NODE_COUNT = 0
EVAL_CACHE = {}
MATE_VALUE = 100000
MATE_THRESHOLD = MATE_VALUE - 1000
thinking_time = 21
SEARCH_ABORTED = False


def _has_pawn(board, color, rank, file):
    return (board.bitboards[color][PAWN] >> sq(file, rank)) & 1

def bewerte_material(board):
    phase = board.phase
    if phase > 24:
        phase = 24  # Sicherheitsnetz falls durch Bug > 24
    if phase < 0:
        phase = 0
    total_material = (board.material_score_mg * phase + board.material_score_eg * (24 - phase)) / 24
    material = 0.0
    white_king_bb = board.bitboards[WHITE][KING]
    black_king_bb = board.bitboards[BLACK][KING]
    white_king_pos = (white_king_bb & -white_king_bb).bit_length() - 1 if white_king_bb else sq(4, 0)
    black_king_pos = (black_king_bb & -black_king_bb).bit_length() - 1 if black_king_bb else sq(4, 7)

    white_pawn_bb = board.bitboards[WHITE][PAWN]
    black_pawn_bb = board.bitboards[BLACK][PAWN]
    wk_rank, wk_file = white_king_pos >> 3, white_king_pos & 7
    bk_rank, bk_file = black_king_pos >> 3, black_king_pos & 7
    fm = FILE_MASKS
    white_pawns_per_col = [(white_pawn_bb & fm[0]).bit_count(), (white_pawn_bb & fm[1]).bit_count(),
                           (white_pawn_bb & fm[2]).bit_count(), (white_pawn_bb & fm[3]).bit_count(),
                           (white_pawn_bb & fm[4]).bit_count(), (white_pawn_bb & fm[5]).bit_count(),
                           (white_pawn_bb & fm[6]).bit_count(), (white_pawn_bb & fm[7]).bit_count()]
    black_pawns_per_col = [(black_pawn_bb & fm[0]).bit_count(), (black_pawn_bb & fm[1]).bit_count(),
                           (black_pawn_bb & fm[2]).bit_count(), (black_pawn_bb & fm[3]).bit_count(),
                           (black_pawn_bb & fm[4]).bit_count(), (black_pawn_bb & fm[5]).bit_count(),
                           (black_pawn_bb & fm[6]).bit_count(), (black_pawn_bb & fm[7]).bit_count()]
    piece_count = board.all_occupancy.bit_count()

    bb = white_pawn_bb
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        if (PASSED_PAWN_MASK_WHITE[s] & black_pawn_bb) == 0:
            rank = s >> 3
            file = s & 7
            material -= 0.2 + (rank * rank) * 0.03
            king_dist_to_queen_sq = max(abs(bk_rank - 7), abs(bk_file - file))
            pawn_dist_to_queen_sq = 7 - rank
            tempo = 0 if board.side_to_move == BLACK else 1
            if king_dist_to_queen_sq > pawn_dist_to_queen_sq + tempo:
                material -= 0.5
    bb = black_pawn_bb
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        if (PASSED_PAWN_MASK_BLACK[s] & white_pawn_bb) == 0:
            rank = s >> 3
            file = s & 7
            material += 0.2 + ((7 - rank) * (7 - rank)) * 0.03
            king_dist_to_queen_sq = max(abs(wk_rank - 0), abs(wk_file - file))
            pawn_dist_to_queen_sq = rank
            tempo = 0 if board.side_to_move == WHITE else 1
            if king_dist_to_queen_sq > pawn_dist_to_queen_sq + tempo:
                material += 0.5

    white_bishops = board.bitboards[WHITE][BISHOP].bit_count()
    black_bishops = board.bitboards[BLACK][BISHOP].bit_count()
    if white_bishops >= 2:
        material -= 0.3
    if black_bishops >= 2:
        material += 0.3

    white_rooks = []
    bb = board.bitboards[WHITE][ROOK]
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        white_rooks.append(s & 7)
    black_rooks = []
    bb = board.bitboards[BLACK][ROOK]
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        black_rooks.append(s & 7)

    if piece_count <= 6 and abs(total_material) >= 3:
        if total_material < 0:
            edge_dist = min(bk_rank, 7 - bk_rank, bk_file, 7 - bk_file)
            king_dist = max(abs(wk_rank - bk_rank), abs(wk_file - bk_file))
            material -= (3 - edge_dist) * 0.1
            material -= (7 - king_dist) * 0.05
        if total_material > 0:
            edge_dist = min(wk_rank, 7 - wk_rank, wk_file, 7 - wk_file)
            king_dist = max(abs(bk_rank - wk_rank), abs(bk_file - wk_file))
            material += (3 - edge_dist) * 0.1
            material += (7 - king_dist) * 0.05

    for file in range(8):
        if white_pawns_per_col[file] >= 2:
            material += 0.3 * (white_pawns_per_col[file] - 1)
        if black_pawns_per_col[file] >= 2:
            material -= 0.3 * (black_pawns_per_col[file] - 1)
        if white_pawns_per_col[file] > 0:
            left = white_pawns_per_col[file - 1] if file > 0 else 0
            right = white_pawns_per_col[file + 1] if file < 7 else 0
            if left == 0 and right == 0:
                material += 0.2 * white_pawns_per_col[file]
        if black_pawns_per_col[file] > 0:
            left = black_pawns_per_col[file - 1] if file > 0 else 0
            right = black_pawns_per_col[file + 1] if file < 7 else 0
            if left == 0 and right == 0:
                material -= 0.2 * black_pawns_per_col[file]

    if piece_count > 6:
        white_undeveloped = 0
        if (board.bitboards[WHITE][KNIGHT] >> sq(1, 0)) & 1: white_undeveloped += 1
        if (board.bitboards[WHITE][KNIGHT] >> sq(6, 0)) & 1: white_undeveloped += 1
        if (board.bitboards[WHITE][BISHOP] >> sq(2, 0)) & 1: white_undeveloped += 1
        if (board.bitboards[WHITE][BISHOP] >> sq(5, 0)) & 1: white_undeveloped += 1
        material += white_undeveloped * 0.1

        black_undeveloped = 0
        if (board.bitboards[BLACK][KNIGHT] >> sq(1, 7)) & 1: black_undeveloped += 1
        if (board.bitboards[BLACK][KNIGHT] >> sq(6, 7)) & 1: black_undeveloped += 1
        if (board.bitboards[BLACK][BISHOP] >> sq(2, 7)) & 1: black_undeveloped += 1
        if (board.bitboards[BLACK][BISHOP] >> sq(5, 7)) & 1: black_undeveloped += 1
        material -= black_undeveloped * 0.1
        white_king_safety = 0
        for dc in (-1, 0, 1):
            c = wk_file + dc
            if 0 <= c <= 7:
                if wk_rank + 1 <= 7 and (white_pawn_bb >> sq(c, wk_rank + 1)) & 1:
                    white_king_safety += 1
                elif wk_rank + 2 <= 7 and (white_pawn_bb >> sq(c, wk_rank + 2)) & 1:
                    white_king_safety += 0.5
        material -= white_king_safety * 0.15

        black_king_safety = 0
        for dc in (-1, 0, 1):
            c = bk_file + dc
            if 0 <= c <= 7:
                if bk_rank - 1 >= 0 and (black_pawn_bb >> sq(c, bk_rank - 1)) & 1:
                    black_king_safety += 1
                elif bk_rank - 2 >= 0 and (black_pawn_bb >> sq(c, bk_rank - 2)) & 1:
                    black_king_safety += 0.5
        material += black_king_safety * 0.15

        if 3 <= wk_file <= 4: material += 0.3
        if 3 <= bk_file <= 4: material -= 0.3

        for dc in (-1, 0, 1):
            c = wk_file + dc
            if 0 <= c <= 7:
                if white_pawns_per_col[c] == 0 and black_pawns_per_col[c] == 0:
                    material += 0.2
                elif white_pawns_per_col[c] == 0:
                    material += 0.1
        for dc in (-1, 0, 1):
            c = bk_file + dc
            if 0 <= c <= 7:
                if white_pawns_per_col[c] == 0 and black_pawns_per_col[c] == 0:
                    material -= 0.2
                elif black_pawns_per_col[c] == 0:
                    material -= 0.1

        black_major_attackers = 0
        occ = board.all_occupancy
        straight_enemy = board.bitboards[BLACK][ROOK] | board.bitboards[BLACK][QUEEN]
        diag_enemy = board.bitboards[BLACK][BISHOP] | board.bitboards[BLACK][QUEEN]
        if get_rook_attacks(white_king_pos, occ) & straight_enemy:
            black_major_attackers += 1
        if get_bishop_attacks(white_king_pos, occ) & diag_enemy:
            black_major_attackers += 1
        material += black_major_attackers * 0.4

        white_straight_enemy = board.bitboards[WHITE][ROOK] | board.bitboards[WHITE][QUEEN]
        white_diag_enemy = board.bitboards[WHITE][BISHOP] | board.bitboards[WHITE][QUEEN]
        white_major_attackers = 0
        if get_rook_attacks(black_king_pos, occ) & white_straight_enemy:
            white_major_attackers += 1
        if get_bishop_attacks(black_king_pos, occ) & white_diag_enemy:
            white_major_attackers += 1
        material -= white_major_attackers * 0.4

    occ = board.all_occupancy
    w_occ = board.occupancy[WHITE]
    b_occ = board.occupancy[BLACK]

    white_mobility = 0
    bb = board.bitboards[WHITE][ROOK]
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        f = s & 7
        atk = get_rook_attacks(s, occ)
        white_mobility += (atk & ~w_occ).bit_count()
        if white_pawns_per_col[f] == 0 and black_pawns_per_col[f] == 0:
            material -= 0.2
        elif white_pawns_per_col[f] == 0:
            material -= 0.1

    black_mobility = 0
    bb = board.bitboards[BLACK][ROOK]
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        f = s & 7
        atk = get_rook_attacks(s, occ)
        black_mobility += (atk & ~b_occ).bit_count()
        if white_pawns_per_col[f] == 0 and black_pawns_per_col[f] == 0:
            material += 0.2
        elif black_pawns_per_col[f] == 0:
            material += 0.1

    bb = board.bitboards[WHITE][KNIGHT]
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        white_mobility += (KNIGHT_ATTACKS[s] & ~w_occ).bit_count()
    bb = board.bitboards[BLACK][KNIGHT]
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        black_mobility += (KNIGHT_ATTACKS[s] & ~b_occ).bit_count()

    bb = board.bitboards[WHITE][BISHOP]
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        white_mobility += (get_bishop_attacks(s, occ) & ~w_occ).bit_count()
    bb = board.bitboards[BLACK][BISHOP]
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        black_mobility += (get_bishop_attacks(s, occ) & ~b_occ).bit_count()

    bb = board.bitboards[WHITE][QUEEN]
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        white_mobility += (get_queen_attacks(s, occ) & ~w_occ).bit_count()
    bb = board.bitboards[BLACK][QUEEN]
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        black_mobility += (get_queen_attacks(s, occ) & ~b_occ).bit_count()

    material -= white_mobility * 0.02
    material += black_mobility * 0.02


    return total_material + material


def _attackers_to(board, square, occ, diag, straight):
    attackers = 0
    attackers |= PAWN_ATTACKS[BLACK][square] & board.bitboards[WHITE][PAWN]
    attackers |= PAWN_ATTACKS[WHITE][square] & board.bitboards[BLACK][PAWN]
    attackers |= KNIGHT_ATTACKS[square] & (board.bitboards[WHITE][KNIGHT] | board.bitboards[BLACK][KNIGHT])
    attackers |= KING_ATTACKS[square] & (board.bitboards[WHITE][KING] | board.bitboards[BLACK][KING])
    masked_b = occ & BISHOP_MASKS[square]
    idx_b = ((masked_b * BISHOP_MAGICS[square]) & FULL) >> BISHOP_SHIFTS[square]
    attackers |= BISHOP_TABLES[square][idx_b] & diag
    masked_r = occ & ROOK_MASKS[square]
    idx_r = ((masked_r * ROOK_MAGICS[square]) & FULL) >> ROOK_SHIFTS[square]
    attackers |= ROOK_TABLES[square][idx_r] & straight
    return attackers & occ

def _least_valuable_attacker(board, attackers_bb, side):
    for pt in (PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING):
        bb = attackers_bb & board.bitboards[side][pt]
        if bb:
            return lsb_index(bb), pt
    return None, None


def SEE(board, move):
    from_sq = move & 0x3F
    to_sq = (move >> 6) & 0x3F
    captured_piece = (move >> 16) & 0x7
    flag = (move >> 22) & 0x7
    capsq = (move >> 25) & 0x3F

    if captured_piece == NONE_PIECE:
        return 0

    attacker_side = board.color_at[from_sq]
    attacker_type = board.piece_at_sq[from_sq]

    occ = board.all_occupancy & ~(1 << from_sq)
    if flag == EN_PASSANT:
        occ &= ~(1 << capsq)

    diag = (board.bitboards[WHITE][BISHOP] | board.bitboards[WHITE][QUEEN] |
            board.bitboards[BLACK][BISHOP] | board.bitboards[BLACK][QUEEN])
    straight = (board.bitboards[WHITE][ROOK] | board.bitboards[WHITE][QUEEN] |
                board.bitboards[BLACK][ROOK] | board.bitboards[BLACK][QUEEN])

    static_attackers = (
        (PAWN_ATTACKS[WHITE][to_sq] & board.bitboards[BLACK][PAWN]) |
        (PAWN_ATTACKS[BLACK][to_sq] & board.bitboards[WHITE][PAWN]) |
        (KNIGHT_ATTACKS[to_sq] & (board.bitboards[WHITE][KNIGHT] | board.bitboards[BLACK][KNIGHT])) |
        (KING_ATTACKS[to_sq] & (board.bitboards[WHITE][KING] | board.bitboards[BLACK][KING]))
    )

    def _sliding_attackers(cur_occ):
        masked_b = cur_occ & BISHOP_MASKS[to_sq]
        idx_b = ((masked_b * BISHOP_MAGICS[to_sq]) & FULL) >> BISHOP_SHIFTS[to_sq]
        masked_r = cur_occ & ROOK_MASKS[to_sq]
        idx_r = ((masked_r * ROOK_MAGICS[to_sq]) & FULL) >> ROOK_SHIFTS[to_sq]
        return ((BISHOP_TABLES[to_sq][idx_b] & diag) | (ROOK_TABLES[to_sq][idx_r] & straight)) & cur_occ

    gains = [piece_value[captured_piece]]
    piece_on_square_value = piece_value[attacker_type]
    side = opposite(attacker_side)
    attackers_bb = (static_attackers & occ) | _sliding_attackers(occ)

    while True:
        sq_att, pt_att = _least_valuable_attacker(board, attackers_bb, side)
        if sq_att is None:
            break
        gains.append(piece_on_square_value - gains[-1])
        occ &= ~(1 << sq_att)
        attackers_bb = (static_attackers & occ) | _sliding_attackers(occ)
        piece_on_square_value = piece_value[pt_att]
        side = opposite(side)

    for i in range(len(gains) - 1, 0, -1):
        gains[i - 1] = -max(-gains[i - 1], gains[i])

    return gains[0]


def gives_check(board, move):
    make_move(board, move)
    result = is_in_check(board, board.side_to_move)
    unmake_move(board)
    return result

def move_score(move, depth, board, piece, captured_piece, flag):
    if captured_piece != NONE_PIECE or flag == EN_PASSANT:
        see_value = SEE(board, move)
        if see_value > 0:
            return 900000 + see_value, see_value
        elif see_value == 0:
            return 800000, see_value
        else:
            return -100000 + see_value, see_value
    killer0 = KILLER[depth][0]
    killer1 = KILLER[depth][1]
    from_sq = move & 0x3F
    to_sq = (move >> 6) & 0x3F
    if killer0 is not None and from_sq == (killer0 & 0x3F) and to_sq == ((killer0 >> 6) & 0x3F):
        return 700000, None
    if killer1 is not None and from_sq == (killer1 & 0x3F) and to_sq == ((killer1 >> 6) & 0x3F):
        return 600000, None
    return HISTORY[from_sq][to_sq], None


def ordered_moves(board, moves_list, depth):
    scored = []
    append = scored.append
    see_cache = {}
    for move in moves_list:
        piece = (move >> 12) & 0x7
        captured_piece = (move >> 16) & 0x7
        flag = (move >> 22) & 0x7
        s, see_value = move_score(move, depth, board, piece, captured_piece, flag)
        if see_value is not None:
            see_cache[move] = see_value
        append((s, move))
    scored.sort(key=lambda t: t[0], reverse=True)
    return [m for _, m in scored], see_cache


def _ci(color):
    return WHITE if color == "white" else BLACK


def eval_cached(board):
    key = board.hash
    if key in EVAL_CACHE:
        return EVAL_CACHE[key]
    v = bewerte_material(board)
    EVAL_CACHE[key] = v
    return v


def make_null_move(board):
    prev_hash = board.hash
    prev_count = board.position_history.get(prev_hash, 0)
    old_ep = board.ep_square
    move_stack.append((board.halfmove_clock, prev_hash, prev_count, old_ep))

    board.ep_square = None
    board.halfmove_clock += 1
    h = board.hash ^ ZOBRIST_TURN
    if old_ep is not None:
        h ^= ZOBRIST_EP_FILE[old_ep & 7]
    board.hash = h
    board.position_history[h] = board.position_history.get(h, 0) + 1
    board.side_to_move = opposite(board.side_to_move)


def unmake_null_move(board):
    half, prev_hash, prev_count, old_ep = move_stack.pop()

    post_hash = board.hash
    current_count = board.position_history.get(post_hash, 0)
    if current_count > 1:
        board.position_history[post_hash] = current_count - 1
    else:
        board.position_history.pop(post_hash, None)
    board.position_history[prev_hash] = prev_count

    board.hash = prev_hash
    board.halfmove_clock = half
    board.ep_square = old_ep
    board.side_to_move = opposite(board.side_to_move)

def negamax(board, depth, color, alpha, beta, is_null_move=False, ply=0, cut_node=False):
    alpha_orig = alpha
    global NODE_COUNT
    NODE_COUNT += 1

    if board.halfmove_clock >= 100:
        return 0
    if board.position_history.get(board.hash, 0) >= 3:
        return 0
    if ply >= 127:
        return eval_cached(board) if color == "black" else -eval_cached(board)

    zobrist_hash = board.hash
    tt_move = None
    idx = tt_probe(zobrist_hash)
    if idx != -1:
        d = TT_DEPTH[idx]
        tt_move = TT_MOVE[idx] if TT_MOVE[idx] != -1 else None
        if d >= depth:
            v = score_from_tt(TT_SCORE[idx], ply)
            bound = TT_BOUND[idx]
            if bound == 0:
                return v
            if bound == 1:
                alpha = max(alpha, v)
            if bound == 2:
                beta = min(beta, v)
            if alpha >= beta:
                return v

    next_color = "white" if color == "black" else "black"
    own_idx = _ci(color)
    piece_count_nm = popcount(board.all_occupancy)
    has_major_piece = popcount(board.bitboards[own_idx][ROOK] | board.bitboards[own_idx][QUEEN]) > 0
    in_check_now = is_in_check(board, own_idx)

    corr_idx = None
    if in_check_now:
        static_eval = STATIC_EVAL[ply - 1] if ply > 0 else 0.0
    else:
        raw_eval = eval_cached(board) if color == "black" else -eval_cached(board)
        corr_idx = compute_pawn_hash(board) & CORR_HIST_MASK
        static_eval = raw_eval + CORRECTION_HISTORY[own_idx][corr_idx]
    STATIC_EVAL[ply] = static_eval
    improving = (not in_check_now) and ply >= 2 and static_eval > STATIC_EVAL[ply - 2]

    if (
            depth <= 6
            and not in_check_now
            and not is_null_move
            and abs(alpha) < MATE_THRESHOLD
            and abs(beta) < MATE_THRESHOLD
    ):
        rfp_margin = (0.9 if improving else 1.3) * depth
        if static_eval - rfp_margin >= beta:
            return static_eval

    if depth >= 3 and not in_check_now and not is_null_move and piece_count_nm > 6 and has_major_piece:
        make_null_move(board)
        null_score = -negamax(board, depth - 3, next_color, -beta, -beta + 1,
                              is_null_move=True, ply=ply + 1, cut_node=True)
        unmake_null_move(board)
        if null_score >= beta:
            return beta

    if time.time() - SEARCH_START > SEARCH_LIMIT:
        return eval_cached(board) if color == "black" else -eval_cached(board)
    if debug:
        print(f"{'  ' * depth}Tiefe {depth} | {color} | alpha={alpha} beta={beta}", file=sys.stderr)

    if tt_move is None and depth >= 4 and not in_check_now:
        depth -= 1

    if depth == 0:
        return quiescence(board, alpha, beta, color, ply)

    moves_list, see_cache = ordered_moves(board, generate_legal_moves(board), depth)

    if not moves_list:
        if in_check_now:
            return -(MATE_VALUE - ply)
        return 0

    if tt_move is not None and tt_move in moves_list:
        moves_list.remove(tt_move)
        moves_list.insert(0, tt_move)

    extension = 0
    if (
            depth >= 6
            and tt_move is not None
            and idx != -1
            and TT_DEPTH[idx] >= depth - 3
            and ply > 0
            and abs(beta) < MATE_THRESHOLD
    ):
        singular_beta = beta - (0.5 + 0.1 * depth)
        reduced_depth = (depth - 1) // 2
        fail_high_count = 0
        best_alt_score = -9999999
        for alt_move in moves_list:
            if alt_move == tt_move:
                continue
            make_move(board, alt_move)
            alt_score = -negamax(board, reduced_depth, next_color, -singular_beta - 1, -singular_beta,
                                 ply=ply + 1, cut_node=True)
            unmake_move(board)
            if alt_score > best_alt_score:
                best_alt_score = alt_score
            if alt_score >= singular_beta:
                fail_high_count += 1
                if fail_high_count >= 3:
                    return beta
        if fail_high_count == 0:
            extension = 2 if (singular_beta - best_alt_score) > 1.5 else 1

    best_score = -9999999
    best_move_here = None
    move_index = 0

    futility_stand_pat = None
    skip_futility = False
    if depth == 1 and not in_check_now:
        skip_futility = _side_has_hanging_piece(board, own_idx)
        if not skip_futility:
            futility_stand_pat = static_eval

    for move in moves_list:
        captured_piece = (move >> 16) & 0x7
        flag = (move >> 22) & 0x7
        is_capture = captured_piece != NONE_PIECE or flag == EN_PASSANT
        from_sq_pv = move & 0x3F
        to_sq_pv = (move >> 6) & 0x3F

        if (
                move_index > 0
                and depth <= 8
                and not in_check_now
                and not is_capture
                and move != tt_move
        ):
            lmp_limit = (4 + depth * depth) if improving else (2 + depth * depth // 2)
            if move_index >= lmp_limit:
                move_index += 1
                continue
            if depth <= 5 and HISTORY[from_sq_pv][to_sq_pv] < -depth * 400:
                move_index += 1
                continue

        if (
                move_index > 0
                and depth <= 6
                and is_capture
                and move != tt_move
                and not in_check_now
        ):
            see_margin = -0.9 * depth * depth
            if see_cache.get(move, 0) < see_margin:
                move_index += 1
                continue

        if move_index > 0 and depth == 1 and not in_check_now and not is_capture and not skip_futility:
            if futility_stand_pat + 3 < alpha:
                move_index += 1
                continue
        make_move(board, move)
        new_depth = depth - 1
        gives_check_now = is_in_check(board, board.side_to_move)
        if gives_check_now and ply < 64:
            new_depth += 1
        if move_index == 0 and extension > 0:
            new_depth += extension

        if move_index == 0:
            score_result = -negamax(board, new_depth, next_color, -beta, -alpha, ply=ply + 1, cut_node=False)
        else:
            killer0 = KILLER[depth][0]
            killer1 = KILLER[depth][1]
            from_sq = move & 0x3F
            to_sq = (move >> 6) & 0x3F
            is_killer = (
                    (killer0 is not None and from_sq == (killer0 & 0x3F) and to_sq == ((killer0 >> 6) & 0x3F))
                    or (killer1 is not None and from_sq == (killer1 & 0x3F) and to_sq == ((killer1 >> 6) & 0x3F))
            )
            can_reduce = (
                    move_index >= 6
                    and new_depth >= 3
                    and not is_capture
                    and not in_check_now
                    and not is_killer
            )

            if can_reduce and gives_check_now:
                can_reduce = False

            if can_reduce:
                reduction = 1 + move_index // 6
                if cut_node:
                    reduction += 1
                reduced_depth = max(1, new_depth - reduction)
            else:
                reduced_depth = new_depth

            score_result = -negamax(board, reduced_depth, next_color, -alpha - 1, -alpha,
                                    ply=ply + 1, cut_node=True)
            if score_result > alpha:
                score_result = -negamax(board, new_depth, next_color, -beta, -alpha,
                                        ply=ply + 1, cut_node=False)

        unmake_move(board)

        if score_result > best_score:
            best_score = score_result
            best_move_here = move

        if score_result > alpha:
            alpha = score_result

        if alpha >= beta:
            if not is_capture:
                killer0 = KILLER[depth][0]
                from_sq = move & 0x3F
                to_sq = (move >> 6) & 0x3F
                if killer0 is None or (killer0 & 0x3F) != from_sq or ((killer0 >> 6) & 0x3F) != to_sq:
                    KILLER[depth][1] = KILLER[depth][0]
                    KILLER[depth][0] = move
                HISTORY[from_sq][to_sq] += depth * depth
            break

        move_index += 1

    if not in_check_now and abs(best_score) < MATE_THRESHOLD:
        error = best_score - static_eval
        updated = CORRECTION_HISTORY[own_idx][corr_idx] + 0.05 * (error - CORRECTION_HISTORY[own_idx][corr_idx])
        CORRECTION_HISTORY[own_idx][corr_idx] = max(-2.0, min(2.0, updated))

    if best_score <= alpha_orig:
        tt_store(zobrist_hash, depth, score_to_tt(best_score, ply), 2, TT_GENERATION, best_move_here)
    elif best_score >= beta:
        tt_store(zobrist_hash, depth, score_to_tt(best_score, ply), 1, TT_GENERATION, best_move_here)
    else:
        tt_store(zobrist_hash, depth, score_to_tt(best_score, ply), 0, TT_GENERATION, best_move_here)

    return best_score

def quiescence(board, alpha, beta, color, ply, depth=10):
    global NODE_COUNT
    NODE_COUNT += 1

    if depth <= 0 or time.time() - SEARCH_START > SEARCH_LIMIT:
        eval_value = eval_cached(board)
        return eval_value if color == "black" else -eval_value

    own_idx = _ci(color)
    in_check_now = is_in_check(board, own_idx)
    next_color = "white" if color == "black" else "black"

    if in_check_now:
        moves_list, _ = ordered_moves(board, generate_legal_moves(board), depth)
        if not moves_list:
            return -(MATE_VALUE - ply)

        best = -9999999
        for move in moves_list:
            make_move(board, move)
            score = -quiescence(board, -beta, -alpha, next_color, ply + 1, depth - 1)
            unmake_move(board)

            if score > best:
                best = score
            if score > alpha:
                alpha = score
            if alpha >= beta:
                break

        return best

    stand_pat = eval_cached(board)
    if color != "black":
        stand_pat = -stand_pat

    if stand_pat >= beta:
        return beta
    if stand_pat > alpha:
        alpha = stand_pat

    candidate_moves = generate_legal_captures(board)
    capture_moves = []
    append = capture_moves.append
    for move in candidate_moves:
        captured_piece = (move >> 16) & 0x7
        flag = (move >> 22) & 0x7
        see_value = SEE(board, move) if captured_piece != NONE_PIECE or flag == EN_PASSANT else 800000
        append((see_value, move))
    capture_moves.sort(key=lambda t: t[0], reverse=True)

    for see_value, move in capture_moves:
        if see_value < 0:
            continue
        captured_piece = (move >> 16) & 0x7
        if (
                captured_piece != NONE_PIECE
                and abs(alpha) < MATE_THRESHOLD
                and stand_pat + piece_value[captured_piece] + 0.3 <= alpha
        ):
            continue
        make_move(board, move)
        score = -quiescence(board, -beta, -alpha, next_color, ply + 1, depth - 1)
        unmake_move(board)

        if score >= beta:
            return beta
        if score > alpha:
            alpha = score

    return alpha

def choose_move(board, color, depth=5, alpha=-1000000, beta=1000000):
    global SEARCH_ABORTED, NODE_COUNT
    moves_list, _ = ordered_moves(board, generate_legal_moves(board), depth)
    if not moves_list:
        return None, 0, 0.0, 1.0

    best_move = None
    best_score = -9999999
    best_move_nodes = 0
    move_index = 0
    moves_searched = 0
    next_color = "white" if color == "black" else "black"
    total_nodes_start = NODE_COUNT

    for move in moves_list:
        nodes_before = NODE_COUNT
        make_move(board, move)

        if move_index == 0:
            evaluation = -negamax(board, depth - 1, next_color, -beta, -alpha, ply=1, cut_node=False)
        else:
            evaluation = -negamax(board, depth - 1, next_color, -alpha - 1, -alpha, ply=1, cut_node=True)
            if evaluation > alpha:
                evaluation = -negamax(board, depth - 1, next_color, -beta, -alpha, ply=1, cut_node=False)

        unmake_move(board)
        nodes_spent = NODE_COUNT - nodes_before
        moves_searched += 1

        if evaluation > best_score:
            best_score = evaluation
            best_move = move
            best_move_nodes = nodes_spent

        if time.time() - SEARCH_START > SEARCH_LIMIT:
            SEARCH_ABORTED = True
            break

        if evaluation > alpha:
            alpha = evaluation
            if alpha >= beta:
                break

        move_index += 1

    total_nodes = NODE_COUNT - total_nodes_start
    node_fraction = (best_move_nodes / total_nodes) if total_nodes > 0 else 1.0
    coverage = moves_searched / len(moves_list)
    return best_move, best_score, node_fraction, coverage

def choose_move_iterative(board, color, max_depth=99, time_limit=thinking_time, info_callback=None):
    global SEARCH_START, SEARCH_LIMIT, TT_GENERATION, NODE_COUNT, SEARCH_ABORTED
    profiler = None
    if performance_debug or debug:
        profiler = cProfile.Profile()
        profiler.enable()
    move_stack.clear()
    for i in range(64):
        for j in range(64):
            HISTORY[i][j] //= 2
    TT_GENERATION += 1
    SEARCH_ABORTED = False
    SEARCH_START = time.time()
    SEARCH_LIMIT = time_limit
    soft_limit = time_limit * 0.6

    best_move_overall = None
    prev_score = None
    prev_move = None
    stability_count = 0

    for depth in range(1, max_depth + 1):
        if time.time() - SEARCH_START > SEARCH_LIMIT:
            break
        if depth > 1 and time.time() - SEARCH_START > soft_limit:
            break

        if prev_score is None:
            window_alpha = -1000000
            window_beta = 1000000
        else:
            window_alpha = prev_score - 0.5
            window_beta = prev_score + 0.5

        move, score, node_fraction, coverage = choose_move(board, color, depth, window_alpha, window_beta)

        if move is not None and (score <= window_alpha or score >= window_beta):
            move, score, node_fraction, coverage = choose_move(board, color, depth, -1000000, 1000000)
        if debug or depth_debug:
            print(f"Tiefe {depth} abgeschlossen | Bester Zug: {move} | Score: {score}", file=sys.stderr)

        if move is not None and (not SEARCH_ABORTED or coverage >= 0.5):
            if prev_move is not None and move == prev_move:
                stability_count += 1
            else:
                stability_count = 0
            eval_swing = abs(score - prev_score) if prev_score is not None else 0.0

            stability_factor = max(0.5, 1.0 - stability_count * 0.1)
            eval_factor = 1.0 + min(1.0, eval_swing * 0.5)
            node_factor = max(0.5, 1.5 - node_fraction)
            soft_limit = time_limit * 0.6 * stability_factor * eval_factor * node_factor

            best_move_overall = move
            prev_score = score
            prev_move = move
        if info_callback is not None:
            elapsed_ms = int((time.time() - SEARCH_START) * 1000)
            info_callback(depth, score, NODE_COUNT, elapsed_ms, move)

        if SEARCH_ABORTED or move is None:
            break

        elapsed = time.time() - SEARCH_START
        if debug or depth_debug:
            print(f"Tiefe {depth} | Nodes: {NODE_COUNT} | Zeit: {elapsed:.2f}s", file=sys.stderr)
        NODE_COUNT = 0

        if time.time() - SEARCH_START > SEARCH_LIMIT:
            break
        if time.time() - SEARCH_START > soft_limit:
            break

    if profiler is not None:
        profiler.disable()
        if performance_debug or debug:
            stats = pstats.Stats(profiler).sort_stats("tottime")
            stats.print_stats(100)

    if best_move_overall is not None:
        captured_piece = (best_move_overall >> 16) & 0x7
        move_flag = (best_move_overall >> 22) & 0x7
        is_capture = captured_piece != NONE_PIECE or move_flag == EN_PASSANT
        if is_capture and prev_score is not None and prev_score < 1.0:
            see_value = SEE(board, best_move_overall)
            if see_value is not None and see_value <= -2.0:
                remaining = SEARCH_LIMIT - (time.time() - SEARCH_START)
                extra_time = min(3.0, max(0.5, remaining))
                SEARCH_LIMIT = (time.time() - SEARCH_START) + extra_time
                check_move, check_score, _, check_coverage = choose_move(board, color, depth + 1, -1000000, 1000000)
                if (check_move is not None and check_coverage >= 0.5
                        and check_move != best_move_overall and check_score > prev_score):
                    if debug or depth_debug:
                        print(f"Root-Sicherheitscheck: {best_move_overall} (SEE {see_value}) verworfen, "
                              f"stattdessen {check_move} (Score {check_score})", file=sys.stderr)
                    best_move_overall = check_move

    return best_move_overall

def tt_probe(zobrist_hash):
    idx = zobrist_hash & TT_MASK
    if TT_DEPTH[idx] != -1 and TT_HASH[idx] == zobrist_hash:
        return idx
    return -1


def tt_store(zobrist_hash, depth, score, bound, generation, best_move):
    idx = zobrist_hash & TT_MASK
    if TT_DEPTH[idx] == -1 or TT_GEN[idx] != generation or depth >= TT_DEPTH[idx]:
        TT_HASH[idx] = zobrist_hash
        TT_DEPTH[idx] = depth
        TT_SCORE[idx] = score
        TT_BOUND[idx] = bound
        TT_GEN[idx] = generation
        TT_MOVE[idx] = best_move if best_move is not None else -1


def tt_clear():
    for i in range(TT_SIZE):
        TT_DEPTH[i] = -1
    EVAL_CACHE.clear()

def score_to_tt(score, ply):
    if score >= MATE_THRESHOLD:
        return score + ply
    if score <= -MATE_THRESHOLD:
        return score - ply
    return score

def score_from_tt(score, ply):
    if score >= MATE_THRESHOLD:
        return score - ply
    if score <= -MATE_THRESHOLD:
        return score + ply
    return score


def _side_has_hanging_piece(board, side):
    occ = board.all_occupancy
    diag = (board.bitboards[WHITE][BISHOP] | board.bitboards[WHITE][QUEEN] |
            board.bitboards[BLACK][BISHOP] | board.bitboards[BLACK][QUEEN])
    straight = (board.bitboards[WHITE][ROOK] | board.bitboards[WHITE][QUEEN] |
                board.bitboards[BLACK][ROOK] | board.bitboards[BLACK][QUEEN])
    opp = opposite(side)
    for pt in (PAWN, KNIGHT, BISHOP, ROOK, QUEEN):
        bb = board.bitboards[side][pt]
        while bb:
            s = (bb & -bb).bit_length() - 1
            bb &= bb - 1
            attackers = _attackers_to(board, s, occ, diag, straight) & board.occupancy[opp]
            if not attackers:
                continue
            lva_sq, lva_pt = _least_valuable_attacker(board, attackers, opp)
            if lva_pt is not None and piece_value[lva_pt] <= piece_value[pt]:
                return True
            defenders = _attackers_to(board, s, occ, diag, straight) & board.occupancy[side]
            if defenders == 0:
                return True
    return False