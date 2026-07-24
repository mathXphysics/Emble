from board import (WHITE, BLACK, PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING,
                    NONE_PIECE, CR_WHITE_SHORT, CR_WHITE_LONG,
                    CR_BLACK_SHORT, CR_BLACK_LONG, VALUE_TABLE_MG, VALUE_TABLE_EG, PHASE_WEIGHT)
from attacks import KNIGHT_ATTACKS, KING_ATTACKS, PAWN_ATTACKS, pawn_pushes_single, pawn_pushes_double
import magic
from magic import (BISHOP_MASKS, BISHOP_MAGICS, BISHOP_SHIFTS, BISHOP_TABLES,
                    ROOK_MASKS, ROOK_MAGICS, ROOK_SHIFTS, ROOK_TABLES)
from board import FULL
import zobrist
from zobrist import ZOBRIST_PIECE, ZOBRIST_CASTLING, ZOBRIST_EP_FILE, ZOBRIST_TURN


NORMAL, DOUBLE_PAWN, EN_PASSANT, CASTLE_KING, CASTLE_QUEEN = range(5)


def encode_move(from_sq, to_sq, piece, color, captured_piece=NONE_PIECE,
                 captured_square=None, promotion=NONE_PIECE, flag=NORMAL):
    if captured_square is None:
        captured_square = to_sq
    return (from_sq | (to_sq << 6) | (piece << 12) | (color << 15)
            | (captured_piece << 16) | (promotion << 19) | (flag << 22)
            | (captured_square << 25))


def mv_from(m):     return m & 0x3F
def mv_to(m):        return (m >> 6) & 0x3F
def mv_piece(m):     return (m >> 12) & 0x7
def mv_color(m):     return (m >> 15) & 0x1
def mv_captured(m):  return (m >> 16) & 0x7
def mv_promotion(m): return (m >> 19) & 0x7
def mv_flag(m):      return (m >> 22) & 0x7
def mv_capsq(m):     return (m >> 25) & 0x3F


def opposite(color):
    return color ^ 1


def attacked_squares(board, by_color):
    occ = board.all_occupancy
    attacks = 0
    bb = board.bitboards[by_color][KNIGHT]
    while bb:
        s = (bb & -bb).bit_length() - 1
        attacks |= KNIGHT_ATTACKS[s]
        bb &= bb - 1
    king_bb = board.bitboards[by_color][KING]
    if king_bb:
        attacks |= KING_ATTACKS[(king_bb & -king_bb).bit_length() - 1]
    bb = board.bitboards[by_color][PAWN]
    pawn_table = PAWN_ATTACKS[by_color]
    while bb:
        s = (bb & -bb).bit_length() - 1
        attacks |= pawn_table[s]
        bb &= bb - 1
    bb = board.bitboards[by_color][BISHOP] | board.bitboards[by_color][QUEEN]
    while bb:
        s = (bb & -bb).bit_length() - 1
        attacks |= magic.get_bishop_attacks(s, occ)
        bb &= bb - 1
    bb = board.bitboards[by_color][ROOK] | board.bitboards[by_color][QUEEN]
    while bb:
        s = (bb & -bb).bit_length() - 1
        attacks |= magic.get_rook_attacks(s, occ)
        bb &= bb - 1
    return attacks


def is_square_attacked(board, square, by_color):
    occ = board.all_occupancy
    if PAWN_ATTACKS[opposite(by_color)][square] & board.bitboards[by_color][PAWN]:
        return True
    if KNIGHT_ATTACKS[square] & board.bitboards[by_color][KNIGHT]:
        return True
    if KING_ATTACKS[square] & board.bitboards[by_color][KING]:
        return True
    diag = board.bitboards[by_color][BISHOP] | board.bitboards[by_color][QUEEN]
    if diag:
        masked = occ & BISHOP_MASKS[square]
        idx = ((masked * BISHOP_MAGICS[square]) & FULL) >> BISHOP_SHIFTS[square]
        if BISHOP_TABLES[square][idx] & diag:
            return True
    straight = board.bitboards[by_color][ROOK] | board.bitboards[by_color][QUEEN]
    if straight:
        masked = occ & ROOK_MASKS[square]
        idx = ((masked * ROOK_MAGICS[square]) & FULL) >> ROOK_SHIFTS[square]
        if ROOK_TABLES[square][idx] & straight:
            return True
    return False


def is_in_check(board, color):
    king_bb = board.bitboards[color][KING]
    if king_bb == 0:
        return False
    square = (king_bb & -king_bb).bit_length() - 1
    by_color = opposite(color)
    occ = board.all_occupancy

    if PAWN_ATTACKS[color][square] & board.bitboards[by_color][PAWN]:
        return True
    if KNIGHT_ATTACKS[square] & board.bitboards[by_color][KNIGHT]:
        return True
    if KING_ATTACKS[square] & board.bitboards[by_color][KING]:
        return True
    diag = board.bitboards[by_color][BISHOP] | board.bitboards[by_color][QUEEN]
    if diag:
        masked = occ & BISHOP_MASKS[square]
        idx = ((masked * BISHOP_MAGICS[square]) & FULL) >> BISHOP_SHIFTS[square]
        if BISHOP_TABLES[square][idx] & diag:
            return True
    straight = board.bitboards[by_color][ROOK] | board.bitboards[by_color][QUEEN]
    if straight:
        masked = occ & ROOK_MASKS[square]
        idx = ((masked * ROOK_MAGICS[square]) & FULL) >> ROOK_SHIFTS[square]
        if ROOK_TABLES[square][idx] & straight:
            return True
    return False

def generate_pseudo_legal_moves(board):
    moves = []
    append = moves.append
    color = board.side_to_move
    opp = opposite(color)
    occ_own = board.occupancy[color]
    occ_opp = board.occupancy[opp]
    all_occ = board.all_occupancy
    not_own = ~occ_own
    promo_rank = 7 if color == WHITE else 0
    piece_at_sq = board.piece_at_sq
    color_shifted = color << 15

    bb = board.bitboards[color][PAWN]
    pawn_atk_table = PAWN_ATTACKS[color]
    ep_sq = board.ep_square
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1

        single = pawn_pushes_single(s, color, all_occ)
        if single:
            t = single.bit_length() - 1
            base = s | (t << 6) | (PAWN << 12) | color_shifted | (NONE_PIECE << 16)
            if (t >> 3) == promo_rank:
                append(base | (QUEEN << 19) | (t << 25))
                append(base | (ROOK << 19) | (t << 25))
                append(base | (BISHOP << 19) | (t << 25))
                append(base | (KNIGHT << 19) | (t << 25))
            else:
                append(base | (NONE_PIECE << 19) | (t << 25))
            double = pawn_pushes_double(s, color, all_occ)
            if double:
                t2 = (double & -double).bit_length() - 1
                append(s | (t2 << 6) | (PAWN << 12) | color_shifted | (NONE_PIECE << 16)
                       | (NONE_PIECE << 19) | (DOUBLE_PAWN << 22) | (t2 << 25))

        cap_bb = pawn_atk_table[s] & occ_opp
        while cap_bb:
            t = (cap_bb & -cap_bb).bit_length() - 1
            cap_bb &= cap_bb - 1
            captured_piece = piece_at_sq[t]
            base = s | (t << 6) | (PAWN << 12) | color_shifted | (captured_piece << 16) | (t << 25)
            if (t >> 3) == promo_rank:
                append(base | (QUEEN << 19))
                append(base | (ROOK << 19))
                append(base | (BISHOP << 19))
                append(base | (KNIGHT << 19))
            else:
                append(base | (NONE_PIECE << 19))

        if ep_sq is not None and (pawn_atk_table[s] >> ep_sq) & 1:
            cap_sq = ep_sq - 8 if color == WHITE else ep_sq + 8
            append(s | (ep_sq << 6) | (PAWN << 12) | color_shifted | (PAWN << 16)
                   | (NONE_PIECE << 19) | (EN_PASSANT << 22) | (cap_sq << 25))

    bb = board.bitboards[color][KNIGHT]
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        t_bb = KNIGHT_ATTACKS[s] & not_own
        while t_bb:
            t = (t_bb & -t_bb).bit_length() - 1
            t_bb &= t_bb - 1
            captured_piece = piece_at_sq[t] if (occ_opp >> t) & 1 else NONE_PIECE
            append(s | (t << 6) | (KNIGHT << 12) | color_shifted | (captured_piece << 16)
                   | (NONE_PIECE << 19) | (t << 25))

    bb = board.bitboards[color][BISHOP]
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        masked = all_occ & BISHOP_MASKS[s]
        idx = ((masked * BISHOP_MAGICS[s]) & FULL) >> BISHOP_SHIFTS[s]
        t_bb = BISHOP_TABLES[s][idx] & not_own
        while t_bb:
            t = (t_bb & -t_bb).bit_length() - 1
            t_bb &= t_bb - 1
            captured_piece = piece_at_sq[t] if (occ_opp >> t) & 1 else NONE_PIECE
            append(s | (t << 6) | (BISHOP << 12) | color_shifted | (captured_piece << 16)
                   | (NONE_PIECE << 19) | (t << 25))

    bb = board.bitboards[color][ROOK]
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        masked = all_occ & ROOK_MASKS[s]
        idx = ((masked * ROOK_MAGICS[s]) & FULL) >> ROOK_SHIFTS[s]
        t_bb = ROOK_TABLES[s][idx] & not_own
        while t_bb:
            t = (t_bb & -t_bb).bit_length() - 1
            t_bb &= t_bb - 1
            captured_piece = piece_at_sq[t] if (occ_opp >> t) & 1 else NONE_PIECE
            append(s | (t << 6) | (ROOK << 12) | color_shifted | (captured_piece << 16)
                   | (NONE_PIECE << 19) | (t << 25))

    bb = board.bitboards[color][QUEEN]
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        occ_b = all_occ & BISHOP_MASKS[s]
        idx_b = ((occ_b * BISHOP_MAGICS[s]) & FULL) >> BISHOP_SHIFTS[s]
        occ_r = all_occ & ROOK_MASKS[s]
        idx_r = ((occ_r * ROOK_MAGICS[s]) & FULL) >> ROOK_SHIFTS[s]
        t_bb = (BISHOP_TABLES[s][idx_b] | ROOK_TABLES[s][idx_r]) & not_own
        while t_bb:
            t = (t_bb & -t_bb).bit_length() - 1
            t_bb &= t_bb - 1
            captured_piece = piece_at_sq[t] if (occ_opp >> t) & 1 else NONE_PIECE
            append(s | (t << 6) | (QUEEN << 12) | color_shifted | (captured_piece << 16)
                   | (NONE_PIECE << 19) | (t << 25))

    king_bb = board.bitboards[color][KING]
    if king_bb:
        s = (king_bb & -king_bb).bit_length() - 1
        t_bb = KING_ATTACKS[s] & not_own
        while t_bb:
            t = (t_bb & -t_bb).bit_length() - 1
            t_bb &= t_bb - 1
            captured_piece = piece_at_sq[t] if (occ_opp >> t) & 1 else NONE_PIECE
            append(s | (t << 6) | (KING << 12) | color_shifted | (captured_piece << 16)
                   | (NONE_PIECE << 19) | (t << 25))

        cr = board.castling_rights
        if color == WHITE:
            if (cr & CR_WHITE_SHORT) and not ((all_occ >> 5) & 1) and not ((all_occ >> 6) & 1):
                if (not is_square_attacked(board, 4, BLACK)
                        and not is_square_attacked(board, 5, BLACK)
                        and not is_square_attacked(board, 6, BLACK)):
                    append(4 | (6 << 6) | (KING << 12) | color_shifted | (NONE_PIECE << 16)
                           | (NONE_PIECE << 19) | (CASTLE_KING << 22) | (6 << 25))
            if (cr & CR_WHITE_LONG) and not ((all_occ >> 1) & 1) and not ((all_occ >> 2) & 1) and not ((all_occ >> 3) & 1):
                if (not is_square_attacked(board, 4, BLACK)
                        and not is_square_attacked(board, 3, BLACK)
                        and not is_square_attacked(board, 2, BLACK)):
                    append(4 | (2 << 6) | (KING << 12) | color_shifted | (NONE_PIECE << 16)
                           | (NONE_PIECE << 19) | (CASTLE_QUEEN << 22) | (2 << 25))
        else:
            if (cr & CR_BLACK_SHORT) and not ((all_occ >> 61) & 1) and not ((all_occ >> 62) & 1):
                if (not is_square_attacked(board, 60, WHITE)
                        and not is_square_attacked(board, 61, WHITE)
                        and not is_square_attacked(board, 62, WHITE)):
                    append(60 | (62 << 6) | (KING << 12) | color_shifted | (NONE_PIECE << 16)
                           | (NONE_PIECE << 19) | (CASTLE_KING << 22) | (62 << 25))
            if (cr & CR_BLACK_LONG) and not ((all_occ >> 57) & 1) and not ((all_occ >> 58) & 1) and not ((all_occ >> 59) & 1):
                if (not is_square_attacked(board, 60, WHITE)
                        and not is_square_attacked(board, 59, WHITE)
                        and not is_square_attacked(board, 58, WHITE)):
                    append(60 | (58 << 6) | (KING << 12) | color_shifted | (NONE_PIECE << 16)
                           | (NONE_PIECE << 19) | (CASTLE_QUEEN << 22) | (58 << 25))

    return moves


def make_move(board, move):
    from_sq = move & 0x3F
    to_sq = (move >> 6) & 0x3F
    piece = (move >> 12) & 0x7
    color = (move >> 15) & 0x1
    captured_piece = (move >> 16) & 0x7
    promotion = (move >> 19) & 0x7
    flag = (move >> 22) & 0x7
    captured_square = (move >> 25) & 0x3F
    opp = color ^ 1

    old_cr = board.castling_rights
    old_ep = board.ep_square
    old_half = board.halfmove_clock
    old_hash = board.hash
    old_hash_count = board.position_history.get(old_hash, 0)
    # Undo als Tuple statt Dict -> keine Dict-Allokation, kein Hashing von Strings
    board.history.append((move, old_cr, old_ep, old_half, old_hash, old_hash_count))

    _remove_piece(board, color, piece, from_sq)

    has_capture = captured_piece != NONE_PIECE
    if has_capture:
        _remove_piece(board, opp, captured_piece, captured_square)

    final_piece = promotion if promotion != NONE_PIECE else piece
    _add_piece(board, color, final_piece, to_sq)

    if flag == CASTLE_KING:
        if color == WHITE:
            _remove_piece(board, color, ROOK, 7); _add_piece(board, color, ROOK, 5)
        else:
            _remove_piece(board, color, ROOK, 63); _add_piece(board, color, ROOK, 61)
    elif flag == CASTLE_QUEEN:
        if color == WHITE:
            _remove_piece(board, color, ROOK, 0); _add_piece(board, color, ROOK, 3)
        else:
            _remove_piece(board, color, ROOK, 56); _add_piece(board, color, ROOK, 59)

    new_cr = old_cr
    if piece == KING:
        if color == WHITE:
            new_cr &= ~(CR_WHITE_SHORT | CR_WHITE_LONG)
        else:
            new_cr &= ~(CR_BLACK_SHORT | CR_BLACK_LONG)
    elif piece == ROOK:
        if from_sq == 0: new_cr &= ~CR_WHITE_LONG
        elif from_sq == 7: new_cr &= ~CR_WHITE_SHORT
        elif from_sq == 56: new_cr &= ~CR_BLACK_LONG
        elif from_sq == 63: new_cr &= ~CR_BLACK_SHORT

    if captured_piece == ROOK:
        if captured_square == 0: new_cr &= ~CR_WHITE_LONG
        elif captured_square == 7: new_cr &= ~CR_WHITE_SHORT
        elif captured_square == 56: new_cr &= ~CR_BLACK_LONG
        elif captured_square == 63: new_cr &= ~CR_BLACK_SHORT

    board.castling_rights = new_cr

    if flag == DOUBLE_PAWN:
        board.ep_square = (from_sq + to_sq) // 2
    else:
        board.ep_square = None

    if piece == PAWN or has_capture:
        board.halfmove_clock = 0
    else:
        board.halfmove_clock += 1

    h = old_hash
    h ^= ZOBRIST_PIECE[color][piece][from_sq]
    if has_capture:
        h ^= ZOBRIST_PIECE[opp][captured_piece][captured_square]
    h ^= ZOBRIST_PIECE[color][final_piece][to_sq]

    if flag == CASTLE_KING:
        if color == WHITE:
            h ^= ZOBRIST_PIECE[color][ROOK][7]
            h ^= ZOBRIST_PIECE[color][ROOK][5]
        else:
            h ^= ZOBRIST_PIECE[color][ROOK][63]
            h ^= ZOBRIST_PIECE[color][ROOK][61]
    elif flag == CASTLE_QUEEN:
        if color == WHITE:
            h ^= ZOBRIST_PIECE[color][ROOK][0]
            h ^= ZOBRIST_PIECE[color][ROOK][3]
        else:
            h ^= ZOBRIST_PIECE[color][ROOK][56]
            h ^= ZOBRIST_PIECE[color][ROOK][59]

    changed_cr = old_cr & ~new_cr
    if changed_cr & CR_WHITE_SHORT: h ^= ZOBRIST_CASTLING[0]
    if changed_cr & CR_WHITE_LONG:  h ^= ZOBRIST_CASTLING[1]
    if changed_cr & CR_BLACK_SHORT: h ^= ZOBRIST_CASTLING[2]
    if changed_cr & CR_BLACK_LONG:  h ^= ZOBRIST_CASTLING[3]

    if old_ep is not None:
        h ^= ZOBRIST_EP_FILE[old_ep & 7]
    if board.ep_square is not None:
        h ^= ZOBRIST_EP_FILE[board.ep_square & 7]

    board.hash = h ^ ZOBRIST_TURN
    board.position_history[board.hash] = board.position_history.get(board.hash, 0) + 1
    board.side_to_move = opp


def unmake_move(board):
    move, old_cr, old_ep, old_half, old_hash, old_hash_count = board.history.pop()
    from_sq = move & 0x3F
    to_sq = (move >> 6) & 0x3F
    piece = (move >> 12) & 0x7
    color = (move >> 15) & 0x1
    captured_piece = (move >> 16) & 0x7
    promotion = (move >> 19) & 0x7
    flag = (move >> 22) & 0x7
    captured_square = (move >> 25) & 0x3F
    opp = color ^ 1

    board.side_to_move = color
    board.castling_rights = old_cr
    board.ep_square = old_ep
    board.halfmove_clock = old_half

    post_hash = board.hash
    current_count = board.position_history.get(post_hash, 0)
    if current_count > 1:
        board.position_history[post_hash] = current_count - 1
    else:
        board.position_history.pop(post_hash, None)
    board.position_history[old_hash] = old_hash_count
    board.hash = old_hash

    final_piece = promotion if promotion != NONE_PIECE else piece
    _remove_piece(board, color, final_piece, to_sq)
    _add_piece(board, color, piece, from_sq)

    if captured_piece != NONE_PIECE:
        _add_piece(board, opp, captured_piece, captured_square)

    if flag == CASTLE_KING:
        if color == WHITE:
            _remove_piece(board, color, ROOK, 5); _add_piece(board, color, ROOK, 7)
        else:
            _remove_piece(board, color, ROOK, 61); _add_piece(board, color, ROOK, 63)
    elif flag == CASTLE_QUEEN:
        if color == WHITE:
            _remove_piece(board, color, ROOK, 3); _add_piece(board, color, ROOK, 0)
        else:
            _remove_piece(board, color, ROOK, 59); _add_piece(board, color, ROOK, 56)


def _compute_checkers(board, king_sq, color):
    opp = opposite(color)
    occ = board.all_occupancy
    checkers = 0
    checkers |= PAWN_ATTACKS[color][king_sq] & board.bitboards[opp][PAWN]
    checkers |= KNIGHT_ATTACKS[king_sq] & board.bitboards[opp][KNIGHT]
    diag = board.bitboards[opp][BISHOP] | board.bitboards[opp][QUEEN]
    straight = board.bitboards[opp][ROOK] | board.bitboards[opp][QUEEN]
    masked_b = occ & BISHOP_MASKS[king_sq]
    idx_b = ((masked_b * BISHOP_MAGICS[king_sq]) & FULL) >> BISHOP_SHIFTS[king_sq]
    checkers |= BISHOP_TABLES[king_sq][idx_b] & diag
    masked_r = occ & ROOK_MASKS[king_sq]
    idx_r = ((masked_r * ROOK_MAGICS[king_sq]) & FULL) >> ROOK_SHIFTS[king_sq]
    checkers |= ROOK_TABLES[king_sq][idx_r] & straight
    return checkers


def _bishop_attacks_inline(square, occ):
    masked = occ & BISHOP_MASKS[square]
    idx = ((masked * BISHOP_MAGICS[square]) & FULL) >> BISHOP_SHIFTS[square]
    return BISHOP_TABLES[square][idx]


def _rook_attacks_inline(square, occ):
    masked = occ & ROOK_MASKS[square]
    idx = ((masked * ROOK_MAGICS[square]) & FULL) >> ROOK_SHIFTS[square]
    return ROOK_TABLES[square][idx]


def _compute_pins(board, king_sq, color):
    opp = opposite(color)
    occ = board.all_occupancy
    own_occ = board.occupancy[color]
    occ_without_own = occ & ~own_occ

    diag_enemy = board.bitboards[opp][BISHOP] | board.bitboards[opp][QUEEN]
    straight_enemy = board.bitboards[opp][ROOK] | board.bitboards[opp][QUEEN]

    pinned = {}

    diag_candidates = _bishop_attacks_inline(king_sq, occ_without_own) & diag_enemy
    ray_king_b = _bishop_attacks_inline(king_sq, occ)
    while diag_candidates:
        p = (diag_candidates & -diag_candidates).bit_length() - 1
        diag_candidates &= diag_candidates - 1
        ray_p = _bishop_attacks_inline(p, occ)
        blockers = ray_king_b & ray_p & occ
        if blockers and (blockers & (blockers - 1)) == 0:
            b_sq = (blockers & -blockers).bit_length() - 1
            if (own_occ >> b_sq) & 1:
                occ_temp = occ & ~(1 << b_sq)
                allowed = (_bishop_attacks_inline(king_sq, occ_temp) & _bishop_attacks_inline(p, occ_temp)) | (1 << p)
                pinned[b_sq] = allowed

    straight_candidates = _rook_attacks_inline(king_sq, occ_without_own) & straight_enemy
    ray_king_r = _rook_attacks_inline(king_sq, occ)
    while straight_candidates:
        p = (straight_candidates & -straight_candidates).bit_length() - 1
        straight_candidates &= straight_candidates - 1
        ray_p = _rook_attacks_inline(p, occ)
        blockers = ray_king_r & ray_p & occ
        if blockers and (blockers & (blockers - 1)) == 0:
            b_sq = (blockers & -blockers).bit_length() - 1
            if (own_occ >> b_sq) & 1:
                occ_temp = occ & ~(1 << b_sq)
                allowed = (_rook_attacks_inline(king_sq, occ_temp) & _rook_attacks_inline(p, occ_temp)) | (1 << p)
                pinned[b_sq] = allowed

    return pinned


def _evasion_mask(board, king_sq, checker_sq):
    checker_piece = board.piece_at_sq[checker_sq]
    if checker_piece not in (BISHOP, ROOK, QUEEN):
        return 1 << checker_sq

    occ = board.all_occupancy
    bishop_ray_king = _bishop_attacks_inline(king_sq, occ)
    if (bishop_ray_king >> checker_sq) & 1:
        between = bishop_ray_king & _bishop_attacks_inline(checker_sq, occ)
    else:
        rook_ray_king = _rook_attacks_inline(king_sq, occ)
        between = rook_ray_king & _rook_attacks_inline(checker_sq, occ)

    return between | (1 << checker_sq)


def generate_legal_moves_fast(board):
    color = board.side_to_move
    king_bb = board.bitboards[color][KING]
    if king_bb == 0:
        return []
    king_sq = (king_bb & -king_bb).bit_length() - 1

    checkers = _compute_checkers(board, king_sq, color)
    num_checkers = 0 if checkers == 0 else (1 if (checkers & (checkers - 1)) == 0 else 2)

    pseudo = generate_pseudo_legal_moves(board)

    if num_checkers >= 2:
        legal = []
        for move in pseudo:
            if ((move >> 12) & 0x7) != KING:
                continue
            make_move(board, move)
            if not is_in_check(board, color):
                legal.append(move)
            unmake_move(board)
        return legal

    pinned = _compute_pins(board, king_sq, color)
    evasion_mask = None
    if num_checkers == 1:
        checker_sq = (checkers & -checkers).bit_length() - 1
        evasion_mask = _evasion_mask(board, king_sq, checker_sq)

    legal = []
    for move in pseudo:
        piece = (move >> 12) & 0x7
        flag = (move >> 22) & 0x7
        to_sq = (move >> 6) & 0x3F

        if piece == KING or flag == EN_PASSANT:
            make_move(board, move)
            if not is_in_check(board, color):
                legal.append(move)
            unmake_move(board)
            continue

        if evasion_mask is not None and not ((evasion_mask >> to_sq) & 1):
            continue

        from_sq = move & 0x3F
        if from_sq in pinned and not ((pinned[from_sq] >> to_sq) & 1):
            continue

        legal.append(move)

    return legal


generate_legal_moves = generate_legal_moves_fast


def generate_legal_moves_slow(board):
    color = board.side_to_move
    legal = []
    for move in generate_pseudo_legal_moves(board):
        make_move(board, move)
        if not is_in_check(board, color):
            legal.append(move)
        unmake_move(board)
    return legal

def _remove_piece(board, color, piece_type, square):
    b = 1 << square
    board.bitboards[color][piece_type] &= ~b
    board.occupancy[color] &= ~b
    board.all_occupancy &= ~b
    board.color_at[square] = -1
    board.piece_at_sq[square] = NONE_PIECE
    board.material_score_mg -= VALUE_TABLE_MG[color][piece_type][square]
    board.material_score_eg -= VALUE_TABLE_EG[color][piece_type][square]
    board.phase -= PHASE_WEIGHT[piece_type]


def _add_piece(board, color, piece_type, square):
    b = 1 << square
    board.bitboards[color][piece_type] |= b
    board.occupancy[color] |= b
    board.all_occupancy |= b
    board.color_at[square] = color
    board.piece_at_sq[square] = piece_type
    board.material_score_mg += VALUE_TABLE_MG[color][piece_type][square]
    board.material_score_eg += VALUE_TABLE_EG[color][piece_type][square]
    board.phase += PHASE_WEIGHT[piece_type]



def generate_legal_captures(board):
    color = board.side_to_move
    king_bb = board.bitboards[color][KING]
    if king_bb == 0:
        return []
    king_sq = (king_bb & -king_bb).bit_length() - 1

    checkers = _compute_checkers(board, king_sq, color)
    num_checkers = 0 if checkers == 0 else (1 if (checkers & (checkers - 1)) == 0 else 2)

    pseudo = generate_pseudo_legal_moves(board)
    candidates = [
        m for m in pseudo
        if ((m >> 16) & 0x7) != NONE_PIECE or ((m >> 22) & 0x7) == EN_PASSANT or ((m >> 19) & 0x7) == QUEEN
    ]

    if num_checkers >= 2:
        legal = []
        for move in candidates:
            if ((move >> 12) & 0x7) != KING:
                continue
            make_move(board, move)
            if not is_in_check(board, color):
                legal.append(move)
            unmake_move(board)
        return legal

    pinned = _compute_pins(board, king_sq, color)
    evasion_mask = None
    if num_checkers == 1:
        checker_sq = (checkers & -checkers).bit_length() - 1
        evasion_mask = _evasion_mask(board, king_sq, checker_sq)

    legal = []
    for move in candidates:
        piece = (move >> 12) & 0x7
        flag = (move >> 22) & 0x7
        to_sq = (move >> 6) & 0x3F

        if piece == KING or flag == EN_PASSANT:
            make_move(board, move)
            if not is_in_check(board, color):
                legal.append(move)
            unmake_move(board)
            continue

        if evasion_mask is not None and not ((evasion_mask >> to_sq) & 1):
            continue

        from_sq = move & 0x3F
        if from_sq in pinned and not ((pinned[from_sq] >> to_sq) & 1):
            continue

        legal.append(move)

    return legal