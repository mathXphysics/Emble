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

import math

import weights as W


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

CONT_HISTORY = [[0 for _ in range(64)] for _ in range(13)]
CONT_HIST_PREV = [[[[0 for _ in range(64)] for _ in range(7)] for _ in range(64)] for _ in range(7)]
CONT_HIST_PREV2 = [[[[0 for _ in range(64)] for _ in range(7)] for _ in range(64)] for _ in range(7)]

CAPTURE_HISTORY = [[[0 for _ in range(7)] for _ in range(64)] for _ in range(6)]

STATIC_EVAL = [0.0] * 128

CORR_HIST_BITS = 16
CORR_HIST_SIZE = 1 << CORR_HIST_BITS
CORR_HIST_MASK = CORR_HIST_SIZE - 1
CORRECTION_HISTORY = [[0.0] * CORR_HIST_SIZE for _ in range(2)]

_THREAT_CACHE_PHASE = -1
_THREAT_BY_MINOR = [0.0] * 7
_THREAT_BY_ROOK  = [0.0] * 7
_HANGING         = 0.0

NODE_COUNT = 0

EVAL_CACHE_BITS = 18
EVAL_CACHE_SIZE = 1 << EVAL_CACHE_BITS
EVAL_CACHE_MASK = EVAL_CACHE_SIZE - 1
EVAL_CACHE_HASH = [0] * EVAL_CACHE_SIZE
EVAL_CACHE_VALUE = [0.0] * EVAL_CACHE_SIZE
EVAL_CACHE_USED = bytearray(EVAL_CACHE_SIZE)

MATE_VALUE = 100000
MATE_THRESHOLD = MATE_VALUE - 1000

HISTORY_MAX = 500000

MVV_LVA_VALUE = {PAWN: 1, KNIGHT: 3, BISHOP: 3, ROOK: 5, QUEEN: 9, KING: 0}

thinking_time = 21
SEARCH_ABORTED = False


_LMR_TABLE = [[0] * 64 for _ in range(64)]
for _d in range(1, 64):
    for _m in range(1, 64):
        _LMR_TABLE[_d][_m] = max(0, int(0.35 + math.log(_d) * math.log(_m) * 0.55))



def _has_pawn(board, color, rank, file):
    return (board.bitboards[color][PAWN] >> sq(file, rank)) & 1



def bewerte_material(board):
    phase = board.phase
    if phase > 24: phase = 24
    if phase < 0:  phase = 0

    total_material = (board.material_score_mg * phase + board.material_score_eg * (24 - phase)) / 24

    non_pawn_material = (
        (board.bitboards[WHITE][KNIGHT] | board.bitboards[BLACK][KNIGHT]).bit_count() * 3.0 +
        (board.bitboards[WHITE][BISHOP] | board.bitboards[BLACK][BISHOP]).bit_count() * 3.0 +
        (board.bitboards[WHITE][ROOK]   | board.bitboards[BLACK][ROOK]).bit_count()   * 5.0 +
        (board.bitboards[WHITE][QUEEN]  | board.bitboards[BLACK][QUEEN]).bit_count()  * 9.0
    )
    if abs(total_material) > 14.0 + non_pawn_material / 64.0:
        return total_material

    material = 0.0

    passed_base        = W.w("PASSED_BASE", phase)
    passed_rank_sq      = W.w("PASSED_RANK_SQ", phase)
    passed_unstoppable  = W.w("PASSED_UNSTOPPABLE", phase)
    bishop_pair         = W.w("BISHOP_PAIR", phase)
    eg_king_edge        = W.w("EG_KING_EDGE_DIST", phase)
    eg_king_dist        = W.w("EG_KING_DIST", phase)
    doubled_pawn        = W.w("DOUBLED_PAWN", phase)
    isolated_pawn       = W.w("ISOLATED_PAWN", phase)
    undeveloped_minor   = W.w("UNDEVELOPED_MINOR", phase)
    king_shield_full    = W.w("KING_SHIELD_FULL_PT", phase)
    king_shield_half    = W.w("KING_SHIELD_HALF_PT", phase)
    king_shield_weight  = W.w("KING_SHIELD_WEIGHT", phase)
    king_center_file    = W.w("KING_CENTER_FILE", phase)
    king_file_open      = W.w("KING_FILE_OPEN", phase)
    king_file_semi_open = W.w("KING_FILE_SEMI_OPEN", phase)
    king_zone_major     = W.w("KING_ZONE_MAJOR_ATTACK", phase)
    rook_open_file      = W.w("ROOK_OPEN_FILE", phase)
    rook_semi_open_file = W.w("ROOK_SEMI_OPEN_FILE", phase)
    rook_on_7th         = W.w("ROOK_ON_7TH", phase)
    mobility_w          = W.w("MOBILITY", phase)

    white_pawn_bb = board.bitboards[WHITE][PAWN]
    black_pawn_bb = board.bitboards[BLACK][PAWN]
    white_king_bb = board.bitboards[WHITE][KING]
    black_king_bb = board.bitboards[BLACK][KING]
    white_king_pos = (white_king_bb & -white_king_bb).bit_length() - 1 if white_king_bb else sq(4, 0)
    black_king_pos = (black_king_bb & -black_king_bb).bit_length() - 1 if black_king_bb else sq(4, 7)
    wk_rank = white_king_pos >> 3
    wk_file = white_king_pos & 7
    bk_rank = black_king_pos >> 3
    bk_file = black_king_pos & 7

    occ   = board.all_occupancy
    w_occ = board.occupancy[WHITE]
    b_occ = board.occupancy[BLACK]

    fm = FILE_MASKS
    white_pawns_per_col = [
        (white_pawn_bb & fm[0]).bit_count(), (white_pawn_bb & fm[1]).bit_count(),
        (white_pawn_bb & fm[2]).bit_count(), (white_pawn_bb & fm[3]).bit_count(),
        (white_pawn_bb & fm[4]).bit_count(), (white_pawn_bb & fm[5]).bit_count(),
        (white_pawn_bb & fm[6]).bit_count(), (white_pawn_bb & fm[7]).bit_count()
    ]
    black_pawns_per_col = [
        (black_pawn_bb & fm[0]).bit_count(), (black_pawn_bb & fm[1]).bit_count(),
        (black_pawn_bb & fm[2]).bit_count(), (black_pawn_bb & fm[3]).bit_count(),
        (black_pawn_bb & fm[4]).bit_count(), (black_pawn_bb & fm[5]).bit_count(),
        (black_pawn_bb & fm[6]).bit_count(), (black_pawn_bb & fm[7]).bit_count()
    ]

    white_pawn_atk = 0
    black_pawn_atk = 0
    bb = white_pawn_bb
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        white_pawn_atk |= PAWN_ATTACKS[WHITE][s]
    bb = black_pawn_bb
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        black_pawn_atk |= PAWN_ATTACKS[BLACK][s]

    white_safe_pawn_atk = white_pawn_atk & ~black_pawn_atk
    black_safe_pawn_atk = black_pawn_atk & ~white_pawn_atk

    piece_count = occ.bit_count()

    bb = white_pawn_bb
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        if (PASSED_PAWN_MASK_WHITE[s] & black_pawn_bb) == 0:
            rank = s >> 3
            file = s & 7
            material -= passed_base + (rank * rank) * passed_rank_sq
            if max(abs(bk_rank - 7), abs(bk_file - file)) > (7 - rank) + (0 if board.side_to_move == BLACK else 1):
                material -= passed_unstoppable

    bb = black_pawn_bb
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        if (PASSED_PAWN_MASK_BLACK[s] & white_pawn_bb) == 0:
            rank = s >> 3
            file = s & 7
            material += passed_base + ((7 - rank) * (7 - rank)) * passed_rank_sq
            if max(abs(wk_rank - 0), abs(wk_file - file)) > rank + (0 if board.side_to_move == WHITE else 1):
                material += passed_unstoppable

    if (board.bitboards[WHITE][BISHOP]).bit_count() >= 2:
        material -= bishop_pair
    if (board.bitboards[BLACK][BISHOP]).bit_count() >= 2:
        material += bishop_pair

    if piece_count <= 6 and abs(total_material) >= 3:
        if total_material < 0:
            edge_dist = min(bk_rank, 7 - bk_rank, bk_file, 7 - bk_file)
            king_dist = max(abs(wk_rank - bk_rank), abs(wk_file - bk_file))
            material -= (3 - edge_dist) * eg_king_edge + (7 - king_dist) * eg_king_dist
        elif total_material > 0:
            edge_dist = min(wk_rank, 7 - wk_rank, wk_file, 7 - wk_file)
            king_dist = max(abs(bk_rank - wk_rank), abs(bk_file - wk_file))
            material += (3 - edge_dist) * eg_king_edge + (7 - king_dist) * eg_king_dist

    for file in range(8):
        wpc = white_pawns_per_col[file]
        bpc = black_pawns_per_col[file]
        if wpc >= 2:
            material += doubled_pawn * (wpc - 1)
        if bpc >= 2:
            material -= doubled_pawn * (bpc - 1)
        if wpc > 0:
            left  = white_pawns_per_col[file - 1] if file > 0 else 0
            right = white_pawns_per_col[file + 1] if file < 7 else 0
            if left == 0 and right == 0:
                material += isolated_pawn * wpc
        if bpc > 0:
            left  = black_pawns_per_col[file - 1] if file > 0 else 0
            right = black_pawns_per_col[file + 1] if file < 7 else 0
            if left == 0 and right == 0:
                material -= isolated_pawn * bpc

    if piece_count > 6:
        if (board.bitboards[WHITE][KNIGHT] >> sq(1, 0)) & 1: material += undeveloped_minor
        if (board.bitboards[WHITE][KNIGHT] >> sq(6, 0)) & 1: material += undeveloped_minor
        if (board.bitboards[WHITE][BISHOP] >> sq(2, 0)) & 1: material += undeveloped_minor
        if (board.bitboards[WHITE][BISHOP] >> sq(5, 0)) & 1: material += undeveloped_minor
        if (board.bitboards[BLACK][KNIGHT] >> sq(1, 7)) & 1: material -= undeveloped_minor
        if (board.bitboards[BLACK][KNIGHT] >> sq(6, 7)) & 1: material -= undeveloped_minor
        if (board.bitboards[BLACK][BISHOP] >> sq(2, 7)) & 1: material -= undeveloped_minor
        if (board.bitboards[BLACK][BISHOP] >> sq(5, 7)) & 1: material -= undeveloped_minor

        white_king_safety = 0.0
        black_king_safety = 0.0
        for dc in (-1, 0, 1):
            c = wk_file + dc
            if 0 <= c <= 7:
                if wk_rank + 1 <= 7 and (white_pawn_bb >> sq(c, wk_rank + 1)) & 1:
                    white_king_safety += king_shield_full
                elif wk_rank + 2 <= 7 and (white_pawn_bb >> sq(c, wk_rank + 2)) & 1:
                    white_king_safety += king_shield_half
            c = bk_file + dc
            if 0 <= c <= 7:
                if bk_rank - 1 >= 0 and (black_pawn_bb >> sq(c, bk_rank - 1)) & 1:
                    black_king_safety += king_shield_full
                elif bk_rank - 2 >= 0 and (black_pawn_bb >> sq(c, bk_rank - 2)) & 1:
                    black_king_safety += king_shield_half

        material -= white_king_safety * king_shield_weight
        material += black_king_safety * king_shield_weight

        if 3 <= wk_file <= 4: material += king_center_file
        if 3 <= bk_file <= 4: material -= king_center_file

        for dc in (-1, 0, 1):
            c = wk_file + dc
            if 0 <= c <= 7:
                if white_pawns_per_col[c] == 0:
                    material += king_file_open if black_pawns_per_col[c] == 0 else king_file_semi_open
            c = bk_file + dc
            if 0 <= c <= 7:
                if black_pawns_per_col[c] == 0:
                    material -= king_file_open if white_pawns_per_col[c] == 0 else king_file_semi_open

        straight_enemy_b = board.bitboards[BLACK][ROOK]  | board.bitboards[BLACK][QUEEN]
        diag_enemy_b     = board.bitboards[BLACK][BISHOP] | board.bitboards[BLACK][QUEEN]
        straight_enemy_w = board.bitboards[WHITE][ROOK]  | board.bitboards[WHITE][QUEEN]
        diag_enemy_w     = board.bitboards[WHITE][BISHOP] | board.bitboards[WHITE][QUEEN]

        black_major_attackers  = bool(get_rook_attacks(white_king_pos, occ) & straight_enemy_b)
        black_major_attackers += bool(get_bishop_attacks(white_king_pos, occ) & diag_enemy_b)
        white_major_attackers  = bool(get_rook_attacks(black_king_pos, occ) & straight_enemy_w)
        white_major_attackers += bool(get_bishop_attacks(black_king_pos, occ) & diag_enemy_w)

        material += black_major_attackers * king_zone_major
        material -= white_major_attackers * king_zone_major

    white_mobility = 0
    black_mobility = 0

    bb = board.bitboards[WHITE][ROOK]
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        f = s & 7
        atk = get_rook_attacks(s, occ)
        white_mobility += (atk & ~w_occ).bit_count()
        if white_pawns_per_col[f] == 0:
            material -= rook_open_file if black_pawns_per_col[f] == 0 else rook_semi_open_file
        if (s >> 3) == 6:
            material -= rook_on_7th

    bb = board.bitboards[BLACK][ROOK]
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        f = s & 7
        atk = get_rook_attacks(s, occ)
        black_mobility += (atk & ~b_occ).bit_count()
        if black_pawns_per_col[f] == 0:
            material += rook_open_file if white_pawns_per_col[f] == 0 else rook_semi_open_file
        if (s >> 3) == 1:
            material += rook_on_7th

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

    material -= white_mobility * mobility_w
    material += black_mobility * mobility_w

    OUTPOST_BONUS_KNIGHT = W.w("OUTPOST_KNIGHT", phase)
    OUTPOST_BONUS_BISHOP = W.w("OUTPOST_BISHOP", phase)
    REACHABLE_OUTPOST_KNIGHT = W.w("REACHABLE_OUTPOST_KNIGHT", phase)
    REACHABLE_OUTPOST_BISHOP = W.w("REACHABLE_OUTPOST_BISHOP", phase)

    white_outpost_squares = 0
    bb = white_pawn_bb
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        f = s & 7
        r = s >> 3
        if f > 0: white_outpost_squares |= (1 << ((r + 1) * 8 + f - 1)) if r < 7 else 0
        if f < 7: white_outpost_squares |= (1 << ((r + 1) * 8 + f + 1)) if r < 7 else 0
    white_outpost_squares &= ~black_pawn_atk

    black_outpost_squares = 0
    bb = black_pawn_bb
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        f = s & 7
        r = s >> 3
        if f > 0: black_outpost_squares |= (1 << ((r - 1) * 8 + f - 1)) if r > 0 else 0
        if f < 7: black_outpost_squares |= (1 << ((r - 1) * 8 + f + 1)) if r > 0 else 0
    black_outpost_squares &= ~white_pawn_atk

    bb = board.bitboards[WHITE][KNIGHT]
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        if (white_outpost_squares >> s) & 1:
            material -= OUTPOST_BONUS_KNIGHT
        elif KNIGHT_ATTACKS[s] & white_outpost_squares:
            material -= REACHABLE_OUTPOST_KNIGHT

    bb = board.bitboards[WHITE][BISHOP]
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        if (white_outpost_squares >> s) & 1:
            material -= OUTPOST_BONUS_BISHOP
        elif get_bishop_attacks(s, occ) & white_outpost_squares:
            material -= REACHABLE_OUTPOST_BISHOP

    bb = board.bitboards[BLACK][KNIGHT]
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        if (black_outpost_squares >> s) & 1:
            material += OUTPOST_BONUS_KNIGHT
        elif KNIGHT_ATTACKS[s] & black_outpost_squares:
            material += REACHABLE_OUTPOST_KNIGHT

    bb = board.bitboards[BLACK][BISHOP]
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        if (black_outpost_squares >> s) & 1:
            material += OUTPOST_BONUS_BISHOP
        elif get_bishop_attacks(s, occ) & black_outpost_squares:
            material += REACHABLE_OUTPOST_BISHOP

    _update_threat_tables(phase)

    white_minor_t = board.bitboards[WHITE][KNIGHT] | board.bitboards[WHITE][BISHOP]
    black_minor_t = board.bitboards[BLACK][KNIGHT] | board.bitboards[BLACK][BISHOP]
    white_rook_t  = board.bitboards[WHITE][ROOK]
    black_rook_t  = board.bitboards[BLACK][ROOK]

    black_piece_types = [
        board.bitboards[BLACK][PAWN],   board.bitboards[BLACK][KNIGHT],
        board.bitboards[BLACK][BISHOP], board.bitboards[BLACK][ROOK],
        board.bitboards[BLACK][QUEEN],
    ]
    white_piece_types = [
        board.bitboards[WHITE][PAWN],   board.bitboards[WHITE][KNIGHT],
        board.bitboards[WHITE][BISHOP], board.bitboards[WHITE][ROOK],
        board.bitboards[WHITE][QUEEN],
    ]

    bb = white_pawn_atk & b_occ & ~black_safe_pawn_atk
    while bb:
        t = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        material -= _THREAT_BY_MINOR[_get_piece_type_idx(black_piece_types, t)]

    bb = black_pawn_atk & w_occ & ~white_safe_pawn_atk
    while bb:
        t = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        material += _THREAT_BY_MINOR[_get_piece_type_idx(white_piece_types, t)]

    bb = white_minor_t
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        atk = KNIGHT_ATTACKS[s] if (board.bitboards[WHITE][KNIGHT] >> s) & 1 else get_bishop_attacks(s, occ)
        targets = atk & b_occ & ~black_safe_pawn_atk
        while targets:
            t = (targets & -targets).bit_length() - 1
            targets &= targets - 1
            material -= _THREAT_BY_MINOR[_get_piece_type_idx(black_piece_types, t)]

    bb = black_minor_t
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        atk = KNIGHT_ATTACKS[s] if (board.bitboards[BLACK][KNIGHT] >> s) & 1 else get_bishop_attacks(s, occ)
        targets = atk & w_occ & ~white_safe_pawn_atk
        while targets:
            t = (targets & -targets).bit_length() - 1
            targets &= targets - 1
            material += _THREAT_BY_MINOR[_get_piece_type_idx(white_piece_types, t)]

    bb = white_rook_t
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        targets = get_rook_attacks(s, occ) & b_occ & ~black_safe_pawn_atk
        while targets:
            t = (targets & -targets).bit_length() - 1
            targets &= targets - 1
            material -= _THREAT_BY_ROOK[_get_piece_type_idx(black_piece_types, t)]

    bb = black_rook_t
    while bb:
        s = (bb & -bb).bit_length() - 1
        bb &= bb - 1
        targets = get_rook_attacks(s, occ) & w_occ & ~white_safe_pawn_atk
        while targets:
            t = (targets & -targets).bit_length() - 1
            targets &= targets - 1
            material += _THREAT_BY_ROOK[_get_piece_type_idx(white_piece_types, t)]

    white_atk_all = 0
    tmp = white_minor_t | white_rook_t | board.bitboards[WHITE][QUEEN]
    while tmp:
        a = (tmp & -tmp).bit_length() - 1
        tmp &= tmp - 1
        if   (board.bitboards[WHITE][KNIGHT] >> a) & 1: white_atk_all |= KNIGHT_ATTACKS[a]
        elif (board.bitboards[WHITE][BISHOP] >> a) & 1: white_atk_all |= get_bishop_attacks(a, occ)
        elif (board.bitboards[WHITE][ROOK]   >> a) & 1: white_atk_all |= get_rook_attacks(a, occ)
        else:                                            white_atk_all |= get_queen_attacks(a, occ)

    black_atk_all = 0
    tmp = black_minor_t | black_rook_t | board.bitboards[BLACK][QUEEN]
    while tmp:
        a = (tmp & -tmp).bit_length() - 1
        tmp &= tmp - 1
        if   (board.bitboards[BLACK][KNIGHT] >> a) & 1: black_atk_all |= KNIGHT_ATTACKS[a]
        elif (board.bitboards[BLACK][BISHOP] >> a) & 1: black_atk_all |= get_bishop_attacks(a, occ)
        elif (board.bitboards[BLACK][ROOK]   >> a) & 1: black_atk_all |= get_rook_attacks(a, occ)
        else:                                            black_atk_all |= get_queen_attacks(a, occ)

    white_king_atk = KING_ATTACKS[white_king_pos]
    black_king_atk = KING_ATTACKS[black_king_pos]

    white_defended = white_pawn_atk | white_atk_all | white_king_atk
    black_defended = black_pawn_atk | black_atk_all | black_king_atk

    material += (w_occ & ~white_defended & black_atk_all).bit_count() * _HANGING
    material -= (b_occ & ~black_defended & white_atk_all).bit_count() * _HANGING

    TEMPO = W.w("TEMPO", phase)
    if board.side_to_move == WHITE:
        material -= TEMPO
    else:
        material += TEMPO


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
    promotion = (move >> 19) & 0x7
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
    piece_on_square_value = piece_value[promotion] if promotion != NONE_PIECE else piece_value[attacker_type]
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

def move_score(move, ply, board, piece, captured_piece, flag, prev_piece=None, prev_to=None,prev_piece2=None, prev_to2=None):
    if captured_piece != NONE_PIECE or flag == EN_PASSANT:
        see_value = SEE(board, move)
        to_sq = (move >> 6) & 0x3F
        captured_type = PAWN if flag == EN_PASSANT else captured_piece
        cap_hist = CAPTURE_HISTORY[piece][to_sq][captured_type]
        if cap_hist > HISTORY_MAX:
            cap_hist = HISTORY_MAX
        elif cap_hist < -HISTORY_MAX:
            cap_hist = -HISTORY_MAX
        cap_bonus = cap_hist / 5000.0
        mvv_lva_bonus = (MVV_LVA_VALUE[captured_type] * 10 - MVV_LVA_VALUE[piece]) / 1000000.0
        if see_value > 0:
            return 900000 + see_value + cap_bonus + mvv_lva_bonus, see_value
        elif see_value == 0:
            return 800000 + cap_bonus + mvv_lva_bonus, see_value
        else:
            return -100000 + see_value + cap_bonus + mvv_lva_bonus, see_value
    killer0 = KILLER[ply][0]
    killer1 = KILLER[ply][1]
    from_sq = move & 0x3F
    to_sq = (move >> 6) & 0x3F
    if killer0 is not None and from_sq == (killer0 & 0x3F) and to_sq == ((killer0 >> 6) & 0x3F):
        return 700000, None
    if killer1 is not None and from_sq == (killer1 & 0x3F) and to_sq == ((killer1 >> 6) & 0x3F):
        return 600000, None
    cont = CONT_HISTORY[piece][to_sq] if piece is not None else 0
    if prev_piece is not None:
        cont += CONT_HIST_PREV[prev_piece][prev_to][piece][to_sq]
    if prev_piece2 is not None:
        cont += CONT_HIST_PREV2[prev_piece2][prev_to2][piece][to_sq]
    total = HISTORY[from_sq][to_sq] + cont
    if total > HISTORY_MAX:
        total = HISTORY_MAX
    elif total < -HISTORY_MAX:
        total = -HISTORY_MAX
    return total, None

def ordered_moves(board, moves_list, ply, prev_piece=None, prev_to=None, prev_piece2=None, prev_to2=None):
    scored = []
    append = scored.append
    see_cache = {}
    for move in moves_list:
        piece = (move >> 12) & 0x7
        captured_piece = (move >> 16) & 0x7
        flag = (move >> 22) & 0x7
        s, see_value = move_score(move, ply, board, piece, captured_piece, flag, prev_piece, prev_to,prev_piece2, prev_to2)
        if see_value is not None:
            see_cache[move] = see_value
        append((s, move))
    scored.sort(key=lambda t: t[0], reverse=True)
    return [m for _, m in scored], see_cache


def _ci(color):
    return WHITE if color == "white" else BLACK


def eval_cached(board):
    key = board.hash
    idx = key & EVAL_CACHE_MASK
    if EVAL_CACHE_USED[idx] and EVAL_CACHE_HASH[idx] == key:
        return EVAL_CACHE_VALUE[idx]
    v = bewerte_material(board)
    EVAL_CACHE_HASH[idx] = key
    EVAL_CACHE_VALUE[idx] = v
    EVAL_CACHE_USED[idx] = 1
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

def negamax(board, depth, color, alpha, beta, is_null_move=False, ply=0, cut_node=False, prev_move=None, prev_move2=None, ext_count=0):
    alpha_orig = alpha
    global NODE_COUNT, SEARCH_ABORTED
    NODE_COUNT += 1

    own_idx = _ci(color)
    in_check_now = is_in_check(board, own_idx)
    is_pv = (beta - alpha) > 1
    prev_piece = (prev_move >> 12) & 0x7 if prev_move is not None else None
    prev_to = (prev_move >> 6) & 0x3F if prev_move is not None else None
    prev_piece2 = (prev_move2 >> 12) & 0x7 if prev_move2 is not None else None
    prev_to2 = (prev_move2 >> 6) & 0x3F if prev_move2 is not None else None

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
    piece_count_nm = popcount(board.all_occupancy)
    has_major_piece = popcount(board.bitboards[own_idx][ROOK] | board.bitboards[own_idx][QUEEN]) > 0

    corr_idx = None
    if in_check_now:
        static_eval = -STATIC_EVAL[ply - 1] if ply > 0 else 0.0
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
            and not is_pv
            and abs(alpha) < MATE_THRESHOLD
            and abs(beta) < MATE_THRESHOLD
    ):
        rfp_margin = (0.9 if improving else 1.3) * depth
        if static_eval - rfp_margin >= beta:
            return static_eval

    if (
            depth >= 4 and not in_check_now and not is_null_move
            and not is_pv
            and piece_count_nm > 6 and has_major_piece
            and abs(beta) < MATE_THRESHOLD
    ):
        r = min(3, depth // 3 + 1)
        make_null_move(board)
        null_score = -negamax(board, depth - 1 - r, next_color, -beta, -beta + 1,
                              is_null_move=True, ply=ply + 1, cut_node=True, ext_count=ext_count)
        unmake_null_move(board)
        if null_score >= beta:
            return beta

    if time.time() - SEARCH_START > SEARCH_LIMIT:
        SEARCH_ABORTED = True
        return eval_cached(board) if color == "black" else -eval_cached(board)

    if debug:
        print(f"{'  ' * depth}Tiefe {depth} | {color} | alpha={alpha} beta={beta}", file=sys.stderr)

    if tt_move is None and depth >= 4 and not in_check_now:
        depth -= 1

    if depth == 0:
        return quiescence(board, alpha, beta, color, ply)

    moves_list, see_cache = ordered_moves(board, generate_legal_moves(board), ply, prev_piece, prev_to, prev_piece2, prev_to2)

    if not moves_list:
        if in_check_now:
            return -(MATE_VALUE - ply)
        return 0

    if tt_move is not None and tt_move in moves_list:
        moves_list.remove(tt_move)
        moves_list.insert(0, tt_move)

    MULTICUT_MAX_MOVES = 6
    MULTICUT_THRESHOLD = 3

    extension = 0
    negative_extension = False
    MAX_EXTENSIONS = 16
    if (
            depth >= 6
            and tt_move is not None
            and idx != -1
            and TT_DEPTH[idx] >= depth - 3
            and TT_BOUND[idx] != 2
            and ply > 0
            and abs(beta) < MATE_THRESHOLD
            and abs(TT_SCORE[idx]) < MATE_THRESHOLD
    ):
        tt_score_local = score_from_tt(TT_SCORE[idx], ply)
        singular_beta = tt_score_local - (0.5 + 0.1 * depth)
        reduced_depth = (depth - 1) // 2
        fail_high_count = 0
        mc_fail_high_count = 0
        best_alt_score = -9999999
        tested = 0
        for alt_move in moves_list:
            if alt_move == tt_move:
                continue
            tested += 1
            make_move(board, alt_move)
            alt_score = -negamax(board, reduced_depth, next_color, -singular_beta - 1, -singular_beta,
                                 ply=ply + 1, cut_node=True, ext_count=ext_count)
            unmake_move(board)
            if alt_score > best_alt_score:
                best_alt_score = alt_score
            if alt_score >= beta:
                mc_fail_high_count += 1
            if alt_score >= singular_beta:
                fail_high_count += 1
                extension = 0
            elif fail_high_count == 0:
                singularity_margin = singular_beta - best_alt_score
                if not is_pv and singularity_margin > 3.0:
                    extension = 3
                elif singularity_margin > 1.5:
                    extension = 2
                else:
                    extension = 1
            if not is_pv and cut_node and mc_fail_high_count >= MULTICUT_THRESHOLD:
                return beta
            if fail_high_count > 0 and mc_fail_high_count < MULTICUT_THRESHOLD:
                break
            if tested >= MULTICUT_MAX_MOVES:
                break
        if fail_high_count > 0 and mc_fail_high_count < MULTICUT_THRESHOLD:
            negative_extension = True

    best_score = -9999999
    best_move_here = None
    move_index = 0

    futility_stand_pat = None
    skip_futility = False
    if depth <= 3 and not in_check_now:
        skip_futility = _side_has_hanging_piece(board, own_idx)
        if not skip_futility:
            futility_stand_pat = static_eval

    quiet_tried = []
    quiet_tried_pieces = {}
    captures_tried = []

    for move in moves_list:
        captured_piece = (move >> 16) & 0x7
        flag = (move >> 22) & 0x7
        is_capture = captured_piece != NONE_PIECE or flag == EN_PASSANT
        is_promotion = ((move >> 19) & 0x7) != NONE_PIECE
        from_sq_pv = move & 0x3F
        to_sq_pv = (move >> 6) & 0x3F

        if (
                move_index > 0
                and depth <= 8
                and not in_check_now
                and not is_pv
                and not is_capture
                and not is_promotion
                and move != tt_move
        ):
            lmp_limit = (4 + 4 * depth) if improving else (2 + 2 * depth)
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
                and not is_pv
        ):
            see_margin = -1.0 * depth
            if see_cache.get(move, 0) < see_margin:
                move_index += 1
                continue

        if (
                move_index > 0
                and depth <= 6
                and not is_capture
                and not is_promotion
                and not in_check_now
                and not is_pv
                and move != tt_move
        ):
            quiet_see_margin = -1.0 * depth
            if SEE_quiet(board, move) < quiet_see_margin:
                move_index += 1
                continue

        if (
                move_index > 0
                and depth <= 3
                and not in_check_now
                and not is_pv
                and not is_capture
                and not is_promotion
                and not skip_futility
        ):
            futility_margin = 1.0 + 1.5 * depth
            if futility_stand_pat + futility_margin < alpha:
                move_index += 1
                continue

        make_move(board, move)
        new_depth = depth - 1
        gives_check_now = is_in_check(board, board.side_to_move)
        new_ext_count = ext_count
        if gives_check_now and ply < 64 and new_ext_count < MAX_EXTENSIONS:
            new_depth += 1
            new_ext_count += 1
        if move_index == 0:
            if extension > 0 and new_ext_count < MAX_EXTENSIONS:
                new_depth += extension
                new_ext_count += 1
            elif negative_extension:
                new_depth -= 1

        if move_index == 0:
            score_result = -negamax(board, new_depth, next_color, -beta, -alpha, ply=ply + 1, cut_node=False,
                                    prev_move=move, prev_move2=prev_move, ext_count=new_ext_count)
        else:
            killer0 = KILLER[ply][0]
            killer1 = KILLER[ply][1]
            from_sq = move & 0x3F
            to_sq = (move >> 6) & 0x3F
            is_killer = (
                    (killer0 is not None and from_sq == (killer0 & 0x3F) and to_sq == ((killer0 >> 6) & 0x3F))
                    or (killer1 is not None and from_sq == (killer1 & 0x3F) and to_sq == ((killer1 >> 6) & 0x3F))
            )
            can_reduce = (
                    move_index >= 3
                    and new_depth >= 2
                    and not is_capture
                    and not is_promotion
                    and not in_check_now
                    and not is_killer
            )

            if can_reduce and gives_check_now:
                can_reduce = False

            if can_reduce:
                reduction = _LMR_TABLE[min(new_depth, 63)][min(move_index, 63)]
                if cut_node:
                    reduction += 1
                if not improving:
                    reduction += 1
                reduced_depth = max(1, new_depth - reduction)
            else:
                reduced_depth = new_depth

            score_result = -negamax(board, reduced_depth, next_color, -alpha - 1, -alpha,
                                    ply=ply + 1, cut_node=True, prev_move=move, prev_move2=prev_move,
                                    ext_count=new_ext_count)
            if score_result > alpha:
                score_result = -negamax(board, new_depth, next_color, -beta, -alpha,
                                        ply=ply + 1, cut_node=False, prev_move=move, prev_move2=prev_move,
                                        ext_count=new_ext_count)

        unmake_move(board)

        if score_result > best_score:
            best_score = score_result
            best_move_here = move

        if score_result > alpha:
            alpha = score_result

        if alpha >= beta:
            if not is_capture:
                killer0 = KILLER[ply][0]
                from_sq = move & 0x3F
                to_sq = (move >> 6) & 0x3F
                if killer0 is None or (killer0 & 0x3F) != from_sq or ((killer0 >> 6) & 0x3F) != to_sq:
                    KILLER[ply][1] = KILLER[ply][0]
                    KILLER[ply][0] = move
                HISTORY[from_sq][to_sq] += depth * depth
                if HISTORY[from_sq][to_sq] > HISTORY_MAX:
                    HISTORY[from_sq][to_sq] = HISTORY_MAX
                piece_moved = (move >> 12) & 0x7
                CONT_HISTORY[piece_moved][to_sq] += depth * depth
                if CONT_HISTORY[piece_moved][to_sq] > HISTORY_MAX:
                    CONT_HISTORY[piece_moved][to_sq] = HISTORY_MAX
                if prev_piece is not None:
                    CONT_HIST_PREV[prev_piece][prev_to][piece_moved][to_sq] += depth * depth
                    if CONT_HIST_PREV[prev_piece][prev_to][piece_moved][to_sq] > HISTORY_MAX:
                        CONT_HIST_PREV[prev_piece][prev_to][piece_moved][to_sq] = HISTORY_MAX
                if prev_piece2 is not None:
                    CONT_HIST_PREV2[prev_piece2][prev_to2][piece_moved][to_sq] += depth * depth
                    if CONT_HIST_PREV2[prev_piece2][prev_to2][piece_moved][to_sq] > HISTORY_MAX:
                        CONT_HIST_PREV2[prev_piece2][prev_to2][piece_moved][to_sq] = HISTORY_MAX
                for qf, qt in quiet_tried:
                    qpiece = quiet_tried_pieces.get((qf, qt), 0)
                    HISTORY[qf][qt] -= depth * depth // 2
                    if HISTORY[qf][qt] < -HISTORY_MAX:
                        HISTORY[qf][qt] = -HISTORY_MAX
                    CONT_HISTORY[qpiece][qt] -= depth * depth // 2
                    if CONT_HISTORY[qpiece][qt] < -HISTORY_MAX:
                        CONT_HISTORY[qpiece][qt] = -HISTORY_MAX
                    if prev_piece is not None:
                        CONT_HIST_PREV[prev_piece][prev_to][qpiece][qt] -= depth * depth // 2
                        if CONT_HIST_PREV[prev_piece][prev_to][qpiece][qt] < -HISTORY_MAX:
                            CONT_HIST_PREV[prev_piece][prev_to][qpiece][qt] = -HISTORY_MAX
                    if prev_piece2 is not None:
                        CONT_HIST_PREV2[prev_piece2][prev_to2][qpiece][qt] -= depth * depth // 2
                        if CONT_HIST_PREV2[prev_piece2][prev_to2][qpiece][qt] < -HISTORY_MAX:
                            CONT_HIST_PREV2[prev_piece2][prev_to2][qpiece][qt] = -HISTORY_MAX
            else:
                to_sq = (move >> 6) & 0x3F
                piece_moved = (move >> 12) & 0x7
                captured_now = (move >> 16) & 0x7
                flag_now = (move >> 22) & 0x7
                captured_type_now = PAWN if flag_now == EN_PASSANT else captured_now
                CAPTURE_HISTORY[piece_moved][to_sq][captured_type_now] += depth * depth
                for cf_piece, cto, ccap in captures_tried:
                    CAPTURE_HISTORY[cf_piece][cto][ccap] -= depth * depth // 2
            break

        if not is_capture:
            from_sq_qt = move & 0x3F
            to_sq_qt = (move >> 6) & 0x3F
            quiet_tried.append((from_sq_qt, to_sq_qt))
            quiet_tried_pieces[(from_sq_qt, to_sq_qt)] = (move >> 12) & 0x7
        else:
            to_sq_ct = (move >> 6) & 0x3F
            piece_ct = (move >> 12) & 0x7
            captured_ct = (move >> 16) & 0x7
            flag_ct = (move >> 22) & 0x7
            captured_type_ct = PAWN if flag_ct == EN_PASSANT else captured_ct
            captures_tried.append((piece_ct, to_sq_ct, captured_type_ct))
        move_index += 1


    if not SEARCH_ABORTED:
        if not in_check_now and corr_idx is not None and abs(best_score) < MATE_THRESHOLD:
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

    own_idx = _ci(color)
    in_check_now = is_in_check(board, own_idx)

    if time.time() - SEARCH_START > SEARCH_LIMIT:
        eval_value = eval_cached(board)
        return eval_value if color == "black" else -eval_value

    if ply >= 127:
        eval_value = eval_cached(board)
        return eval_value if color == "black" else -eval_value

    if depth <= 0 and not in_check_now:
        eval_value = eval_cached(board)
        return eval_value if color == "black" else -eval_value

    if depth <= -8:
        eval_value = eval_cached(board)
        return eval_value if color == "black" else -eval_value

    next_color = "white" if color == "black" else "black"

    if in_check_now:
        moves_list, _ = ordered_moves(board, generate_legal_moves(board), ply)
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
    corr_idx_qs = compute_pawn_hash(board) & CORR_HIST_MASK
    stand_pat += CORRECTION_HISTORY[own_idx][corr_idx_qs]

    if stand_pat >= beta:
        return stand_pat
    if stand_pat > alpha:
        alpha = stand_pat

    candidate_moves = generate_legal_captures(board)
    capture_moves = []
    append = capture_moves.append
    for move in candidate_moves:
        captured_piece = (move >> 16) & 0x7
        flag = (move >> 22) & 0x7
        is_real_capture = captured_piece != NONE_PIECE or flag == EN_PASSANT
        see_value = SEE(board, move) if is_real_capture else 800000
        if is_real_capture:
            piece_moved = (move >> 12) & 0x7
            captured_type = PAWN if flag == EN_PASSANT else captured_piece
            mvv_lva_value = MVV_LVA_VALUE[captured_type] * 10 - MVV_LVA_VALUE[piece_moved]
        else:
            mvv_lva_value = 0
        append((see_value, mvv_lva_value, move))
    capture_moves.sort(key=lambda t: (t[0], t[1]), reverse=True)

    best = stand_pat
    for see_value, _, move in capture_moves:
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

        if score > best:
            best = score
        if score > alpha:
            alpha = score
        if alpha >= beta:
            break

    if depth == 10 and alpha < beta and abs(alpha) < MATE_THRESHOLD and stand_pat + 1.0 > alpha:
        opp_idx = 1 - own_idx
        enemy_king_bb = board.bitboards[opp_idx][KING]
        if enemy_king_bb:
            enemy_king_sq = lsb_index(enemy_king_bb)
            candidates_scanned = 0
            checks_searched = 0
            check_futility_margin = 0.5
            for move in generate_legal_moves(board):
                captured_piece_qc = (move >> 16) & 0x7
                flag_qc = (move >> 22) & 0x7
                if captured_piece_qc != NONE_PIECE or flag_qc == EN_PASSANT:
                    continue
                if candidates_scanned >= 12:
                    break
                candidates_scanned += 1
                if not _gives_direct_check_fast(board, move, own_idx, enemy_king_sq):
                    continue
                if stand_pat + check_futility_margin <= alpha:
                    continue
                make_move(board, move)
                score = -quiescence(board, -beta, -alpha, next_color, ply + 1, depth - 1)
                unmake_move(board)

                if score > best:
                    best = score
                if score > alpha:
                    alpha = score
                checks_searched += 1
                if alpha >= beta:
                    break
                if checks_searched >= 3:
                    break

    return best



def choose_move(board, color, depth=5, alpha=-1000000, beta=1000000):
    global SEARCH_ABORTED, NODE_COUNT
    moves_list, see_cache = ordered_moves(board, generate_legal_moves(board), 0)

    idx = tt_probe(board.hash)
    if idx != -1:
        tt_move = TT_MOVE[idx] if TT_MOVE[idx] != -1 else None
        if tt_move is not None and tt_move in moves_list:
            moves_list.remove(tt_move)
            moves_list.insert(0, tt_move)

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
    for i in range(13):
        for j in range(64):
            CONT_HISTORY[i][j] //= 2
    for pp in range(7):
        for pt in range(64):
            for p in range(7):
                for t in range(64):
                    CONT_HIST_PREV[pp][pt][p][t] //= 2
    for pp in range(7):
        for pt in range(64):
            for p in range(7):
                for t in range(64):
                    CONT_HIST_PREV2[pp][pt][p][t] //= 2
    for p in range(6):
        for t in range(64):
            for c in range(7):
                CAPTURE_HISTORY[p][t][c] //= 2

    TT_GENERATION += 1
    SEARCH_ABORTED = False
    SEARCH_START = time.time()
    SEARCH_LIMIT = time_limit
    soft_limit = time_limit * 0.6
    STATIC_EVAL[0] = eval_cached(board) if color == "black" else -eval_cached(board)

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
            aspiration_delta = 0.6
            window_alpha = prev_score - aspiration_delta
            window_beta = prev_score + aspiration_delta

        move, score, node_fraction, coverage = choose_move(board, color, depth, window_alpha, window_beta)

        while move is not None and (score <= window_alpha or score >= window_beta):
            if score <= window_alpha:
                window_alpha = max(-1000000, window_alpha - aspiration_delta)
            if score >= window_beta:
                window_beta = min(1000000, window_beta + aspiration_delta)
            aspiration_delta *= 2
            if window_alpha <= -1000000 and window_beta >= 1000000:
                move, score, node_fraction, coverage = choose_move(board, color, depth, -1000000, 1000000)
                break
            move, score, node_fraction, coverage = choose_move(board, color, depth, window_alpha, window_beta)
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





def _attackers_to_sq(board, s, occ):
    return (
        (PAWN_ATTACKS[WHITE][s] & board.bitboards[BLACK][PAWN]) |
        (PAWN_ATTACKS[BLACK][s] & board.bitboards[WHITE][PAWN]) |
        (KNIGHT_ATTACKS[s] & (board.bitboards[WHITE][KNIGHT] | board.bitboards[BLACK][KNIGHT])) |
        (get_bishop_attacks(s, occ) & (
            board.bitboards[WHITE][BISHOP] | board.bitboards[BLACK][BISHOP] |
            board.bitboards[WHITE][QUEEN]  | board.bitboards[BLACK][QUEEN]
        )) |
        (get_rook_attacks(s, occ) & (
            board.bitboards[WHITE][ROOK] | board.bitboards[BLACK][ROOK] |
            board.bitboards[WHITE][QUEEN] | board.bitboards[BLACK][QUEEN]
        )) |
        (KING_ATTACKS[s] & (board.bitboards[WHITE][KING] | board.bitboards[BLACK][KING]))
    )



def _s(mg, eg, phase):
    return (mg * phase + eg * (24 - phase)) / 2400

def _get_piece_type_idx(bbs_list, t):
    for i, bbs in enumerate(bbs_list):
        if (bbs >> t) & 1:
            return i + 1
    return 0


def _update_threat_tables(phase):
    global _THREAT_CACHE_PHASE, _THREAT_BY_MINOR, _THREAT_BY_ROOK, _HANGING
    if phase == _THREAT_CACHE_PHASE:
        return
    _THREAT_CACHE_PHASE = phase
    _THREAT_BY_MINOR = [0.0, _s(5,32,phase), _s(55,41,phase), _s(55,41,phase), _s(76,76,phase), _s(76,76,phase), 0.0]
    _THREAT_BY_ROOK  = [0.0, _s(3,44,phase), _s(37,68,phase), _s(37,68,phase), 0.0, _s(42,60,phase), 0.0]
    _HANGING         = _s(69, 36, phase)




def _gives_direct_check_fast(board, move, own_idx, enemy_king_sq):
    piece = (move >> 12) & 0x7
    promo = (move >> 19) & 0x7
    if promo != NONE_PIECE:
        piece = promo
    if piece == KING:
        return False
    from_sq = move & 0x3F
    to_sq = (move >> 6) & 0x3F
    if piece == KNIGHT:
        return bool(KNIGHT_ATTACKS[to_sq] & (1 << enemy_king_sq))
    if piece == PAWN:
        return bool(PAWN_ATTACKS[own_idx][to_sq] & (1 << enemy_king_sq))
    occ_after = (board.all_occupancy & ~(1 << from_sq)) | (1 << to_sq)
    if piece == BISHOP:
        return bool(get_bishop_attacks(to_sq, occ_after) & (1 << enemy_king_sq))
    if piece == ROOK:
        return bool(get_rook_attacks(to_sq, occ_after) & (1 << enemy_king_sq))
    if piece == QUEEN:
        return bool(get_queen_attacks(to_sq, occ_after) & (1 << enemy_king_sq))
    return False





def SEE_quiet(board, move):
    from_sq = move & 0x3F
    to_sq = (move >> 6) & 0x3F
    promotion = (move >> 19) & 0x7

    attacker_side = board.color_at[from_sq]
    attacker_type = board.piece_at_sq[from_sq]

    occ = board.all_occupancy & ~(1 << from_sq)

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

    gains = [0]
    piece_on_square_value = piece_value[promotion] if promotion != NONE_PIECE else piece_value[attacker_type]
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