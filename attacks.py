from board import FILE_A, FILE_H, RANK_1, RANK_8, FULL

WHITE, BLACK = 0, 1


def _shift_north(bb):
    return (bb << 8) & FULL


def _shift_south(bb):
    return bb >> 8


def _shift_east(bb):
    return (bb << 1) & ~FILE_A & FULL


def _shift_west(bb):
    return (bb >> 1) & ~FILE_H


def _knight_attacks_from_square(square):
    bb = 1 << square
    attacks = 0
    attacks |= (bb << 17) & ~FILE_A & FULL
    attacks |= (bb << 15) & ~FILE_H & FULL
    attacks |= (bb << 10) & ~FILE_A & ~(FILE_A << 1) & FULL
    attacks |= (bb << 6)  & ~FILE_H & ~(FILE_H >> 1) & FULL
    attacks |= (bb >> 17) & ~FILE_H
    attacks |= (bb >> 15) & ~FILE_A
    attacks |= (bb >> 10) & ~FILE_H & ~(FILE_H >> 1)
    attacks |= (bb >> 6)  & ~FILE_A & ~(FILE_A << 1)
    return attacks & FULL


def _king_attacks_from_square(square):
    bb = 1 << square
    attacks = 0
    attacks |= _shift_north(bb)
    attacks |= _shift_south(bb)
    attacks |= _shift_east(bb)
    attacks |= _shift_west(bb)
    attacks |= _shift_north(_shift_east(bb))
    attacks |= _shift_north(_shift_west(bb))
    attacks |= _shift_south(_shift_east(bb))
    attacks |= _shift_south(_shift_west(bb))
    return attacks & FULL


def _white_pawn_attacks_from_square(square):
    bb = 1 << square
    return (_shift_north(_shift_east(bb)) | _shift_north(_shift_west(bb))) & FULL


def _black_pawn_attacks_from_square(square):
    bb = 1 << square
    return (_shift_south(_shift_east(bb)) | _shift_south(_shift_west(bb))) & FULL


KNIGHT_ATTACKS = [_knight_attacks_from_square(s) for s in range(64)]
KING_ATTACKS = [_king_attacks_from_square(s) for s in range(64)]
PAWN_ATTACKS = [
    [_white_pawn_attacks_from_square(s) for s in range(64)],
    [_black_pawn_attacks_from_square(s) for s in range(64)],
]


def pawn_pushes_single(square, color, occupancy):
    bb = 1 << square
    if color == WHITE:
        target = _shift_north(bb)
    else:
        target = _shift_south(bb)
    return target & ~occupancy


def pawn_pushes_double(square, color, occupancy):
    bb = 1 << square
    if color == WHITE:
        if not (bb & RANK_1 << 8):
            return 0
        one = _shift_north(bb) & ~occupancy
        if one == 0:
            return 0
        two = _shift_north(one) & ~occupancy
        return two
    else:
        if not (bb & RANK_8 >> 8):
            return 0
        one = _shift_south(bb) & ~occupancy
        if one == 0:
            return 0
        two = _shift_south(one) & ~occupancy
        return two


def _file_fill_masks():
    file_mask = [FILE_A << f for f in range(8)]
    adj = [0] * 8
    for f in range(8):
        m = file_mask[f]
        if f > 0: m |= file_mask[f - 1]
        if f < 7: m |= file_mask[f + 1]
        adj[f] = m
    return file_mask, adj

FILE_MASKS, ADJACENT_FILE_MASKS = _file_fill_masks()


def _passed_pawn_masks():
    white_masks = [0] * 64
    black_masks = [0] * 64
    for s in range(64):
        rank, file = s // 8, s % 8
        cols = ADJACENT_FILE_MASKS[file]
        w = 0
        for r in range(rank + 1, 8):
            w |= (RANK_1 << (r * 8))
        white_masks[s] = w & cols
        b = 0
        for r in range(0, rank):
            b |= (RANK_1 << (r * 8))
        black_masks[s] = b & cols
    return white_masks, black_masks

PASSED_PAWN_MASK_WHITE, PASSED_PAWN_MASK_BLACK = _passed_pawn_masks()