import random

random.seed(42)

WHITE, BLACK = 0, 1
PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING = range(6)

# ZOBRIST_PIECE[color][piece_type][square]
ZOBRIST_PIECE = [[[random.getrandbits(64) for _ in range(64)] for _ in range(6)] for _ in range(2)]

ZOBRIST_TURN = random.getrandbits(64)

ZOBRIST_CASTLING = [random.getrandbits(64) for _ in range(4)]

ZOBRIST_EP_FILE = [random.getrandbits(64) for _ in range(8)]


def compute_hash(board):
    h = 0
    for color in (WHITE, BLACK):
        for pt in range(6):
            bb = board.bitboards[color][pt]
            while bb:
                square = (bb & -bb).bit_length() - 1
                h ^= ZOBRIST_PIECE[color][pt][square]
                bb &= bb - 1

    if board.side_to_move == BLACK:
        h ^= ZOBRIST_TURN

    cr = board.castling_rights
    if cr & 1: h ^= ZOBRIST_CASTLING[0]
    if cr & 2: h ^= ZOBRIST_CASTLING[1]
    if cr & 4: h ^= ZOBRIST_CASTLING[2]
    if cr & 8: h ^= ZOBRIST_CASTLING[3]

    if board.ep_square is not None:
        h ^= ZOBRIST_EP_FILE[board.ep_square & 7]

    return h


def update_hash_piece(h, color, piece_type, square):
    return h ^ ZOBRIST_PIECE[color][piece_type][square]


def update_hash_castling(h, bit_index):
    return h ^ ZOBRIST_CASTLING[bit_index]

def compute_pawn_hash(board):
    h = 0
    for color in (WHITE, BLACK):
        bb = board.bitboards[color][PAWN]
        while bb:
            square = (bb & -bb).bit_length() - 1
            h ^= ZOBRIST_PIECE[color][PAWN][square]
            bb &= bb - 1
    return h
