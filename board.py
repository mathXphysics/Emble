# board.py - Bitboard-Repräsentation
# Bit-Index 0..63, Feld = rank*8 + file, rank 0 = Reihe 1, file 0 = Spalte a
# a1=0, h1=7, a8=56, h8=63

import zobrist

WHITE, BLACK = 0, 1
PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING = range(6)

FULL = 0xFFFFFFFFFFFFFFFF

FILE_A = 0x0101010101010101
FILE_H = FILE_A << 7
RANK_1 = 0xFF
RANK_8 = RANK_1 << 56
NONE_PIECE = 6
CR_WHITE_SHORT = 1
CR_WHITE_LONG  = 2
CR_BLACK_SHORT = 4
CR_BLACK_LONG  = 8
CR_ALL = CR_WHITE_SHORT | CR_WHITE_LONG | CR_BLACK_SHORT | CR_BLACK_LONG


piece_value = {PAWN: 1, KNIGHT: 3, BISHOP: 3, ROOK: 5, QUEEN: 9, KING: 99}

piece_square_table_knight = [
    [-50,-40,-30,-30,-30,-30,-40,-50],
    [-40,-20,+0,+0,+0,+0,-20,-40],
    [-30,+0,+10,+15,+15,+10,+0,-30],
    [-30,+5,+15,+20,+20,+15,+5,-30],
    [-30,+5,+15,+20,+20,+15,+5,-30],
    [-30,+0,+10,+15,+15,+10,+0,-30],
    [-40,-20,+0,+0,+0,+0,-20,-40],
    [-50,-40,-30,-30,-30,-30,-40,-50]
]
piece_square_table_bishop = [
    [-20,-10,-10,-10,-10,-10,-10,-20],
    [-10,+0,+0,+0,+0,+0,+0,-10],
    [-10,+0,+5,+10,+10,+5,+0,-10],
    [-10,+5,+5,+10,+10,+5,+5,-10],
    [-10,+0,+10,+10,+10,+10,+0,-10],
    [-10,+10,+10,+10,+10,+10,+10,-10],
    [-10,+5,+0,+0,+0,+0,+5,-10],
    [-20,-10,-10,-10,-10,-10,-10,-20],
]
piece_square_table_rook = [
    [+0,+0,+0,+0,+0,+0,+0,+0],
    [+5,+10,+10,+10,+10,+10,+10,+5],
    [-5,+0,+0,+0,+0,+0,+0,-5],
    [-5,+0,+0,+0,+0,+0,+0,-5],
    [-5,+0,+0,+0,+0,+0,+0,-5],
    [-5,+0,+0,+0,+0,+0,+0,-5],
    [-5,+0,+0,+0,+0,+0,+0,-5],
    [+0,+0,+0,+5,+5,+0,+0,+0]
]
piece_square_table_queen = [
    [-20,-10,-10,-5,-5,-10,-10,-20],
    [-10,+0,+0,+0,+0,+0,+0,+10],
    [-10,+0,+5,+5,+5,+5,+0,-10],
    [-5,+0,+5,+5,+5,+5,+0,-5],
    [+0,+0,+5,+5,+5,+5,+0,-5],
    [-10,+5,+5,+5,+5,+5,+5,-10],
    [-10,+0,+5,+0,+0,+0,+0,-10],
    [-20,-10,-10,-5,-5,-10,-10,-20]
]
piece_square_table_pawn = [
    [+0,+0,+0,+0,+0,+0,+0,+0],
    [+5,+5,+5,+5,+5,+5,+5,+5],
    [+10,+10,+20,+30,+30,+20,+10,+10],
    [+5,+5,+10,+25,+25,+10,+5,+5],
    [+0,+0,+0,+20,+20,+0,+0,+0],
    [-5,-10,-15,+0,+0,-15,-10,-5],
    [+5,+10,+10,-20,-20,+10,+10,+5],
    [+0,+0,+0,+0,+0,+0,+0,+0]
]
piece_square_table_king = [
    [-30,-40,-40,-50,-50,-40,-40,-30],
    [-30,-40,-40,-50,-50,-40,-40,-30],
    [-30,-40,-40,-50,-50,-40,-40,-30],
    [-30,-40,-40,-50,-50,-40,-40,-30],
    [-20,-30,-30,-40,-40,-30,-30,-20],
    [-10,-20,-20,-20,-20,-20,-20,-10],
    [+20,+20,+0,+0,+0,+0,+20,+20],
    [+20,+30,+5,+0,+0,+5,+30,+20]
]

_PST = {PAWN: piece_square_table_pawn, KNIGHT: piece_square_table_knight,
        BISHOP: piece_square_table_bishop, ROOK: piece_square_table_rook,
        QUEEN: piece_square_table_queen, KING: piece_square_table_king}


def _build_value_table():
    table = [[[0.0] * 64 for _ in range(6)] for _ in range(2)]
    for pt in range(6):
        pst = _PST[pt]
        val = piece_value[pt]
        for s in range(64):
            rank, file = s // 8, s % 8
            table[0][pt][s] = -(val + pst[7 - rank][file] / 100)  # WHITE
            table[1][pt][s] = (val + pst[rank][file] / 100)       # BLACK
    return table


VALUE_TABLE = _build_value_table()

def sq(file, rank):
    return rank * 8 + file

def file_of(square):
    return square & 7

def rank_of(square):
    return square >> 3

def bb_of_square(square):
    return 1 << square

def popcount(bb):
    return bb.bit_count()

def lsb_index(bb):
    return (bb & -bb).bit_length() - 1

def iter_squares(bb):
    while bb:
        s = lsb_index(bb)
        yield s
        bb &= bb - 1


class Board:
    def __init__(self):
        self.bitboards = [[0] * 6 for _ in range(2)]
        self.occupancy = [0, 0]
        self.all_occupancy = 0
        self.side_to_move = WHITE
        self.castling_rights = CR_ALL
        self.ep_square = None
        self.halfmove_clock = 0
        self.history = []
        self._setup_start_position()
        self.material_score = 0.0
        for color in (WHITE, BLACK):
            for pt in range(6):
                bb = self.bitboards[color][pt]
                while bb:
                    s = (bb & -bb).bit_length() - 1
                    bb &= bb - 1
                    self.material_score += VALUE_TABLE[color][pt][s]
        self.color_at = [-1] * 64
        self.piece_at_sq = [NONE_PIECE] * 64
        for s in range(64):
            info = self._scan_square(s)
            if info is not None:
                self.color_at[s], self.piece_at_sq[s] = info
        self.hash = zobrist.compute_hash(self)
        self.position_history = {self.hash: 1}

    def _setup_start_position(self):
        bb = self.bitboards
        bb[WHITE][PAWN]   = RANK_1 << 8
        bb[WHITE][ROOK]   = bb_of_square(sq(0,0)) | bb_of_square(sq(7,0))
        bb[WHITE][KNIGHT] = bb_of_square(sq(1,0)) | bb_of_square(sq(6,0))
        bb[WHITE][BISHOP] = bb_of_square(sq(2,0)) | bb_of_square(sq(5,0))
        bb[WHITE][QUEEN]  = bb_of_square(sq(3,0))
        bb[WHITE][KING]   = bb_of_square(sq(4,0))

        bb[BLACK][PAWN]   = RANK_1 << 48
        bb[BLACK][ROOK]   = bb_of_square(sq(0,7)) | bb_of_square(sq(7,7))
        bb[BLACK][KNIGHT] = bb_of_square(sq(1,7)) | bb_of_square(sq(6,7))
        bb[BLACK][BISHOP] = bb_of_square(sq(2,7)) | bb_of_square(sq(5,7))
        bb[BLACK][QUEEN]  = bb_of_square(sq(3,7))
        bb[BLACK][KING]   = bb_of_square(sq(4,7))

        self._recompute_occupancy()

    def _recompute_occupancy(self):
        self.occupancy[WHITE] = 0
        self.occupancy[BLACK] = 0
        for pt in range(6):
            self.occupancy[WHITE] |= self.bitboards[WHITE][pt]
            self.occupancy[BLACK] |= self.bitboards[BLACK][pt]
        self.all_occupancy = self.occupancy[WHITE] | self.occupancy[BLACK]

    def _scan_square(self, square):
        b = bb_of_square(square)
        for color in (WHITE, BLACK):
            for pt in range(6):
                if self.bitboards[color][pt] & b:
                    return color, pt
        return None

    def piece_at(self, square):
        c = self.color_at[square]
        if c == -1:
            return None
        return c, self.piece_at_sq[square]

    def print_ascii(self):
        symbols = {
            (WHITE, PAWN): "P", (WHITE, KNIGHT): "N", (WHITE, BISHOP): "B",
            (WHITE, ROOK): "R", (WHITE, QUEEN): "Q", (WHITE, KING): "K",
            (BLACK, PAWN): "p", (BLACK, KNIGHT): "n", (BLACK, BISHOP): "b",
            (BLACK, ROOK): "r", (BLACK, QUEEN): "q", (BLACK, KING): "k",
        }
        for rank in range(7, -1, -1):
            row = []
            for file in range(8):
                piece = self.piece_at(sq(file, rank))
                row.append(symbols[piece] if piece else ".")
            print(rank + 1, " ".join(row))
        print("  a b c d e f g h")