import random

PIECES = ["B", "-B", "S", "-S", "L", "-L", "T", "-T", "D", "-D", "K", "-K"]

random.seed(42)
ZOBRIST_TABLE = {}
for row in range(8):
    for col in range(8):
        for piece in PIECES:
            ZOBRIST_TABLE[(row, col, piece)] = random.getrandbits(64)

ZOBRIST_TURN = random.getrandbits(64)

ZOBRIST_CASTLING = {
    "white_short": random.getrandbits(64),
    "white_long": random.getrandbits(64),
    "black_short": random.getrandbits(64),
    "black_long": random.getrandbits(64),
}
ZOBRIST_EP_FILE = [random.getrandbits(64) for _ in range(8)]

def compute_hash(board, color, white_short=True, white_long=True,
                  black_short=True, black_long=True, ep_file=None):
    h = 0
    for row in range(8):
        for col in range(8):
            piece = board[row][col]
            if piece != "0":
                h ^= ZOBRIST_TABLE[(row, col, piece)]
    if color == "black":
        h ^= ZOBRIST_TURN
    if white_short: h ^= ZOBRIST_CASTLING["white_short"]
    if white_long: h ^= ZOBRIST_CASTLING["white_long"]
    if black_short: h ^= ZOBRIST_CASTLING["black_short"]
    if black_long: h ^= ZOBRIST_CASTLING["black_long"]
    if ep_file is not None:
        h ^= ZOBRIST_EP_FILE[ep_file]
    return h

def update_hash(h, row, col, piece):
    return h ^ ZOBRIST_TABLE[(row, col, piece)]

def flip_turn(h):
    return h ^ ZOBRIST_TURN