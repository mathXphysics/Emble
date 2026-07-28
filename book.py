import os
import random
try:
    import chess
    import chess.polyglot
    BOOK_AVAILABLE = True
except ImportError:
    BOOK_AVAILABLE = False
from board import QUEEN, ROOK, BISHOP, KNIGHT, NONE_PIECE
from moves import generate_legal_moves

_BOOKS_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "books")

# Reihenfolge = Prioritaet. Erstes Buch mit einem Eintrag fuer die Stellung gewinnt.
BOOK_PATHS = [
    os.path.join(_BOOKS_DIR, "Cerebellum3Merge.bin"),
    os.path.join(_BOOKS_DIR, "Perfect2023.bin"),
    os.path.join(_BOOKS_DIR, "Human.bin"),
    os.path.join(_BOOKS_DIR, "Titans.bin"),
    os.path.join(_BOOKS_DIR, "gm2001.bin"),
    os.path.join(_BOOKS_DIR, "komodo.bin"),
    os.path.join(_BOOKS_DIR, "rodent.bin"),
]

MAX_BOOK_PLY = 50

_readers = None


def _get_readers():
    global _readers
    if _readers is not None:
        return _readers
    _readers = []
    for path in BOOK_PATHS:
        if os.path.exists(path):
            try:
                _readers.append(chess.polyglot.open_reader(path))
            except Exception:
                pass
    return _readers


def _uci_to_square(uci_str):
    col = ord(uci_str[0]) - ord('a')
    row = int(uci_str[1]) - 1
    return row * 8 + col


def _find_matching_move(board, uci_str):
    from_sq = _uci_to_square(uci_str[0:2])
    to_sq = _uci_to_square(uci_str[2:4])
    promo_char = {"q": QUEEN, "r": ROOK, "b": BISHOP, "n": KNIGHT}
    promotion = promo_char.get(uci_str[4]) if len(uci_str) == 5 else None
    promo_val = promotion if promotion is not None else NONE_PIECE

    for move in generate_legal_moves(board):
        if (move & 0x3F) == from_sq and ((move >> 6) & 0x3F) == to_sq and ((move >> 19) & 0x7) == promo_val:
            return move
    return None


def get_book_move(board, ply_count, weighted=False):
    if ply_count >= MAX_BOOK_PLY:
        return None

    readers = _get_readers()
    if not readers:
        return None

    try:
        cb_board = chess.Board(board.to_fen())
    except ValueError:
        return None

    for reader in readers:
        entries = list(reader.find_all(cb_board))
        if not entries:
            continue

        if weighted:
            weights = [e.weight for e in entries]
            chosen = random.choices(entries, weights=weights, k=1)[0]
        else:
            chosen = max(entries, key=lambda e: e.weight)

        move = _find_matching_move(board, chosen.move.uci())
        if move is not None:
            return move

    return None