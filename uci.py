import sys
from board import Board, WHITE, BLACK, QUEEN, ROOK, BISHOP, KNIGHT
from moves import make_move, generate_legal_moves
from engine import choose_move_iterative, thinking_time, tt_clear, KILLER, HISTORY, MATE_VALUE, MATE_THRESHOLD
from book import get_book_move
import engine
NONE_PIECE = 6


def uci_to_square(uci_str):
    col = ord(uci_str[0]) - ord('a')
    row = int(uci_str[1]) - 1
    return row * 8 + col


def square_to_uci(square):
    col = chr(ord('a') + square % 8)
    row = square // 8 + 1
    return f"{col}{row}"


PROMO_CHAR_TO_PIECE = {"q": QUEEN, "r": ROOK, "b": BISHOP, "n": KNIGHT}
PIECE_TO_PROMO_CHAR = {QUEEN: "q", ROOK: "r", BISHOP: "b", KNIGHT: "n"}


def _move_to_uci_string(move):
    from_sq = move & 0x3F
    to_sq = (move >> 6) & 0x3F
    promo = (move >> 19) & 0x7
    result = square_to_uci(from_sq) + square_to_uci(to_sq)
    if promo in PIECE_TO_PROMO_CHAR:
        result += PIECE_TO_PROMO_CHAR[promo]
    return result


def _format_score(score):
    if score >= MATE_THRESHOLD:
        plies = MATE_VALUE - score
        return f"mate {int((plies + 1) // 2)}"
    if score <= -MATE_THRESHOLD:
        plies = MATE_VALUE + score
        return f"mate -{int((plies + 1) // 2)}"
    return f"cp {int(round(score * 100))}"


def _print_uci_info(depth, score, nodes, elapsed_ms, move):
    print(
        f"info depth {depth} score {_format_score(score)} nodes {nodes} "
        f"time {elapsed_ms} pv {_move_to_uci_string(move)}",
        flush=True
    )


def parse_and_apply_move(board, move_str):
    from_sq = uci_to_square(move_str[0:2])
    to_sq = uci_to_square(move_str[2:4])
    promotion = PROMO_CHAR_TO_PIECE.get(move_str[4]) if len(move_str) == 5 else None
    promo_val = promotion if promotion is not None else NONE_PIECE

    for move in generate_legal_moves(board):
        if (move & 0x3F) == from_sq and ((move >> 6) & 0x3F) == to_sq and ((move >> 19) & 0x7) == promo_val:
            make_move(board, move)
            return True
    return False


def uci_loop():
    board = Board()
    color = "white"

    while True:
        command = input().strip()

        if command == "uci":
            print("id name Emble 5.02", flush=True)
            print("id author Malte Freiherr", flush=True)
            print("uciok", flush=True)

        elif command == "isready":
            print("readyok", flush=True)

        elif command == "quit":
            break

        elif command.startswith("position"):
            parts = command.split()
            tt_clear()
            for i in range(128):
                KILLER[i][0] = None
                KILLER[i][1] = None
            for i in range(64):
                for j in range(64):
                    HISTORY[i][j] = 0

            moves_index = parts.index("moves") if "moves" in parts else len(parts)

            if parts[1] == "fen":
                fen_string = " ".join(parts[2:moves_index])
                board = Board(fen=fen_string)
            else:
                board = Board()

            color = "white" if board.side_to_move == WHITE else "black"

            if "moves" in parts:
                move_strings = parts[moves_index + 1:]
                for move_str in move_strings:
                    parse_and_apply_move(board, move_str)
                    color = "black" if color == "white" else "white"

        elif command.startswith("go"):
            ply_count = len(board.history)
            book_move = get_book_move(board, ply_count)
            if book_move is not None:
                mf = book_move & 0x3F
                mt = (book_move >> 6) & 0x3F
                promo = (book_move >> 19) & 0x7
                uci_move = square_to_uci(mf) + square_to_uci(mt)
                if promo in PIECE_TO_PROMO_CHAR:
                    uci_move += PIECE_TO_PROMO_CHAR[promo]
                print(f"bestmove {uci_move}", flush=True)
            else:
                parts = command.split()
                time_limit = thinking_time
                if "movetime" in parts:
                    time_limit = int(parts[parts.index("movetime") + 1]) / 1000.0
                elif color == "white" and "wtime" in parts:
                    wtime = int(parts[parts.index("wtime") + 1])
                    time_limit = min(thinking_time, wtime / 30000.0)
                elif color == "black" and "btime" in parts:
                    btime = int(parts[parts.index("btime") + 1])
                    time_limit = min(thinking_time, btime / 30000.0)

                move = choose_move_iterative(board, color, time_limit=time_limit, info_callback=_print_uci_info)
                if move is not None:
                    mf = move & 0x3F
                    mt = (move >> 6) & 0x3F
                    promo = (move >> 19) & 0x7
                    uci_move = square_to_uci(mf) + square_to_uci(mt)
                    if promo in PIECE_TO_PROMO_CHAR:
                        uci_move += PIECE_TO_PROMO_CHAR[promo]
                    print(f"bestmove {uci_move}", flush=True)


if __name__ == "__main__":
    uci_loop()