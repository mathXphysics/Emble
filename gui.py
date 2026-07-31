import atexit
import os
import subprocess
import sys

import pygame

from board import Board, WHITE, BLACK, PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING, NONE_PIECE, sq
from moves import generate_legal_moves, make_move, is_in_check

# ---------------------------------------------------------------------------
# Konfiguration
# ---------------------------------------------------------------------------

ENGINE_COLOR = BLACK        # Engine spielt Schwarz, du spielst Weiss
ENGINE_MOVETIME_MS = 21000   # Denkzeit der Engine pro Zug in Millisekunden

# Engine laeuft mit demselben Python wie die GUI (kein externer Pfad noetig,
# dadurch spaeter problemlos als eigenstaendige .exe buendelbar). Kostet
# Geschwindigkeit gegenueber PyPy, spielt aber fuer Demo-Zwecke keine Rolle.
ENGINE_EXECUTABLE = sys.executable
UCI_SCRIPT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "uci.py")

SQUARE_SIZE = 80
BOARD_OFFSET = 30
WINDOW_SIZE = SQUARE_SIZE * 8 + BOARD_OFFSET * 2

LIGHT = (222, 185, 126)
DARK = (110, 63, 24)
COLOR_LAST_MOVE = (255, 215, 0)
COLOR_SELECTED = (60, 180, 60)
COLOR_LEGAL_TARGET = (60, 120, 220)

LETTERS = ["a", "b", "c", "d", "e", "f", "g", "h"]

PIECE_SYMBOLS = {
    (WHITE, PAWN): "\u2659", (WHITE, KNIGHT): "\u2658", (WHITE, BISHOP): "\u2657",
    (WHITE, ROOK): "\u2656", (WHITE, QUEEN): "\u2655", (WHITE, KING): "\u2654",
    (BLACK, PAWN): "\u265F", (BLACK, KNIGHT): "\u265E", (BLACK, BISHOP): "\u265D",
    (BLACK, ROOK): "\u265C", (BLACK, QUEEN): "\u265B", (BLACK, KING): "\u265A",
}

PROMOTION_OPTIONS = [QUEEN, ROOK, BISHOP, KNIGHT]
PROMOTION_LABELS = ["Dame", "Turm", "Laeufer", "Springer"]
PROMO_CHAR_TO_PIECE = {"q": QUEEN, "r": ROOK, "b": BISHOP, "n": KNIGHT}
PIECE_TO_PROMO_CHAR = {QUEEN: "q", ROOK: "r", BISHOP: "b", KNIGHT: "n"}


# ---------------------------------------------------------------------------
# Engine-Prozess (PyPy) ueber UCI ansteuern -- pygame bleibt komplett in CPython
# ---------------------------------------------------------------------------

class EngineProcess:
    def __init__(self):
        self.process = subprocess.Popen(
            [ENGINE_EXECUTABLE, UCI_SCRIPT],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            text=True,
            bufsize=1,
        )
        self._send("uci")
        self._read_until("uciok")
        self._send("isready")
        self._read_until("readyok")

    def _send(self, command):
        self.process.stdin.write(command + "\n")
        self.process.stdin.flush()

    def _read_until(self, token):
        lines = []
        while True:
            line = self.process.stdout.readline()
            if line == "":
                raise RuntimeError("Engine-Prozess wurde unerwartet beendet (PyPy-Pfad korrekt?).")
            line = line.strip()
            lines.append(line)
            if line.startswith(token):
                break
        return lines

    def best_move(self, moves_uci, movetime_ms):
        position_cmd = "position startpos"
        if moves_uci:
            position_cmd += " moves " + " ".join(moves_uci)
        self._send(position_cmd)
        self._send(f"go movetime {movetime_ms}")
        for line in self._read_until("bestmove"):
            if line.startswith("bestmove"):
                parts = line.split()
                return parts[1] if len(parts) > 1 else None
        return None

    def quit(self):
        try:
            self._send("quit")
        except (BrokenPipeError, OSError):
            pass
        self.process.terminate()


# ---------------------------------------------------------------------------
# UCI-Notation <-> internes Zugformat
# ---------------------------------------------------------------------------

def square_to_uci(square):
    file_char = chr(ord('a') + (square & 7))
    rank_char = str((square >> 3) + 1)
    return file_char + rank_char


def uci_to_square(uci_str):
    file_index = ord(uci_str[0]) - ord('a')
    rank_index = int(uci_str[1]) - 1
    return sq(file_index, rank_index)


def move_to_uci(from_sq, to_sq, promotion=None):
    result = square_to_uci(from_sq) + square_to_uci(to_sq)
    if promotion is not None:
        result += PIECE_TO_PROMO_CHAR[promotion]
    return result


def parse_uci_move(uci_str):
    from_sq = uci_to_square(uci_str[0:2])
    to_sq = uci_to_square(uci_str[2:4])
    promotion = PROMO_CHAR_TO_PIECE.get(uci_str[4]) if len(uci_str) == 5 else None
    return from_sq, to_sq, promotion


# ---------------------------------------------------------------------------
# Koordinaten-Hilfsfunktionen
# ---------------------------------------------------------------------------

def square_from_pixel(pos):
    x, y = pos
    file = (x - BOARD_OFFSET) // SQUARE_SIZE
    row_from_top = (y - BOARD_OFFSET) // SQUARE_SIZE
    if not (0 <= file <= 7 and 0 <= row_from_top <= 7):
        return None
    rank = 7 - row_from_top
    return sq(file, rank)


# ---------------------------------------------------------------------------
# Zug-Hilfsfunktionen (arbeiten mit den int-encodierten Moves aus moves.py)
# ---------------------------------------------------------------------------

def legal_moves_from_square(board, from_sq):
    return [m for m in generate_legal_moves(board) if (m & 0x3F) == from_sq]


def find_move(board, from_sq, to_sq, promotion=None):
    promo_val = promotion if promotion is not None else NONE_PIECE
    for m in generate_legal_moves(board):
        if (m & 0x3F) == from_sq and ((m >> 6) & 0x3F) == to_sq and ((m >> 19) & 0x7) == promo_val:
            return m
    return None


def needs_promotion_choice(board, from_sq, to_sq):
    piece_info = board.piece_at(from_sq)
    if piece_info is None or piece_info[1] != PAWN:
        return False
    target_rank = to_sq >> 3
    return target_rank == 7 or target_rank == 0


def game_status(board):
    """Gibt 'checkmate', 'stalemate' oder None zurueck."""
    if generate_legal_moves(board):
        return None
    if is_in_check(board, board.side_to_move):
        return "checkmate"
    return "stalemate"


# ---------------------------------------------------------------------------
# Zeichnen
# ---------------------------------------------------------------------------

def draw_board(window, board, font_piece, font_label, selected_sq, legal_targets, last_move, status_text):
    for row_from_top in range(8):
        for file in range(8):
            rank = 7 - row_from_top
            square = sq(file, rank)
            color = LIGHT if (rank + file) % 2 == 0 else DARK
            x = BOARD_OFFSET + file * SQUARE_SIZE
            y = BOARD_OFFSET + row_from_top * SQUARE_SIZE
            pygame.draw.rect(window, color, (x, y, SQUARE_SIZE, SQUARE_SIZE))

            if last_move is not None and square in ((last_move & 0x3F), (last_move >> 6) & 0x3F):
                pygame.draw.rect(window, COLOR_LAST_MOVE, (x, y, SQUARE_SIZE, SQUARE_SIZE), 5)

            if selected_sq == square:
                pygame.draw.rect(window, COLOR_SELECTED, (x, y, SQUARE_SIZE, SQUARE_SIZE), 5)
            elif square in legal_targets:
                center = (x + SQUARE_SIZE // 2, y + SQUARE_SIZE // 2)
                pygame.draw.circle(window, COLOR_LEGAL_TARGET, center, 10)

            piece_info = board.piece_at(square)
            if piece_info is not None:
                p_color, p_type = piece_info
                symbol = PIECE_SYMBOLS[(p_color, p_type)]
                text = font_piece.render(symbol, True, (0, 0, 0))
                tx = x + (SQUARE_SIZE - text.get_width()) // 2
                ty = y + (SQUARE_SIZE - text.get_height()) // 2
                window.blit(text, (tx, ty))

    for i in range(8):
        text = font_label.render(LETTERS[i], True, (0, 0, 0))
        window.blit(text, (BOARD_OFFSET + i * SQUARE_SIZE + SQUARE_SIZE // 2 - 5,
                           WINDOW_SIZE - BOARD_OFFSET + 6))
    for i in range(8):
        rank_number = str(8 - i)
        text = font_label.render(rank_number, True, (0, 0, 0))
        window.blit(text, (8, BOARD_OFFSET + i * SQUARE_SIZE + SQUARE_SIZE // 2 - 10))

    if status_text:
        text = font_label.render(status_text, True, (200, 0, 0))
        window.blit(text, (BOARD_OFFSET, WINDOW_SIZE - 20))


def ask_promotion(window, font_label):
    box_w, box_h = 220, 4 * 36 + 16
    box_x = (WINDOW_SIZE - box_w) // 2
    box_y = (WINDOW_SIZE - box_h) // 2

    while True:
        pygame.draw.rect(window, (240, 240, 240), (box_x, box_y, box_w, box_h))
        pygame.draw.rect(window, (0, 0, 0), (box_x, box_y, box_w, box_h), 2)
        rects = []
        for i, label in enumerate(PROMOTION_LABELS):
            rect = pygame.Rect(box_x + 8, box_y + 8 + i * 36, box_w - 16, 30)
            pygame.draw.rect(window, (210, 210, 210), rect)
            text = font_label.render(label, True, (0, 0, 0))
            window.blit(text, (rect.x + 10, rect.y + 5))
            rects.append(rect)
        pygame.display.flip()

        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                pygame.quit()
                sys.exit()
            if event.type == pygame.MOUSEBUTTONDOWN:
                for i, rect in enumerate(rects):
                    if rect.collidepoint(event.pos):
                        return PROMOTION_OPTIONS[i]


# ---------------------------------------------------------------------------
# Hauptprogramm
# ---------------------------------------------------------------------------

def main():
    pygame.init()
    window = pygame.display.set_mode((WINDOW_SIZE, WINDOW_SIZE), pygame.RESIZABLE)
    pygame.display.set_caption("Emblium")

    font_piece = pygame.font.SysFont("segoeuisymbol", 60)
    font_label = pygame.font.SysFont("segoeuisymbol", 20)

    engine = EngineProcess()
    atexit.register(engine.quit)

    board = Board()
    move_history_uci = []
    selected_sq = None
    legal_targets = []
    last_move = None
    status_text = None
    game_over = False

    clock = pygame.time.Clock()

    while True:
        draw_board(window, board, font_piece, font_label, selected_sq, legal_targets, last_move, status_text)
        pygame.display.flip()
        clock.tick(60)

        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                pygame.quit()
                sys.exit()

            if event.type == pygame.MOUSEBUTTONDOWN and not game_over:
                clicked_sq = square_from_pixel(event.pos)
                if clicked_sq is None:
                    continue

                if board.side_to_move == ENGINE_COLOR:
                    continue  # Engine ist am Zug, Klicks werden ignoriert

                if selected_sq is None:
                    piece_info = board.piece_at(clicked_sq)
                    if piece_info is not None and piece_info[0] == board.side_to_move:
                        selected_sq = clicked_sq
                        legal_targets = [(m >> 6) & 0x3F for m in legal_moves_from_square(board, clicked_sq)]
                else:
                    if clicked_sq == selected_sq:
                        selected_sq = None
                        legal_targets = []
                        continue

                    promotion = None
                    if needs_promotion_choice(board, selected_sq, clicked_sq):
                        promotion = ask_promotion(window, font_label)

                    move = find_move(board, selected_sq, clicked_sq, promotion)
                    if move is not None:
                        make_move(board, move)
                        move_history_uci.append(move_to_uci(selected_sq, clicked_sq, promotion))
                        last_move = move
                        selected_sq = None
                        legal_targets = []

                        status = game_status(board)
                        if status == "checkmate":
                            winner = "Weiss" if board.side_to_move == BLACK else "Schwarz"
                            status_text = f"Schachmatt - {winner} gewinnt"
                            game_over = True
                        elif status == "stalemate":
                            status_text = "Patt - Unentschieden"
                            game_over = True
                    else:
                        piece_info = board.piece_at(clicked_sq)
                        if piece_info is not None and piece_info[0] == board.side_to_move:
                            selected_sq = clicked_sq
                            legal_targets = [(m >> 6) & 0x3F for m in legal_moves_from_square(board, clicked_sq)]
                        else:
                            selected_sq = None
                            legal_targets = []

        if not game_over and board.side_to_move == ENGINE_COLOR:
            status_text = "Engine denkt..."
            draw_board(window, board, font_piece, font_label, selected_sq, legal_targets, last_move, status_text)
            pygame.display.flip()

            best_uci = engine.best_move(move_history_uci, ENGINE_MOVETIME_MS)
            status_text = None

            if best_uci is None:
                status = game_status(board)
                if status == "checkmate":
                    winner = "Weiss" if board.side_to_move == BLACK else "Schwarz"
                    status_text = f"Schachmatt - {winner} gewinnt"
                elif status == "stalemate":
                    status_text = "Patt - Unentschieden"
                game_over = True
            else:
                from_sq, to_sq, promotion = parse_uci_move(best_uci)
                move = find_move(board, from_sq, to_sq, promotion)
                if move is None:
                    status_text = f"Engine-Zug ungueltig: {best_uci}"
                    game_over = True
                else:
                    make_move(board, move)
                    move_history_uci.append(best_uci)
                    last_move = move

                    status = game_status(board)
                    if status == "checkmate":
                        winner = "Weiss" if board.side_to_move == BLACK else "Schwarz"
                        status_text = f"Schachmatt - {winner} gewinnt"
                        game_over = True
                    elif status == "stalemate":
                        status_text = "Patt - Unentschieden"
                        game_over = True


if __name__ == "__main__":
    main()