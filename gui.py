import os
import sys

import pygame

from board import Board, WHITE, BLACK, PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING, NONE_PIECE, sq
from moves import generate_legal_moves, make_move, is_in_check
from engine import choose_move_iterative
from book import get_book_move

# ---------------------------------------------------------------------------
# Konfiguration
# ---------------------------------------------------------------------------

ENGINE_COLOR = BLACK        # Engine spielt Schwarz, du spielst Weiss
ENGINE_TIME_LIMIT = 21    # Denkzeit der Engine pro Zug in Sekunden

SQUARE_SIZE = 80
BOARD_OFFSET = 30
WINDOW_SIZE = SQUARE_SIZE * 8 + BOARD_OFFSET * 2

BACKGROUND = (235, 235, 235)
LIGHT = (222, 185, 126)
DARK = (110, 63, 24)
COLOR_LAST_MOVE = (255, 215, 0)
COLOR_SELECTED = (60, 180, 60)
COLOR_LEGAL_TARGET = (60, 120, 220)
COLOR_HINT = (120, 120, 120)
COLOR_ANALYSIS = (30, 90, 200)
COLOR_COPY_OK = (30, 140, 30)

LETTERS = ["a", "b", "c", "d", "e", "f", "g", "h"]

PIECE_SYMBOLS = {
    (WHITE, PAWN): "\u2659", (WHITE, KNIGHT): "\u2658", (WHITE, BISHOP): "\u2657",
    (WHITE, ROOK): "\u2656", (WHITE, QUEEN): "\u2655", (WHITE, KING): "\u2654",
    (BLACK, PAWN): "\u265F", (BLACK, KNIGHT): "\u265E", (BLACK, BISHOP): "\u265D",
    (BLACK, ROOK): "\u265C", (BLACK, QUEEN): "\u265B", (BLACK, KING): "\u265A",
}

PROMOTION_OPTIONS = [QUEEN, ROOK, BISHOP, KNIGHT]
PROMOTION_LABELS = ["Dame", "Turm", "Laeufer", "Springer"]
PIECE_TO_PROMO_CHAR = {QUEEN: "q", ROOK: "r", BISHOP: "b", KNIGHT: "n"}


# ---------------------------------------------------------------------------
# Engine direkt im selben Prozess ansteuern (kein Subprocess, kein UCI-Text-
# protokoll noetig -- dadurch als EINE einzige .exe buendelbar).
# ---------------------------------------------------------------------------

def color_to_str(color_const):
    return "white" if color_const == WHITE else "black"


def engine_choose_move(board):
    ply_count = len(board.history)
    book_move = get_book_move(board, ply_count)
    if book_move is not None:
        return book_move
    return choose_move_iterative(board, color_to_str(board.side_to_move), time_limit=ENGINE_TIME_LIMIT)


# ---------------------------------------------------------------------------
# UCI-Notation (nur noch fuer den PGN-Export gebraucht)
# ---------------------------------------------------------------------------

def square_to_uci(square):
    file_char = chr(ord('a') + (square & 7))
    rank_char = str((square >> 3) + 1)
    return file_char + rank_char


def uci_of_move(move):
    from_sq = move & 0x3F
    to_sq = (move >> 6) & 0x3F
    promo = (move >> 19) & 0x7
    result = square_to_uci(from_sq) + square_to_uci(to_sq)
    if promo in PIECE_TO_PROMO_CHAR:
        result += PIECE_TO_PROMO_CHAR[promo]
    return result


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


def board_at_ply(move_ints_history, ply):
    """Baut die Stellung nach den ersten `ply` Zuegen aus move_ints_history neu auf."""
    b = Board()
    for m in move_ints_history[:ply]:
        make_move(b, m)
    return b


# ---------------------------------------------------------------------------
# PGN-Export + Zwischenablage
# ---------------------------------------------------------------------------

def build_pgn(move_ints_history):
    """Erzeugt einen PGN-String ueber python-chess. None, falls chess nicht installiert ist."""
    try:
        import chess
        import chess.pgn
    except ImportError:
        return None

    game = chess.pgn.Game()
    game.headers["Event"] = "Emblium Partie"
    node = game
    cb_board = chess.Board()
    for move_int in move_ints_history:
        uci_str = uci_of_move(move_int)
        move = cb_board.parse_uci(uci_str)
        node = node.add_variation(move)
        cb_board.push(move)
    return str(game)


def copy_to_clipboard(text):
    try:
        import tkinter
        root = tkinter.Tk()
        root.withdraw()
        root.clipboard_clear()
        root.clipboard_append(text)
        root.update()
        root.destroy()
        return True
    except Exception:
        return False


# ---------------------------------------------------------------------------
# Zeichnen
# ---------------------------------------------------------------------------

def draw_board(window, board, font_piece, font_label, selected_sq, legal_targets,
               last_move, status_text, top_hint_text, top_hint_color, copy_message):
    window.fill(BACKGROUND)

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

    if top_hint_text:
        text = font_label.render(top_hint_text, True, top_hint_color)
        window.blit(text, (BOARD_OFFSET, 5))

    if copy_message:
        text = font_label.render(copy_message, True, COLOR_COPY_OK)
        window.blit(text, (BOARD_OFFSET, WINDOW_SIZE - 40))

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
    font_label = pygame.font.SysFont("segoeuisymbol", 16)

    live_board = Board()
    move_ints_history = []
    view_ply = 0

    selected_sq = None
    legal_targets = []
    status_text = None
    game_over = False

    copy_message = None
    copy_message_until = 0

    clock = pygame.time.Clock()

    while True:
        is_live = (view_ply == len(move_ints_history))
        display_board = live_board if is_live else board_at_ply(move_ints_history, view_ply)
        last_move_display = move_ints_history[view_ply - 1] if view_ply > 0 else None

        if copy_message and pygame.time.get_ticks() > copy_message_until:
            copy_message = None

        if is_live:
            top_hint_text = "<- -> Zuege ansehen  |  C: PGN kopieren"
            top_hint_color = COLOR_HINT
        else:
            top_hint_text = f"Analyse: Zug {view_ply}/{len(move_ints_history)}  |  -> zum Live-Stand"
            top_hint_color = COLOR_ANALYSIS

        draw_board(window, display_board, font_piece, font_label, selected_sq, legal_targets,
                   last_move_display, status_text, top_hint_text, top_hint_color, copy_message)
        pygame.display.flip()
        clock.tick(60)

        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                pygame.quit()
                sys.exit()

            if event.type == pygame.KEYDOWN:
                if event.key == pygame.K_LEFT:
                    view_ply = max(0, view_ply - 1)
                    selected_sq = None
                    legal_targets = []
                elif event.key == pygame.K_RIGHT:
                    view_ply = min(len(move_ints_history), view_ply + 1)
                    selected_sq = None
                    legal_targets = []
                elif event.key == pygame.K_c:
                    pgn_text = build_pgn(move_ints_history)
                    if pgn_text is None:
                        if move_ints_history:
                            pgn_text = "startpos moves " + " ".join(uci_of_move(m) for m in move_ints_history)
                        else:
                            pgn_text = ""
                    if pgn_text and copy_to_clipboard(pgn_text):
                        copy_message = "In Zwischenablage kopiert"
                    else:
                        copy_message = "Kopieren fehlgeschlagen"
                    copy_message_until = pygame.time.get_ticks() + 2000

            if event.type == pygame.MOUSEBUTTONDOWN and not game_over and is_live:
                clicked_sq = square_from_pixel(event.pos)
                if clicked_sq is None:
                    continue

                if live_board.side_to_move == ENGINE_COLOR:
                    continue  # Engine ist am Zug, Klicks werden ignoriert

                if selected_sq is None:
                    piece_info = live_board.piece_at(clicked_sq)
                    if piece_info is not None and piece_info[0] == live_board.side_to_move:
                        selected_sq = clicked_sq
                        legal_targets = [(m >> 6) & 0x3F for m in legal_moves_from_square(live_board, clicked_sq)]
                else:
                    if clicked_sq == selected_sq:
                        selected_sq = None
                        legal_targets = []
                        continue

                    promotion = None
                    if needs_promotion_choice(live_board, selected_sq, clicked_sq):
                        promotion = ask_promotion(window, font_label)

                    move = find_move(live_board, selected_sq, clicked_sq, promotion)
                    if move is not None:
                        make_move(live_board, move)
                        move_ints_history.append(move)
                        view_ply = len(move_ints_history)
                        selected_sq = None
                        legal_targets = []

                        status = game_status(live_board)
                        if status == "checkmate":
                            winner = "Weiss" if live_board.side_to_move == BLACK else "Schwarz"
                            status_text = f"Schachmatt - {winner} gewinnt"
                            game_over = True
                        elif status == "stalemate":
                            status_text = "Patt - Unentschieden"
                            game_over = True
                    else:
                        piece_info = live_board.piece_at(clicked_sq)
                        if piece_info is not None and piece_info[0] == live_board.side_to_move:
                            selected_sq = clicked_sq
                            legal_targets = [(m >> 6) & 0x3F for m in legal_moves_from_square(live_board, clicked_sq)]
                        else:
                            selected_sq = None
                            legal_targets = []

        if not game_over and is_live and live_board.side_to_move == ENGINE_COLOR:
            status_text = None
            draw_board(window, live_board, font_piece, font_label, selected_sq, legal_targets,
                       last_move_display, "Engine denkt...", top_hint_text, top_hint_color, copy_message)
            pygame.display.flip()

            move = engine_choose_move(live_board)

            if move is None:
                status = game_status(live_board)
                if status == "checkmate":
                    winner = "Weiss" if live_board.side_to_move == BLACK else "Schwarz"
                    status_text = f"Schachmatt - {winner} gewinnt"
                elif status == "stalemate":
                    status_text = "Patt - Unentschieden"
                game_over = True
            else:
                make_move(live_board, move)
                move_ints_history.append(move)
                view_ply = len(move_ints_history)

                status = game_status(live_board)
                if status == "checkmate":
                    winner = "Weiss" if live_board.side_to_move == BLACK else "Schwarz"
                    status_text = f"Schachmatt - {winner} gewinnt"
                    game_over = True
                elif status == "stalemate":
                    status_text = "Patt - Unentschieden"
                    game_over = True


if __name__ == "__main__":
    main()