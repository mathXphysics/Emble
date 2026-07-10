import pygame
from board import create_board, symbols
from moves import make_move
import moves
from engine import choose_move, all_moves, all_moves_white, choose_move_iterative, thinking_time, in_check
import zobrist
import os
board = create_board()
moves.white_king_pos = (7, 4)
moves.black_king_pos = (0, 4)
moves.current_hash = zobrist.compute_hash(board, "white")
moves.position_history = {moves.current_hash: 1}
moves.piece_count = 30
moves.white_major_count = 3
moves.black_major_count = 3
pygame.init()
window = pygame.display.set_mode((700,700), pygame.RESIZABLE)
turn = "white"
light = (222,185,126)
dark = (110,63,24)
font = pygame.font.SysFont("segoeuisymbol", 60)
font_klein = font_klein = pygame.font.SysFont("segoeuisymbol", 20)
letters = ["a", "b", "c", "d", "e", "f", "g", "h"]
numbers= ["1", "2", "3", "4", "5", "6", "7", "8"]
selected = None
pygame.display.set_caption("Chess Engine")
if os.path.exists(r"C:\Users\Malte\Downloads\ChessEngine.png"):
    icon = pygame.image.load(r"C:\Users\Malte\Downloads\ChessEngine.png")
    pygame.display.set_icon(icon)
def draw_board():
    for reihe in range(8):
        for spalte in range(8):
            if (reihe + spalte) % 2 == 0:
                color = light
            else:
                color = dark
            x = spalte * 80 + 30
            y = reihe * 80 + 30
            pygame.draw.rect(window,color,(x,y,80,80))
            if moves.last_move is not None:
                if (reihe, spalte) == moves.last_move[0] or (reihe, spalte) == moves.last_move[1]:
                    pygame.draw.rect(window, (255, 255, 0), (x, y, 80, 80), 5)
            feld = board[reihe][spalte]
            symbol = symbols[feld]
            if feld !="0":
                text = font.render(symbol, True, (0, 0, 0))
                x = x + (80 - text.get_width()) // 2 + 7
                y = y + (80 - text.get_height()) // 2
                window.blit(text, (x, y))
    for i in range(8):
        x = i * 80 + 35 + 60
        y = 640
        text = font_klein.render(letters[i], True, (0, 0, 0))
        window.blit(text, (x, y))
    for i in range(8):
        x = 30
        y =  i * 80 + 30
        number = 8-i
        text = font_klein.render(numbers[number -1], True, (0, 0, 0))
        window.blit(text, (x, y))

while True:
    draw_board()
    pygame.display.flip()
    for event in pygame.event.get():
        if event.type == pygame.QUIT:
            pygame.quit()
            exit()
        if event.type == pygame.MOUSEBUTTONDOWN:
            event.pos
            square_row = (event.pos[1]-30) // 80
            square_col = (event.pos[0]-30) // 80
            if 0 <= square_row <= 7 and 0 <= square_col <= 7:
                if selected == None:
                    start_square = (square_row, square_col)
                    if turn == "white":
                        if "-" not in board[square_row][square_col] and not board[square_row][square_col] == "0":
                            selected = start_square
                    if turn == "black":
                        if "-" in board[square_row][square_col] and not board[square_row][square_col] == "0":
                            selected = start_square
                elif selected != None:
                    end_square = (square_row, square_col)
                    selected = None
                    promotion_needed = (
                            (turn == "white" and start_square[0] == 1 and end_square[0] == 0
                             and board[start_square[0]][start_square[1]] == "B")
                            or
                            (turn == "black" and start_square[0] == 6 and end_square[0] == 7
                             and board[start_square[0]][start_square[1]] == "-B")
                    )
                    chosen_promo = moves.promotion_auswahl() if promotion_needed else None
                    erfolg = make_move(board, start_square, end_square, promotion_piece=chosen_promo)
                    if erfolg == True:
                        erfolg = False
                        if turn == "white":
                            turn = "black"
                            answer_moves = all_moves(board)
                            schach = in_check(board, "black")
                            if answer_moves == [] and schach == True:
                                print("Checkmate")
                                print("Weiß hat gewonnen")
                                pygame.quit()
                                exit()
                            elif answer_moves == [] and schach == False:
                                print("Patt")
                                print("Unentschieden")
                                pygame.quit()
                                exit()
                        elif turn == "black":
                            turn = "white"
                            answer_moves = all_moves_white(board)
                            schach = in_check(board, "white")
                            if answer_moves == [] and schach == True:
                                print("Checkmate")
                                print("Schwarz hat gewonnen")
                                pygame.quit()
                                exit()
                            elif answer_moves == [] and schach == False:
                                print("Patt")
                                print("Unentschieden")
                                pygame.quit()
                                exit()
                        if turn == "black":
                            draw_board()
                            pygame.display.flip()
                            engine_move = choose_move_iterative(board, "black", max_depth=99, time_limit=thinking_time)
                            if engine_move is not None:
                                make_move(board, engine_move[0], engine_move[1], promotion_piece=engine_move[2])
                                turn = "white"
                                answer_moves = all_moves_white(board)
                                schach = in_check(board, "white")
                                if answer_moves == [] and schach == True:
                                    print("Checkmate")
                                    print("Schwarz hat gewonnen")
                                    pygame.quit()
                                    exit()
                                elif answer_moves == [] and schach == False:
                                    print("Patt")
                                    print("Unentschieden")
                                    pygame.quit()
                                    exit()
