from tkinter import *
import zobrist

white_short = True
white_long = True
black_short = True
black_long = True
white_short_execute = False
white_long_execute = False
black_short_execute = False
black_long_execute = False
last_move = None
current_hash = None
position_history = {}
halfmove_clock = 0

direction_straight = [
    (+1, +0),
    (-1, +0),
    (+0, +1),
    (+0, -1)
]
direction_diagonal = [
    (+1, +1),
    (+1, -1),
    (-1, +1),
    (-1, -1)
]
direction_Knight = [
    (+2, +1),
    (+2, -1),
    (-2, +1),
    (-2, -1),
    (+1, +2),
    (+1, -2),
    (-1, +2),
    (-1, -2)
]
direction_King = [
    (+1, +1),
    (+1, -1),
    (+1, 0),
    (-1, +1),
    (-1, -1),
    (-1, 0),
    (0, +1),
    (0, -1),
]

def knight_moves(board, square):
    square_knight = []
    for jump in direction_Knight:
        new_row = square[0] + jump[0]
        new_collum = square[1] + jump[1]

        if new_row < 0 or new_row > 7 or new_collum < 0 or new_collum > 7:
            continue
        if board[square[0]][square[1]] == "-S":
            if "-" in board[new_row][new_collum]:
                continue
        if board[square[0]][square[1]] == "S":
            if ("-" not in board[new_row][new_collum] and not board[new_row][new_collum] == "0"):
                continue

        square_knight.append((new_row, new_collum))
    return square_knight

def rook_moves(board, square):
    square_rook = []
    for direction in direction_straight:
        now_row = square[0]
        now_collum = square[1]
        rookPossible = True
        while rookPossible == True:
            new_row = now_row + direction[0]
            new_collum = now_collum + direction[1]

            if new_row < 0 or new_row > 7 or new_collum < 0 or new_collum > 7:
                rookPossible = False
                continue
            if board[square[0]][square[1]] == "-T" or board[square[0]][square[1]] == "-D":
                if "-" in board[new_row][new_collum]:
                    rookPossible = False
                    continue
            if board[square[0]][square[1]] == "T" or board[square[0]][square[1]] == "D":
                if ("-" not in board[new_row][new_collum] and not board[new_row][new_collum] == "0"):
                    rookPossible = False
                    continue
            if board[square[0]][square[1]] == "-T" or board[square[0]][square[1]] == "-D":
                if ("-" not in board[new_row][new_collum] and not board[new_row][new_collum] == "0"):
                    square_rook.append((new_row, new_collum))
                    rookPossible = False
                    continue
            if board[square[0]][square[1]] == "T" or board[square[0]][square[1]] == "D":
                if "-" in board[new_row][new_collum]:
                    square_rook.append((new_row, new_collum))
                    rookPossible = False
                    continue
            if rookPossible == True:
                square_rook.append((new_row, new_collum))

            now_row = new_row
            now_collum = new_collum

    return square_rook


def bishop_moves(board, square):
    square_bishop = []
    for direction in direction_diagonal:
        now_row = square[0]
        now_collum = square[1]
        bishopPossible = True
        while bishopPossible == True:
            new_row = now_row + direction[0]
            new_collum = now_collum + direction[1]
            if new_row < 0 or new_row > 7 or new_collum < 0 or new_collum > 7:
                bishopPossible = False
                continue
            if board[square[0]][square[1]] == "-L" or board[square[0]][square[1]] == "-D":
                if "-" in board[new_row][new_collum]:
                    bishopPossible = False
                    continue
            if board[square[0]][square[1]] == "L" or board[square[0]][square[1]] =="D":
                if ("-" not in board[new_row][new_collum] and not board[new_row][new_collum] == "0"):
                    bishopPossible = False
                    continue
            if board[square[0]][square[1]] == "-L" or board[square[0]][square[1]] == "-D":
                if ("-" not in board[new_row][new_collum] and not board[new_row][new_collum] == "0"):
                    square_bishop.append((new_row, new_collum))
                    bishopPossible = False
                    continue
            if board[square[0]][square[1]] == "L" or board[square[0]][square[1]] =="D":
                if "-" in board[new_row][new_collum]:
                    square_bishop.append((new_row, new_collum))
                    bishopPossible = False
                    continue
            if bishopPossible == True:
                square_bishop.append((new_row, new_collum))

            now_row = new_row
            now_collum = new_collum

    return square_bishop


def queen_moves(board, square):
    rook_ergebnis = rook_moves(board, square)
    bishop_ergebnis = bishop_moves(board, square)
    square_Queen = rook_ergebnis + bishop_ergebnis
    return square_Queen

def find_King(board):
    king = []
    for index, row in enumerate(board):
            for collum in range(8):
                if board[index][collum] == "K" or board[index][collum] == "-K":
                    king.append((index, collum))
    return king

def king_moves(board, square):
    square_king = []
    for Zug in direction_King:
        new_row = square[0] + Zug[0]
        new_collum = square[1] + Zug[1]

        if new_row < 0 or new_row > 7 or new_collum < 0 or new_collum > 7:
            continue
        if board[square[0]][square[1]] == "K":
            if ("-" not in board[new_row][new_collum] and not board[new_row][new_collum] == "0"):
                continue

        if board[square[0]][square[1]] == "-K":
            if "-" in board[new_row][new_collum]:
                continue


        square_king.append((new_row, new_collum))
    if board[square[0]][square[1]] == "K":
        if white_short == True:
            if board[7][5] == "0" and board[7][6] == "0":
                square_king.append((7,6))
        if white_long == True:
            if board[7][1] == "0" and board[7][2] == "0" and board[7][3] == "0":
                square_king.append((7,2))

    if board[square[0]][square[1]] == "-K":
        if black_short == True:
            if board[0][5] == "0" and board[0][6] == "0":
                square_king.append((0,6))
        if black_long == True:
            if board[0][1] == "0" and board[0][2] == "0" and board[0][3] == "0":
                square_king.append((0,2))

    return  square_king

def pawn_moves(board, square, color, last_move):
    square_pawn = []
    movespawnwhite = [
        (-1,+0)
    ]
    movespawnblack = [
        (+1,+0),
    ]
    if color == "white":
        for Zug in movespawnwhite:
            if board[square[0]][square[1]] == "B":
                new_row = square[0] + Zug[0]
                new_collum = square[1] + Zug[1]
                if board[new_row][new_collum] == "0":
                    square_pawn.append((new_row, new_collum))
                if square[0] - 1 >= 0 and square[1] + 1 <= 7 and "-" in board[square[0] - 1][square[1] + 1]:
                    new_row = square[0] - 1
                    new_collum = square[1] + 1
                    if new_collum <= 7:
                        square_pawn.append((new_row, new_collum))
                if square[0] - 1 >= 0 and square[1] - 1 >= 0 and "-" in board[square[0] - 1][square[1] - 1]:
                    new_row = square[0] - 1
                    new_collum = square[1] - 1
                    if new_collum >= 0:
                        square_pawn.append((new_row, new_collum))
                if square[0] == 6:
                    if board[square[0] - 1][square[1]] == "0" and board[square[0] - 2][square[1]] == "0":
                        new_row = square[0] - 2
                        new_collum = square[1] + Zug[1]
                        square_pawn.append((new_row, new_collum))
                if last_move is not None and last_move[2] == "-B" and square[0] == 3:
                    if last_move[0][0] == 1 and last_move[1][0] == 3:
                        collum_collum = last_move[1][1]
                        if collum_collum == square[1] + 1:
                            square_pawn.append((2, collum_collum))
                        if collum_collum == square[1] - 1:
                            square_pawn.append((2, collum_collum))

    if color == "black":
        for Zug in movespawnblack:
            if board[square[0]][square[1]] == "-B":

                new_row = square[0] + Zug[0]
                new_col = square[1] + Zug[1]
                if 0 <= new_row <= 7 and 0 <= new_col <= 7:
                    if board[new_row][new_col] == "0":
                        square_pawn.append((new_row, new_col))

                if square[0] + 1 <= 7 and square[1] + 1 <= 7:
                    if "-" not in board[square[0] + 1][square[1] + 1] and board[square[0] + 1][square[1] + 1] != "0":
                        square_pawn.append((square[0] + 1, square[1] + 1))

                if square[0] + 1 <= 7 and square[1] - 1 >= 0:
                    if "-" not in board[square[0] + 1][square[1] - 1] and board[square[0] + 1][square[1] - 1] != "0":
                        square_pawn.append((square[0] + 1, square[1] - 1))

                if square[0] == 1:
                    if board[square[0] + 1][square[1]] == "0" and board[square[0] + 2][square[1]] == "0":
                        square_pawn.append((square[0] + 2, square[1]))

                if last_move is not None and last_move[2] == "B" and square[0] == 4:
                    if last_move[0][0] == 6 and last_move[1][0] == 4:
                        col_last = last_move[1][1]
                        if col_last == square[1] + 1:
                            square_pawn.append((5, col_last))
                        if col_last == square[1] - 1:
                            square_pawn.append((5, col_last))

    return square_pawn

def make_move(board,start_square,end_square, promotion_piece = None):
    global white_short, white_long, black_short, black_long
    global white_short_execute, white_long_execute
    global black_short_execute, black_long_execute
    global last_move
    global current_hash, position_history, halfmove_clock

    white_short_execute = False
    white_long_execute = False
    black_short_execute = False
    black_long_execute = False

    square = []
    erfolg = False
    if "-" in board[start_square[0]][start_square[1]]:
        color = "black"
    else:
        color = "white"
    if board[start_square[0]][start_square[1]] == "B":
        square = pawn_moves(board,start_square, "white",last_move)
        color = "white"
    if board[start_square[0]][start_square[1]] == "-B":
        square = pawn_moves(board, start_square, "black", last_move)
        color = "black"
    if "S" in board[start_square[0]][start_square[1]]:
        square = knight_moves(board,start_square)
    if "T" in board[start_square[0]][start_square[1]]:
        square = rook_moves(board, start_square)
    if "L" in board[start_square[0]][start_square[1]]:
        square = bishop_moves(board, start_square)
    if "D" in board[start_square[0]][start_square[1]]:
        square = queen_moves(board,start_square)
    if "K" in board[start_square[0]][start_square[1]]:
        if start_square == (7, 4) and end_square == (7, 6):
            white_short_execute = True
        if start_square == (7, 4) and end_square == (7, 2):
            white_long_execute = True
        if start_square == (0, 4) and end_square == (0, 6):
            black_short_execute = True
        if start_square == (0, 4) and end_square == (0, 2):
            black_long_execute = True
        square = king_moves(board, start_square)
    if end_square in square:
        piece = board[start_square[0]][start_square[1]]
        target_inhalt = board[end_square[0]][end_square[1]]
        if target_inhalt == "T":
            if end_square == (7, 0):
                white_long = False
            if end_square == (7, 7):
                white_short = False

        if target_inhalt == "-T":
            if end_square == (0, 0):
                black_long = False
            if end_square == (0, 7):
                black_short = False
        board[end_square[0]][end_square[1]] = board[start_square[0]][start_square[1]]
        board[start_square[0]][start_square[1]] = "0"
        verursacht_schach = in_check(board,color)
        if verursacht_schach == True:
            board[start_square[0]][start_square[1]] = piece
            board[end_square[0]][end_square[1]] = target_inhalt
        else:
            rochade_blockiert = False
            if white_short_execute == True:
                if rochade_schach(board, (7,4), "white") == True or rochade_schach(board, (7,5), "white") == True or rochade_schach(board, (7,6), "white") == True:
                    white_short_execute = False
                    board[start_square[0]][start_square[1]] = piece
                    board[end_square[0]][end_square[1]] = target_inhalt
                    rochade_blockiert = True
                    erfolg = False
                if white_short_execute == True:
                    board[7][5] ="T"
                    board[7][7] ="0"
                    white_short_execute = False
                    white_long_execute = False
                    white_short = False
                    white_long = False
            if white_long_execute == True:
                if rochade_schach(board, (7, 4), "white") == True or rochade_schach(board, (7, 3),"white") == True or rochade_schach(board, (7, 2), "white") == True:
                    white_long_execute = False
                    board[start_square[0]][start_square[1]] = piece
                    board[end_square[0]][end_square[1]] = target_inhalt
                    rochade_blockiert = True
                    erfolg = False
                if white_long_execute == True:
                    board[7][3] ="T"
                    board[7][0] ="0"
                    white_long_execute = False
                    white_short_execute = False
                    white_long = False
                    white_short = False
            if black_short_execute == True:
                if rochade_schach(board, (0, 4), "black") == True or rochade_schach(board, (0, 5),"black") == True or rochade_schach(board, (0, 6), "black") == True:
                    black_short_execute = False
                    board[start_square[0]][start_square[1]] = piece
                    board[end_square[0]][end_square[1]] = target_inhalt
                    rochade_blockiert = True
                    erfolg = False
                if black_short_execute == True:
                    board[0][5] ="-T"
                    board[0][7] ="0"
                    black_short_execute = False
                    black_long_execute = False
                    black_short = False
                    black_long = False
            if black_long_execute == True:
                if rochade_schach(board,(0,4),"black") == True or rochade_schach(board, (0, 3),"black") == True or rochade_schach(board, (0, 2),"black") == True:
                    black_long_execute = False
                    board[start_square[0]][start_square[1]] = piece
                    board[end_square[0]][end_square[1]] = target_inhalt
                    rochade_blockiert = True
                    erfolg = False
                if black_long_execute == True:
                    board[0][3] ="-T"
                    board[0][0] ="0"
                    black_long_execute = False
                    black_short_execute = False
                    black_long = False
                    black_short = False
            if rochade_blockiert == False:
                erfolg = True
            if erfolg == True:
                if board[0][end_square[1]] == "B":
                    if promotion_piece is None:
                        inputPromotion = "Queen"
                    else:
                        inputPromotion = promotion_piece
                    if inputPromotion == "Queen":
                        board[0][end_square[1]] = "D"
                    if inputPromotion == "rook":
                        board[0][end_square[1]] = "T"
                    if inputPromotion == "knight":
                        board[0][end_square[1]] = "S"
                    if inputPromotion == "bishop":
                        board[0][end_square[1]] = "L"
                if board[7][end_square[1]] == "-B":
                    board[7][end_square[1]] = "-D"
                if piece == "B" and target_inhalt == "0" and start_square[1] != end_square[1]:
                    board[start_square[0]][end_square[1]] = "0"
                if piece == "-B" and target_inhalt == "0" and start_square[1] != end_square[1]:
                    board[start_square[0]][end_square[1]] = "0"

                if "K" in piece:
                    if color == "white":
                        white_short = False
                        white_long = False
                    if color == "black":
                        black_short = False
                        black_long = False
                if start_square == (7, 0):
                    white_long = False
                if start_square == (7, 7):
                    white_short = False
                if start_square == (0, 0):
                    black_long = False
                if start_square == (0, 7):
                    black_short = False
                next_color = "black" if color == "white" else "white"
                if piece in ("B", "-B") or target_inhalt != "0":
                    halfmove_clock = 0
                else:
                    halfmove_clock += 1
                current_hash = zobrist.compute_hash(board, next_color)
                position_history[current_hash] = position_history.get(current_hash, 0) + 1
                last_move = (start_square, end_square, piece)
    return erfolg

def in_check(board,color):
    king_attacked = False
    king = find_King(board)
    if len(king) < 2:
        return False
    Position = None
    for k in king:
        if color == "white" and "-" not in board[k[0]][k[1]]:
            Position = k
        if color == "black" and "-" in board[k[0]][k[1]]:
            Position = k
    if Position is None:
        return False
    square = Position
    for direction in direction_straight:
        now_row = square[0]
        now_collum = square[1]
        piece_found = False
        while not piece_found:
            new_row = now_row + direction[0]
            new_collum = now_collum + direction[1]
            if new_row < 0 or new_row > 7 or new_collum < 0 or new_collum > 7:
                piece_found = True
                continue
            if color == "white":
                if board[new_row][new_collum] == "-T" or board[new_row][new_collum] == "-D":
                    piece_found = True
                    king_attacked = True
                if not board[new_row][new_collum] == "0":
                    piece_found = True
                    continue
                now_row = new_row
                now_collum = new_collum
            else:
                if board[new_row][new_collum] == "T" or board[new_row][new_collum] == "D":
                    piece_found = True
                    king_attacked = True
                if not board[new_row][new_collum] == "0":
                    piece_found = True
                    continue
                now_row = new_row
                now_collum = new_collum

    for direction in direction_diagonal:
        now_row = square[0]
        now_collum = square[1]
        piece_found = False
        while not piece_found:
            new_row = now_row + direction[0]
            new_collum = now_collum + direction[1]
            if new_row < 0 or new_row > 7 or new_collum < 0 or new_collum > 7:
                piece_found = True
                continue
            if color == "white":
                if board[new_row][new_collum] == "-L" or board[new_row][new_collum] == "-D":
                    piece_found = True
                    king_attacked = True
                if not board[new_row][new_collum] == "0":
                    piece_found = True
                    continue
                now_row = new_row
                now_collum = new_collum
            else:
                if board[new_row][new_collum] == "L" or board[new_row][new_collum] == "D":
                    piece_found = True
                    king_attacked = True
                if not board[new_row][new_collum] == "0":
                    piece_found = True
                    continue
                now_row = new_row
                now_collum = new_collum

    if color == "white":
        if Position[0] - 1 >= 0 and Position[1] + 1 <= 7:
            if board[Position[0] - 1][Position[1] + 1] == "-B":
                king_attacked = True
        if Position[0] - 1 >= 0 and Position[1] - 1 >= 0:
            if board[Position[0] - 1][Position[1] - 1] == "-B":
                king_attacked = True
    if color == "black":
        if Position[0] + 1 <= 7 and Position[1] + 1 <= 7:
            if board[Position[0] + 1][Position[1] + 1] == "B":
                king_attacked = True
        if Position[0] + 1 <= 7 and Position[1] - 1 >= 0:
            if board[Position[0] + 1][Position[1] - 1] == "B":
                king_attacked = True

    for direction in direction_Knight:
        new_row = square[0] + direction[0]
        new_collum = square[1] + direction[1]
        if new_row < 0 or new_row > 7 or new_collum < 0 or new_collum > 7:
            continue
        if color == "white":
            if board[new_row][new_collum] == "-S":
                king_attacked = True
        if color == "black":
            if board[new_row][new_collum] == "S":
                king_attacked = True

    for direction in direction_King:
        new_row = square[0] + direction[0]
        new_collum = square[1] + direction[1]
        if new_row < 0 or new_row > 7 or new_collum < 0 or new_collum > 7:
            continue
        if color == "white":
            if board[new_row][new_collum] == "-K":
                king_attacked = True
        if color == "black":
            if board[new_row][new_collum] == "K":
                king_attacked = True
    return king_attacked


def rochade_schach(board, square, color):
    king_attacked = False
    for direction in direction_straight:
        now_row = square[0]
        now_collum = square[1]
        piece_found = False
        while not piece_found:
            new_row = now_row + direction[0]
            new_collum = now_collum + direction[1]
            if new_row < 0 or new_row > 7 or new_collum < 0 or new_collum > 7:
                piece_found = True
                continue
            if color == "white":
                if board[new_row][new_collum] == "-T" or board[new_row][new_collum] == "-D":
                    piece_found = True
                    king_attacked = True
                if not board[new_row][new_collum] == "0":
                    piece_found = True
                    continue
                now_row = new_row
                now_collum = new_collum
            else:
                if board[new_row][new_collum] == "T" or board[new_row][new_collum] == "D":
                    piece_found = True
                    king_attacked = True
                if not board[new_row][new_collum] == "0":
                    piece_found = True
                    continue
                now_row = new_row
                now_collum = new_collum

    for direction in direction_diagonal:
        now_row = square[0]
        now_collum = square[1]
        piece_found = False
        while not piece_found:
            new_row = now_row + direction[0]
            new_collum = now_collum + direction[1]
            if new_row < 0 or new_row > 7 or new_collum < 0 or new_collum > 7:
                piece_found = True
                continue
            if color == "white":
                if board[new_row][new_collum] == "-L" or board[new_row][new_collum] == "-D":
                    piece_found = True
                    king_attacked = True
                if not board[new_row][new_collum] == "0":
                    piece_found = True
                    continue
                now_row = new_row
                now_collum = new_collum
            else:
                if board[new_row][new_collum] == "L" or board[new_row][new_collum] == "D":
                    piece_found = True
                    king_attacked = True
                if not board[new_row][new_collum] == "0":
                    piece_found = True
                    continue
                now_row = new_row
                now_collum = new_collum
    if color == "white":
        if square[0] - 1 >= 0 and square[1] + 1 <= 7:
            if board[square[0] - 1][square[1] + 1] == "-B":
                king_attacked = True
        if square[0] - 1 >= 0 and square[1] - 1 >= 0:
            if board[square[0] - 1][square[1] - 1] == "-B":
                king_attacked = True
    if color == "black":
        if square[0] + 1 <= 7 and square[1] + 1 <= 7:
            if board[square[0] + 1][square[1] + 1] == "B":
                king_attacked = True
        if square[0] + 1 <= 7 and square[1] - 1 >= 0:
            if board[square[0] + 1][square[1] - 1] == "B":
                king_attacked = True

    for direction in direction_Knight:
        new_row = square[0] + direction[0]
        new_collum = square[1] + direction[1]
        if new_row < 0 or new_row > 7 or new_collum < 0 or new_collum > 7:
            continue
        if color == "white":
            if board[new_row][new_collum] == "-S":
                king_attacked = True
        if color == "black":
            if board[new_row][new_collum] == "S":
                king_attacked = True

    return king_attacked


def promotion_auswahl():
    window_Tk = Tk()
    window_Tk.title("Chess Engine")
    window_Tk.geometry("100x100")
    global inputPromotion
    inputPromotion = None
    def promotion_Queen():
        global inputPromotion
        inputPromotion = "Queen"
        window_Tk.destroy()
    def promotion_rook():
        global inputPromotion
        inputPromotion = "rook"
        window_Tk.destroy()
    def promotion_bishop():
        global inputPromotion
        inputPromotion = "bishop"
        window_Tk.destroy()
    def promotion_knight():
        global inputPromotion
        inputPromotion = "knight"
        window_Tk.destroy()
    buttonQueen = Button(window_Tk, text="Queen",command=promotion_Queen)
    buttonQueen.grid()
    buttonrook = Button(window_Tk, text="rook",command=promotion_rook)
    buttonrook.grid()
    buttonbishop = Button(window_Tk, text="bishop", command=promotion_bishop)
    buttonbishop.grid()
    buttonknight = Button(window_Tk, text="knight", command=promotion_knight)
    buttonknight.grid()
    window_Tk.mainloop()
    return inputPromotion
