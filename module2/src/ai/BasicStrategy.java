package src.ai;

import src.game.Board;
import src.game.GameBoard;
import src.game.Mark;

public class BasicStrategy implements Strategy{ //NEEDS TO BE TESTED
    //A strategy that selects winning moves, and prevents winning moves of the opponent
    //However this AI can still create winning moves for the opponent by rotating the wrong thing
    private DumbStrategy random = new DumbStrategy();

    @Override
    public String getName() {
        return "Normal";
    }

    public int[] determineWinningMove(Board board, Mark mark) {
        for(int i = 0; board.isField(i); i++) {
            for (int j = 0; j < 8; j++) {
                GameBoard copy = (GameBoard) board.deepCopy();
                if (copy.getField(i) == Mark.EMPTY) {
                    copy.setField(i, mark);
                    if (j/4 == 1) { //rotate to the left if j > 3
                        copy.rotateLeft(j%4);
                    } else { //else, rotate to the right
                        copy.rotateRight(j);
                    }
                    if (copy.isWinner(mark)) { return new int[]{i, j};} //return if move wins
                }
            }
        }
        return null; //if no move wins, return null
    }


    @Override
    public int[] determineMove(Board board, Mark mark) {
        //try to find a winning move first
        int[] move = determineWinningMove(board, mark);
        if (move != null) {
            return move;
        }

        //if opponent can win with a rotation (without placing a mark), prevent that
        for (int j = 0; j < 8; j++) {
            GameBoard copy = (GameBoard) board.deepCopy();
            if (j/4 == 1) { //rotate to the left if j > 3
                copy.rotateLeft(j%4);
                j -= 4; //change j so the AI prevents the winning move by rotating the same subBoard to the right
            } else { //else, rotate to the right
                copy.rotateRight(j);
                j += 4; //change j so the AI prevents the winning move by rotating the same subBoard to the left
            }
            if (copy.isWinner(mark.other())) {
                //We have a rotation, but we still need a field to place our mark on
                //For this, check if opponent can win with a different move
                for(int n = 0; board.isField(n); n++) {
                    for (int m = 0; m < 8; m++) {
                        if (m == j) {continue; } //skip the rotation that always wins the game for the opponent
                        GameBoard copy2 = (GameBoard) board.deepCopy();
                        if (copy2.getField(n) == Mark.EMPTY) {
                            copy2.setField(n, mark.other());
                            if (m/4 == 1) { //rotate to the left if j > 3
                                copy.rotateLeft(m%4);
                            } else { //else, rotate to the right
                                copy.rotateRight(m);
                            }
                            if (copy.isWinner(mark.other())) { return new int[]{n, j};} //return if move wins
                        }
                    }
                }

                //otherwise, return a random field
                int index = random.determineMove(board, mark)[0];
                return new int[]{index, j};
            }
        }


        //if opponent can win with a move, prevent that
        move = determineWinningMove(board, mark.other());
        if (move != null) {
            return move;
        }

        //if there isn't a direct way to win or prevent a win, return a random move
        return new DumbStrategy().determineMove(board, mark);
    }
}
