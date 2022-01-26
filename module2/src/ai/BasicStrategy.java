package src.ai;

import src.game.Board;
import src.game.GameBoard;
import src.game.Mark;

public class BasicStrategy implements Strategy{ //NEEDS TO BE TESTED
    //A strategy that selects winning moves, and prevents winning moves of the opponent
    //Is still easy to win against, because you often have multiple winning moves at the same time
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
                            if (m/4 == 1) { //rotate to the left if m > 3
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
        int index;
        if (move != null) {
            index = move[0]; //we have found a field that we need to place a piece on to prevent the opponent from winning
        } else {
            index = random.determineMove(board, mark)[0]; //there is no winning move for the opponent, so we select a random field
        }
        //we also don't want to create a winning move for our opponent by rotating a board
        //so next, we want to determine a rotation so our opponent cannot win
        for (int j = 0; j < 8; j++) { //see if the opponent can win if we do this rotation
            GameBoard copy = (GameBoard) board.deepCopy();
            copy.setField(index, mark);
            if (j/4 == 1) { //rotate to the left if j > 3
                copy.rotateLeft(j%4);
            } else { //else, rotate to the right
                copy.rotateRight(j);
            }
            if (determineWinningMove(board, mark.other()) == null) {//Conclusion: the opponent cannot win if we do this rotation
                return new int[]{index, j};
            }
        } //if this for loop finishes without returning anything, we have lost

        //if there isn't a way to prevent the opponent from winning, just return a random move
        return random.determineMove(board, mark);
    }
}
