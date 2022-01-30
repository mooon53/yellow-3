package src.ai;

import src.game.Board;
import src.game.GameBoard;
import src.game.Mark;

public class BasicStrategy implements Strategy {
    //A strategy that selects winning moves, and prevents winning moves of the opponent
    //Is still easy to win against, because you often have multiple winning moves at the same time
    private DumbStrategy random = new DumbStrategy();

    @Override
    public String getName() {
        return "Normal";
    }

    public int[] determineWinningMove(Board board, Mark mark) {
        for (int i = 0; board.isField(i); i++) {
            for (int j = 0; j < 8; j++) {
                GameBoard copy = (GameBoard) board.deepCopy();
                if (copy.getField(i) == Mark.EMPTY) {
                    copy.setField(i, mark);
                    if (j / 4 == 1) { //rotate to the left if j > 3
                        copy.rotateLeft(j % 4);
                    } else { //else, rotate to the right
                        copy.rotateRight(j);
                    }
                    if (copy.isWinner(mark)) {
                        return new int[]{i, j};
                    } //return if move wins
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

        //else, make sure the opponent cannot win
        for (int i = 0; board.isField(i); i++) {
            for (int j = 0; j < 8; j++) {
                GameBoard copy = (GameBoard) board.deepCopy();
                if (copy.getField(i) == Mark.EMPTY) {
                    copy.setField(i, mark);
                    if (j / 4 == 1) { //rotate to the left if j > 3
                        copy.rotateLeft(j % 4);
                    } else { //else, rotate to the right
                        copy.rotateRight(j);
                    }
                    if (determineWinningMove(copy, mark.other()) == null) {
                        return new int[]{i, j};
                    } //return if move wins
                }
            }
        }
        //if there isn't a way to prevent the opponent from winning, return a random field with rotation 3
        return new int[]{random.determineMove(board, mark)[0], 3};
    }
    //seems to work, but always return 0, 0 if opponent doesn't have a winning move
}
