package src.ai;

import src.game.Board;
import src.game.GameBoard;
import src.game.Mark;

/**
 * A strategy that prevents the opponent from winning by blocking a guaranteed win for the opponent in 2 moves
 * Can also see win opportunities 2 moves ahead
 * Not very easy to beat
 */
public class SmartStrategy implements Strategy {

    private DumbStrategy random = new DumbStrategy();
    private BasicStrategy basic = new BasicStrategy();

    /**
     * The name (difficulty) of the strategy
     * @return the name of the strategy
     */
    @Override
    public String getName() {
        return "Hard";
    }

    /**
     * Tries to find a guaranteed win (in 2 moves or fewer).
     * Checks for every move if the selected mark can win
     * The opponent plays the move according to BasicStrategy
     * If we still have a winning move after that, we have a guaranteed win
     * @param board current board state
     * @param mark the mark to determine a winning move of
     * @return the winning move, or null if no such move exists
     */
    public int[] determineWinningMove(Board board, Mark mark) {
        //see if we can win immediately
        int[] move = basic.determineWinningMove(board, mark);
        if (move != null) {
            return move;
        }

        //see if we can find a guaranteed win (in 2 moves)
        for (int i = 0; board.isField(i); i++) {
            for (int j = 0; j < 8; j++) {
                GameBoard copy = (GameBoard) board.deepCopy();
                if (copy.getField(i) == Mark.EMPTY) {
                    copy.setField(i, mark);
                    if (j % 2 == 0) {
                        copy.rotateLeft(j / 2);
                    } else {
                        copy.rotateRight(j / 2);
                    }
                    //this prevents us from winning, if it's possible
                    int[] basicMove = basic.determineMove(copy, mark.other());
                    copy.setField(basicMove[0], mark.other());
                    if (basicMove[1] % 2 == 0) {
                        copy.rotateLeft(basicMove[1] / 2);
                    } else {
                        copy.rotateRight(basicMove[1] / 2);
                    }
                    if (basic.determineWinningMove(copy, mark) != null) {
                        return new int[]{i, j};
                    }
                }
            }
        }
        return null; //return null if no move wins
    }

    /**
     * Determines the move for the player.
     * First checks if there is a guaranteed win for the player
     * If there is no such move, it returns a move such that the opponent doesn't have a guaranteed win in 2 moves
     * If no such move exists, it returns a random move
     * @param board the current board state
     * @param mark the mark that the player uses
     * @return the move to be played
     */
    @Override
    public int[] determineMove(Board board, Mark mark) {
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
                    if (j % 2 == 0) { //rotate to the left if j is uneven
                        copy.rotateLeft(j / 2);
                    } else { //else, rotate to the right
                        copy.rotateRight(j / 2);
                    }
                    if (determineWinningMove(copy, mark.other()) == null) {
                        return new int[]{i, j};
                    } //return if move wins
                }
            }
        }
        //if the program reaches this point, the AI has lost the game
        //return a random field with rotation 3, since the game is lost anyway
        return new int[]{random.determineMove(board, mark)[0], 3};
    }
}
