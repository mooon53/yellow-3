package src.model.ai;

import src.model.game.Board;
import src.model.game.GameBoard;
import src.model.game.Mark;

/**
 * A strategy that selects winning moves, and prevents winning moves of the opponent.
 * Is still easy to win against, because you often have multiple winning moves at the same time
 * Also always returns the first legal move if opponent has no way of winning
 */
public class BasicStrategy implements Strategy {

    private DumbStrategy random = new DumbStrategy();


    /**
     * The name (difficulty) of the strategy.
     * @return the name of the strategy
     */
    @Override
    public String getName() {
        return "Normal";
    }

    /**
     * Checks if, for every legal move, it makes the selected mark the winner.
     * @param board current board state
     * @param mark mark to be checked if it can win the game
     * @return a winning move, or null if no such move exists
     */
    public int[] determineWinningMove(Board board, Mark mark) {
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
                    if (copy.isWinner(mark)) {
                        return new int[]{i, j};
                    } //return if move wins
                }
            }
        }
        return null; //if no move wins, return null
    }

    /**
     * Determines the move for the player.
     * First checks if there is a move that directly wins them the game
     * If there is no such move, it returns a move such that the opponent cannot win the game in 1 move
     * If no such move exists, it returns a random move
     * @param board the current board state
     * @param mark the mark that the player uses
     * @return the move to be played
     */
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
