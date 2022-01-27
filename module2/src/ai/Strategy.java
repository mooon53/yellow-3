package src.ai;

import src.game.Board;
import src.game.Mark;

public interface Strategy {

    /**
     * Each strategy has a name
     * @return the name of the strategy
     */
    public String getName();

    /**
     * Determines the next move according to the strategy used
     * The first index of the array will be the move, the second the rotation
     * @param board the current board state
     * @param mark the mark that the player uses
     * @return an array of integers, with the first being the index of the field, the second the integer for the rotation
     */
    public int[] determineMove(Board board, Mark mark);
}
