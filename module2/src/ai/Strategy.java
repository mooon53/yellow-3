package src.ai;

import src.game.Board;
import src.game.Mark;

/**
 * Default interface that every AI should implement. Is used by ComputerPlayer.
 */
public interface Strategy {

    /**
     * Each strategy has a name.
     * @return the name of the strategy
     */
    String getName();

    /**
     * Determines the next move according to the strategy used.
     * The first index of the array will be the move, the second the rotation
     * @param board the current board state
     * @param mark the mark that the player uses
     * @return the determined move in an array of integers
     */
    int[] determineMove(Board board, Mark mark);
}
