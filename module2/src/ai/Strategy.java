package src.ai;

import src.game.Board;
import src.game.Mark;

public interface Strategy {

    /**
     * Each strategy has a name
     * @return the name of the strategy
     */
    String getName();

    /**
     * Determines the next move according to the strategy used
     * @param board the current board state
     * @param mark the mark that the player uses
     * @return a valid move (which should be determined according to the strategy)
     */
    int determineMove(Board board, Mark mark);
}
