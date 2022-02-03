package src.ai;

import src.game.GameBoard;
import src.game.Mark;
import src.game.Player;

/**
 * Player class that uses the given strategy to determine the moves.
 * To be used for AI players.
 */
public class ComputerPlayer extends Player {
    private Strategy strategy;

    /**
     * Constructor for ComputerPlayer.
     * Needs a strategy to determine moves
     * @param strategy algorithm that the player will use for determining moves
     * @param mark mark of the player
     */
    public ComputerPlayer(Strategy strategy, Mark mark) {
        super(strategy.getName(), mark);
        this.strategy = strategy;
    }

    /**
     * Returns a move determined by the strategy.
     * @param board current board state
     * @return move to be played
     */
    @Override
    public int[] turn(GameBoard board) {
        return strategy.determineMove(board, getMark());
    }
}
