package src.ai;

import src.game.GameBoard;
import src.game.Mark;
import src.game.Player;

public class ComputerPlayer extends Player {
    private Strategy strategy;

    public ComputerPlayer(Strategy strategy, boolean turn) {
        super(strategy.getName() + "-", turn);
        this.strategy = strategy;
    }

    @Override
    public int[] turn(GameBoard board){
        return strategy.determineMove(board, Mark.XX);
    }


    //@pure;
    public Strategy getStrategy() {
        return strategy;
    }

}
