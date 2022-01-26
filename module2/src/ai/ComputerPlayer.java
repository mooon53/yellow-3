package src.ai;

import src.game.*;

public class ComputerPlayer extends Player {
    private Strategy strategy;

    public ComputerPlayer(Strategy strategy, Mark mark) {
        super(strategy.getName() + "-" + mark.name(), mark);
        this.strategy = strategy;
    }

    @Override
    public int chooseMove(Board board) {
        return strategy.determineMove(board, this.getMark());
    }

    //@pure;
    public Strategy getStrategy() {
        return strategy;
    }
}
