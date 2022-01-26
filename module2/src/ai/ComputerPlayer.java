package src.ai;

import src.game.*;

public class ComputerPlayer extends Player {
    private Strategy strategy;

    public ComputerPlayer(Strategy strategy, Mark mark) {
        super(strategy.getName() + "-" + mark.name(), mark);
        this.strategy = strategy;
    }

    @Override
    public int chooseMove(GameBoard board) {
        return strategy.determineMove(board, this.getMark());
    }

    @Override
    public int chooseRotation(GameBoard board) {
        return 0;
    }

    //@pure;
    public Strategy getStrategy() {
        return strategy;
    }
}
