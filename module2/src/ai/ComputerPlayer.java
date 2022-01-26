package src.ai;

import src.game.*;

public class ComputerPlayer extends Player {
    private Strategy strategy;
    private int[] moveList;

    public ComputerPlayer(Strategy strategy, Mark mark) {
        super(strategy.getName() + "-" + mark.name(), mark);
        this.strategy = strategy;
    }

    @Override
    public int chooseMove(GameBoard board) {
        moveList = strategy.determineMove(board, this.getMark());
        return moveList[0];
    }


    @Override
    public int chooseRotation(GameBoard board) {
        //since chooseMove is called first in the makeMove method, this works
        return moveList[1];
    }

    //@pure;
    public Strategy getStrategy() {
        return strategy;
    }
}
