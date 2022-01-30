package src.ai;

import src.game.GameBoard;
import src.game.Mark;
import src.game.Player;

public class ComputerPlayer extends Player {
    private Strategy strategy;
    private int[] moveList;

    public ComputerPlayer(Strategy strategy) {
        super(strategy.getName());
        this.strategy = strategy;
    }

    @Override
    public int[] turn(GameBoard board){
        moveList = strategy.determineMove(board, Mark.XX);
        //since chooseMove is called first in the makeMove method, this works
        return moveList;
    }


    //@pure;
    public Strategy getStrategy() {
        return strategy;
    }

}
