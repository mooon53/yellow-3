package src.ai;

import src.game.Board;
import src.game.GameBoard;
import src.game.Mark;

public class DumbStrategy implements Strategy{
    @Override
    public String getName() {
        return "Easy";
    }

    @Override
    public int determineMove(Board board, Mark mark) {
        int[] moveList = new int[GameBoard.DIM^2];
        int i = 0;
        for (int j = 0; board.isField(j); j++) {
            if (board.getField(j) == Mark.EMPTY) {
                moveList[i] = j;
                i++;
            }
        }
        int index = (int) (Math.random() * i);
        return moveList[index];
    }
}
