package src.ai;


import src.game.Board;
import src.game.GameBoard;
import src.game.Mark;

public class DumbStrategy implements Strategy{
    //A strategy that selects random moves
    @Override
    public String getName() {
        return "Easy";
    }

    @Override
    public int[] determineMove(Board board, Mark mark) {
        int[] moveList = new int[GameBoard.DIM^2];
        int i = 0;
        for (int j = 0; board.isField(j); j++) {
            if (board.getField(j) == Mark.EMPTY) { //only adds it to the moveList if the move is valid
                moveList[i] = j;
                i++;
            }
        }
        int index = (int) (Math.random() * i); //choose a random move

        //now choose a random rotation
        int rotation = (int) (Math.random() * 8);

        return new int[]{moveList[index], rotation};
    }
}
