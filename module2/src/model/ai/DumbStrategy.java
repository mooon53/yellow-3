package src.model.ai;


import src.model.game.Board;
import src.model.game.GameBoard;
import src.model.game.Mark;

/**
 * A strategy that just select random legal moves
 */
public class DumbStrategy implements Strategy {

    /**
     * The name (difficulty) of the strategy
     * @return the name of the strategy
     */
    @Override
    public String getName() {
        return "Easy";
    }

    /**
     * Gets all the indexes of empty fields, and select a random one.
     * Also selects a random rotation.
     * @param board the current board state
     * @param mark the mark that the player uses
     * @return a random legal move
     */
    @Override
    public int[] determineMove(Board board, Mark mark) {
        int[] moveList = new int[GameBoard.DIM * GameBoard.DIM];
        int i = 0;
        for (int j = 0; board.isField(j); j++) {
            if (board.getField(j) == Mark.EMPTY) { //only adds it to moveList if the move is valid
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
