package src.test;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import src.game.*;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class GameTest {
    private GameBoard board;
    private Game game;
    private Player player1;
    private Player player2;

    @BeforeEach
    public void setup(){
        player1 = new HumanPlayer("player1", Mark.XX);
        player2 = new HumanPlayer("player2", Mark.OO);
        board = new GameBoard();
        game = new Game(player1, player2);
    }

    @Test
    public void resetTest(){
        board.setField(5, Mark.XX);
        board.reset();
        assertEquals(Mark.EMPTY, board.getField(5));

    }

    @Test
    public void testIsFull(){
        for (int i =0; i < board.dim* board.dim; i++){
                board.setField(i,Mark.XX);
        }
        assertTrue(board.isFull());
    }
}
