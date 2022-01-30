package src.test;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import src.game.Player;
import src.game.*;
import src.server.Game;

import static org.junit.jupiter.api.Assertions.*;

public class GameTest {
    private GameBoard board;
    private Game game;
    private Player player1;
    private Player player2;

    @BeforeEach
    public void setup(){
        player1 = new HumanPlayer("player1",true);
        player2 = new HumanPlayer("player2", false);
        board = new GameBoard();
        //game = new Game(player1, player2);
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

    @Test
    public void hasWinningLine(){
        board.setField(1,Mark.XX);
        board.setField(2,Mark.XX);
        board.setField(3,Mark.XX);
        board.setField(4,Mark.XX);
        board.setField(11,Mark.XX);
        assertFalse(board.winLine(Mark.XX));
        board.setField(5,Mark.XX);
        board.winLine(Mark.XX);
        assertTrue(board.winLine(Mark.XX));
    }

    @Test
    public void hasWinningColumn(){
        board.setField(2,Mark.XX);
        board.setField(8,Mark.XX);
        board.setField(14,Mark.XX);
        board.setField(20,Mark.XX);
        board.setField(9,Mark.XX);
        board.setField(15,Mark.XX);
        board.setField(21,Mark.XX);
        board.setField(27,Mark.XX);
        assertFalse(board.winCol(Mark.XX));
        board.setField(26,Mark.XX);
        assertTrue(board.winCol(Mark.XX));
    }

    @Test
    public void hasWinningRightDiagonal(){
        board.setField(7,Mark.XX);
        board.setField(14,Mark.XX);
        board.setField(21,Mark.XX);
        board.setField(28,Mark.XX);
        //board.winDiagonal(Mark.XX);
        assertFalse(board.winDiagonal(Mark.XX));
        board.setField(35,Mark.XX);
        board.winDiagonal(Mark.XX);
        assertTrue(board.winDiagonal(Mark.XX));
    }

    @Test
    public void hasWinningLeftfDiagonal(){
        board.setField(10,Mark.XX);
        board.setField(15,Mark.XX);
        board.setField(20,Mark.XX);
        board.setField(25,Mark.XX);
        //board.winDiagonal(Mark.XX);
        assertFalse(board.winDiagonal(Mark.XX));
        board.setField(30,Mark.XX);
        board.winDiagonal(Mark.XX);
        assertTrue(board.winDiagonal(Mark.XX));
    }

    @Test
    public void hasWinningIrrRightDiagonal(){
        board.setField(8,Mark.XX);
        board.setField(15,Mark.XX);
        board.setField(22,Mark.XX);
        board.setField(29,Mark.XX);

        board.setField(6,Mark.XX);
        board.setField(13,Mark.XX);
        board.setField(20,Mark.XX);
        board.setField(27,Mark.XX);

        assertFalse(board.winIrregularDiagonal(Mark.XX));

        board.setField(1,Mark.OO);
        assertFalse(board.winIrregularDiagonal(Mark.XX));

        board.setField(34,Mark.XX);
        assertTrue(board.winIrregularDiagonal(Mark.XX));

        board.reset();

        board.setField(6,Mark.XX);
        board.setField(13,Mark.XX);
        board.setField(20,Mark.XX);
        board.setField(27,Mark.XX);
        assertFalse(board.winIrregularDiagonal(Mark.XX));
        board.setField(34,Mark.XX);
        assertTrue(board.winIrregularDiagonal(Mark.XX));
    }

    @Test
    public void hasWinningIrrLeftDiagonal(){
        board.setField(4,Mark.XX);
        board.setField(9,Mark.XX);
        board.setField(14,Mark.XX);
        board.setField(19,Mark.XX);
        assertFalse(board.winIrregularDiagonal(Mark.XX));
        board.setField(24, Mark.XX);
        assertTrue(board.winIrregularDiagonal(Mark.XX));

        board.reset();
        board.setField(11,Mark.XX);
        board.setField(16,Mark.XX);
        board.setField(21,Mark.XX);
        board.setField(26,Mark.XX);
        assertFalse(board.winIrregularDiagonal(Mark.XX));
        board.setField(31, Mark.XX);
        board.winIrregularDiagonal(Mark.XX);
        assertTrue(board.winIrregularDiagonal(Mark.XX));



    }

}
