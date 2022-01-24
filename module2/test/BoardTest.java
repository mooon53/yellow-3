package test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;

import game.GameBoard;
import game.Mark;


public class BoardTest {
    private GameBoard board;

    @BeforeEach
    public void setUp() {
        board = new GameBoard();
    }

    @Test
    public void testIndex() {
        int index = 0;
        for (int i = 0; i < GameBoard.DIM; i++) {
            for (int j = 0; j < GameBoard.DIM; j++) {
                assertEquals(index, board.getIndex(i, j));
                index += 1;
            }
        }
//        assertEquals(0, board.index(0, 0));
//        assertEquals(1, board.index(0, 1));
//        assertEquals(3, board.index(1, 0));
//        assertEquals(8, board.index(2, 2));
    }

    @Test
    public void testIsFieldIndex() {
        assertFalse(board.isField(-1));
        assertTrue(board.isField(0));
        assertTrue(board.isField(GameBoard.DIM * GameBoard.DIM - 1));
        assertFalse(board.isField(GameBoard.DIM * GameBoard.DIM));
    }


    @Test
    public void testSetAndGetFieldIndex() {
        board.setField(0, Mark.XX);
        assertEquals(Mark.XX, board.getField(0));
        assertEquals(Mark.EMPTY, board.getField(1));
    }


    @Test
    public void testSetup() {
        for (int i = 0; i < GameBoard.DIM * GameBoard.DIM; i++) {
            assertEquals(Mark.EMPTY, board.getField(i));
        }
        assertEquals(Mark.EMPTY, board.getField(GameBoard.DIM * GameBoard.DIM - 1));
    }

    @Test
    public void testRotateRight() {
        board.rotateRight(1);
    }
}


