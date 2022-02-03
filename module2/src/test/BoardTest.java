package src.test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;

import src.game.GameBoard;
import src.game.Mark;


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

        board.setField(8, Mark.XX);
        assertEquals(Mark.XX, board.getField(8));
        assertEquals(Mark.XX, board.subBoards[0].getField(5));
    }


    @Test
    public void testSetup() {
        for (int i = 0; i < GameBoard.DIM * GameBoard.DIM; i++) {
            assertEquals(Mark.EMPTY, board.getField(i));
        }
        assertEquals(Mark.EMPTY, board.getField(GameBoard.DIM * GameBoard.DIM - 1));
    }

    @Test
    public void testRotate() {
        board.setField(0, Mark.XX);
        board.setField(8, Mark.XX);
        board.setField(5, Mark.OO);
        board.rotateRight(0);
        assertEquals(Mark.XX, board.getField(2));
        assertEquals(Mark.XX, board.getField(13));
        assertEquals(Mark.OO, board.getField(5));
        board.rotateRight(1);
        assertEquals(Mark.OO, board.getField(17));
        assertEquals(Mark.XX, board.getField(2));
        assertEquals(Mark.XX, board.getField(13));
    }

    @Test
    public void testRotateLeft() {
        board.setField(29, Mark.XX);
        board.setField(19, Mark.XX);
        board.setField(5, Mark.OO);
        board.rotateLeft(2);
        assertEquals(Mark.OO, board.getField(5));
        assertEquals(Mark.XX, board.getField(29));
        assertEquals(Mark.XX, board.getField(24));
        board.rotateLeft(3);
        assertEquals(Mark.OO, board.getField(5));
        assertEquals(Mark.XX, board.getField(22));
        assertEquals(Mark.XX, board.getField(24));
    }


    @Test
    public void testString() {
        board.setField(29, Mark.XX);
        board.setField(19, Mark.XX);
        board.setField(5, Mark.OO);
        System.out.println(board.toString());
    }

}


