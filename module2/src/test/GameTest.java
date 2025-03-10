package src.test;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import src.model.game.*;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Test class that test the win-conditions of the board
 * Also tests board.isFull() and board.reset()
 */
public class GameTest {
    private GameBoard board;

    /**
     * Creates a new board
     */
    @BeforeEach
    public void setup() {
        board = new GameBoard();
    }

    /**
     * Tests if the board resets correctly
     */
    @Test
    public void resetTest() {
        board.setField(5, Mark.XX);
        board.reset();
        assertEquals(Mark.EMPTY, board.getField(5));

    }

    /**
     * Tests if isFull() works correctly.
     */
    @Test
    public void testIsFull() {
        for (int i = 0; i < board.dim * board.dim; i++) {
            board.setField(i, Mark.XX);
        }
        assertTrue(board.isFull());
    }

    /**
     * Tests if winLine works correctly.
     */
    @Test
    public void hasWinningLine() {
        board.setField(1, Mark.XX);
        board.setField(2, Mark.XX);
        board.setField(3, Mark.XX);
        board.setField(4, Mark.XX);
        board.setField(11, Mark.XX);
        assertFalse(board.winLine(Mark.XX));
        board.setField(5, Mark.XX);
        board.winLine(Mark.XX);
        assertTrue(board.winLine(Mark.XX));

    }

    /**
     * Tests if winColumn works correctly.
     */
    @Test
    public void hasWinningColumn() {
        board.setField(2, Mark.XX);
        board.setField(8, Mark.XX);
        board.setField(14, Mark.XX);
        board.setField(20, Mark.XX);
        board.setField(9, Mark.XX);
        board.setField(15, Mark.XX);
        board.setField(21, Mark.XX);
        board.setField(27, Mark.XX);
        assertFalse(board.winCol(Mark.XX));
        board.setField(26, Mark.XX);
        assertTrue(board.winCol(Mark.XX));
    }

    /**
     * Tests if winDiagonal works for the diagonal from top left to bottom right.
     */
    @Test
    public void hasWinningRightDiagonal() {
        board.setField(0, Mark.XX);
        board.setField(14, Mark.XX);
        board.setField(21, Mark.XX);
        board.setField(28, Mark.XX);
        assertFalse(board.winDiagonal(Mark.XX));
        board.setField(7, Mark.XX);
        assertTrue(board.winDiagonal(Mark.XX));
    }

    /**
     * Tests if winDiagonal works for the diagonal from top right to bottom left
     */
    @Test
    public void hasWinningLeftDiagonal() {
        board.setField(10, Mark.XX);
        board.setField(15, Mark.XX);
        board.setField(20, Mark.XX);
        board.setField(25, Mark.XX);

        assertFalse(board.winDiagonal(Mark.XX));
        board.setField(30, Mark.XX);
        board.winDiagonal(Mark.XX);
        assertTrue(board.winDiagonal(Mark.XX));
    }

    /**
     * Tests if winIrregularDiagonal() works for diagonals from top left to bottom right.
     */
    @Test
    public void hasWinningIrrRightDiagonal() {
        board.setField(8, Mark.XX);
        board.setField(15, Mark.XX);
        board.setField(22, Mark.XX);
        board.setField(29, Mark.XX);

        board.setField(6, Mark.XX);
        board.setField(13, Mark.XX);
        board.setField(20, Mark.XX);
        board.setField(27, Mark.XX);

        board.setField(1, Mark.OO);
        assertFalse(board.winIrregularDiagonal(Mark.XX));

        board.setField(34, Mark.XX);
        assertTrue(board.winIrregularDiagonal(Mark.XX));

        board.reset();

        board.setField(6, Mark.XX);
        board.setField(13, Mark.XX);
        board.setField(20, Mark.XX);
        board.setField(27, Mark.XX);
        assertFalse(board.winIrregularDiagonal(Mark.XX));
        board.setField(34, Mark.XX);
        assertTrue(board.winIrregularDiagonal(Mark.XX));
    }

    /**
     * Tests if winIrregularDiagonal() works for diagonals from top right to bottom left.
     */
    @Test
    public void hasWinningIrrLeftDiagonal() {
        board.setField(4, Mark.XX);
        board.setField(9, Mark.XX);
        board.setField(14, Mark.XX);
        board.setField(19, Mark.XX);
        assertFalse(board.winIrregularDiagonal(Mark.XX));
        board.setField(24, Mark.XX);
        assertTrue(board.winIrregularDiagonal(Mark.XX));

        board.reset();

        board.setField(11, Mark.XX);
        board.setField(16, Mark.XX);
        board.setField(21, Mark.XX);
        board.setField(26, Mark.XX);
        assertFalse(board.winIrregularDiagonal(Mark.XX));
        board.setField(31, Mark.XX);
        board.winIrregularDiagonal(Mark.XX);
        assertTrue(board.winIrregularDiagonal(Mark.XX));



    }

}
