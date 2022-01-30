package src.test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Disabled;

import src.ai.*;
import src.game.GameBoard;
import src.game.Mark;

/**
 * A test file with toString methods to see AI behaviour when they play against each other
 * It doesn't actually assert much, but it prints the board state for every move, so you can see what's happening
 */
public class ComputerTest {
    private GameBoard board;
    private Strategy strategy;

    @BeforeEach
    public void setUp() {
        board = new GameBoard();
    }

    @Disabled
    @Test
    public void testRandomGame() { //not a real test since it doesn't assert anything, but we can see what happens in the console
        strategy = new DumbStrategy();
        playGame();
    }

    @Disabled
    @Test
    public void testBasicStrategy() {
        strategy = new BasicStrategy();
        playGame();
    }


    @Test
    public void testSmartStrategy() {
        strategy = new SmartStrategy();
        playGame();
        assertTrue(board.isFull());
    }

    /**
     * Plays a game with all the moves determined by 1 algorithm
     */
    public void playGame() {
        Mark mark = Mark.XX;
        while (!board.isFull() && !board.isWinner(Mark.XX) && !board.isWinner(Mark.OO)) {
            var move = strategy.determineMove(board, mark);
            board.setField(move[0], mark);
            if (move[1] % 2 == 1) {
                board.rotateLeft(move[1] / 2);
            } else {
                board.rotateRight(move[1] / 2);
            }
            mark = mark.other();
            System.out.println(board.toString());
            System.out.println();
            System.out.println();
        }
    }


}