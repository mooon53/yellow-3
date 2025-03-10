package src.test;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Disabled;

import src.model.ai.*;
import src.model.game.GameBoard;
import src.model.game.Mark;

import static org.junit.jupiter.api.Assertions.*;

/**
 * A test file with toString methods to see AI behaviour when they play against each other.
 * It doesn't actually assert much, but it prints the board state for every move, so you can see what's happening
 */
public class ComputerTest {
    private GameBoard board;
    private Strategy strategy;

    /**
     * Creates a new board
     */
    @BeforeEach
    public void setUp() {
        board = new GameBoard();
    }

    /**
     * Plays a game with random moves.
     */
    @Disabled
    @Test
    public void testRandomGame() {
        strategy = new DumbStrategy();
        playGame();
    }

    /**
     * Plays a game BasicStrategy determining all the moves.
     */
    @Disabled
    @Test
    public void testBasicStrategy() {
        strategy = new BasicStrategy();
        playGame();
    }

    /**
     * Plays a game with SmartStrategy determining all the moves.
     */
    @Disabled
    @Test
    public void testSmartStrategy() {
        strategy = new SmartStrategy();
        playGame();
        assertTrue(board.isFull());
    }

    /**
     * Plays a game with all the moves determined by 1 algorithm.
     */
    public void playGame() {
        Mark mark = Mark.XX;
        while (!board.isFull() && !board.isWinner(Mark.XX) && !board.isWinner(Mark.OO)) {
            var move = strategy.determineMove(board, mark);
            board.setField(move[0], mark);
            if (move[1] % 2 == 0) {
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


    /**
     * Tests if SmartStrategy behaves as expected.
     */
    @Test
    public void testSmartWinningMove() {
        strategy = new SmartStrategy();
        board.setField(7, Mark.XX);
        board.setField(13, Mark.XX);
        board.setField(19, Mark.XX);
        var move = strategy.determineMove(board, Mark.OO);
        board.setField(move[0], Mark.OO);
        if (move[1] % 2 == 0) {
            board.rotateLeft(move[1] / 2);
        } else {
            board.rotateRight(move[1] / 2);
        }
        System.out.println(board.toString());
    }


}