package src.ai;

import src.game.Board;
import src.game.GameBoard;
import src.game.Mark;

public class SmartStrategy implements Strategy {
    //prevents the opponent from winning by blocking a guaranteed win for the opponent in 2 moves
    //can also see win opportunities 2 moves ahead
    //should be better in seeing patterns than the average player
    private DumbStrategy random = new DumbStrategy();
    private BasicStrategy basic = new BasicStrategy();

    @Override
    public String getName() {
        return "Hard";
    }


    public int[] determineWinningMove(Board board, Mark mark) {
        //see if we can win immediately
        int[] move = basic.determineWinningMove(board, mark);
        if (move != null) {
            return move;
        }

        //see if we can find a guaranteed win (in 2 moves)
        for (int i = 0; board.isField(i); i++) {
            for (int j = 0; j < 8; j++) {
                GameBoard copy = (GameBoard) board.deepCopy();
                if (copy.getField(i) == Mark.EMPTY) {
                    copy.setField(i, mark);
                    if (j / 4 == 1) {
                        copy.rotateLeft(j % 4);
                    } else {
                        copy.rotateRight(j);
                    }
                    //this prevents us from winning, if it's possible
                    int[] basicMove = basic.determineMove(copy, mark.other());
                    copy.setField(basicMove[0], mark);
                    if (basicMove[1] / 4 == 1) {
                        copy.rotateLeft(basicMove[1] % 4);
                    } else {
                        copy.rotateRight(basicMove[1]);
                    }
                    if (basic.determineWinningMove(copy, mark) != null) {
                        return new int[]{i, j};
                    }
                }
            }
        }
        return null; //return null if no move wins
    }


    @Override
    public int[] determineMove(Board board, Mark mark) {
        int[] move = determineWinningMove(board, mark);
        if (move != null) {
            return move;
        }

        //else, make sure the opponent cannot win
        for (int i = 0; board.isField(i); i++) {
            for (int j = 0; j < 8; j++) {
                GameBoard copy = (GameBoard) board.deepCopy();
                if (copy.getField(i) == Mark.EMPTY) {
                    copy.setField(i, mark);
                    if (j / 4 == 1) { //rotate to the left if j > 3
                        copy.rotateLeft(j % 4);
                    } else { //else, rotate to the right
                        copy.rotateRight(j);
                    }
                    if (determineWinningMove(copy, mark.other()) == null) {
                        return new int[]{i, j};
                    } //return if move wins
                }
            }
        }
        //if there isn't a way to prevent the opponent from winning, return a random field with rotation 3
        return new int[]{random.determineMove(board, mark)[0], 3};




        /*int[] winningMove = basic.determineWinningMove(board, mark);
        if (winningMove != null) { //if we can win, execute the move
            return winningMove;
        }

        //next we check if the opponents has moves, such that we cannot prevent them from winning 1 turn later
        for (int i = 0; board.isField(i); i++) {
            for (int j = 0; j < 8; j++) {
                GameBoard copy = (GameBoard) board.deepCopy();
                if (copy.getField(i) == Mark.EMPTY) {
                    copy.setField(i, mark.other());
                    if (j / 4 == 1) { //rotate to the left if j > 3
                        copy.rotateLeft(j % 4);
                    } else { //else, rotate to the right
                        copy.rotateRight(j);
                    }
                    //next, execute basicStrategy move on the copy board
                    int[] basicMove = basic.determineMove(copy, mark);
                    copy.setField(basicMove[0], mark);
                    if (basicMove[1] / 4 == 1) {
                        copy.rotateLeft(basicMove[1] % 4);
                    } else {
                        copy.rotateRight(basicMove[1]);
                    }
                    //see if the opponent has a winning move now
                    winningMove = basic.determineWinningMove(copy, mark.other());
                    if (winningMove != null) {
                        return new int[]{i, j};
                    }

                }
            }
        }*/
    }
}
