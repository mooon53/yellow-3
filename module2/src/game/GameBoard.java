package src.game;

/**
 * Board to play Pentago games on.
 */
public class GameBoard extends AbstractBoard {
    //@public invariant fields.length == DIM*DIM;
    //@public invariant (\forall int i; (i >= 0 && i < DIM*DIM); fields[i] != null);

    public final static int DIM = 6;
    private final static String DELIM = "     ";
    private final static String LINE = "---+---+---+---+---+---";
    private final static String[] NUMBERS = {" 0 | 1 | 2 | 3 | 4 | 5 ", " 6 | 7 | 8 | 9 |10 |11 ",
        "12 |13 |14 |15 |16 |17 ", "18 |19 |20 |21 |22 |23 ",
        "24 |25 |26 |27 |28 |29 ", "30 |31 |32 |33 |34 |35 "};

    /* Board should be shown as follows (with toString())
     0 | 1 | 2 | 3 | 4 | 5
    ---+---+---+---+---+---
     6 | 7 | 8 | 9 |10 |11
    ---+---+---+---+---+---
    12 |13 |14 |15 |16 |17
    ---+---+---+---+---+---
    18 |19 |20 |21 |22 |23
    ---+---+---+---+---+---
    24 |25 |26 |27 |28 |29
    ---+---+---+---+---+---
    30 |31 |32 |33 |34 |35
    */

    public SubBoard[] subBoards = new SubBoard[4];


    /**
     * Constructor: creates a new Board where all fields are empty.
     * Also creates the 4 subBoards that the board is made of
     */
    //@ ensures (\forall int i; (i >= 0 && i < DIM*DIM); fields[i] == Mark.EMPTY);
    public GameBoard() {
        super(DIM);
        subBoards[0] = new SubBoard(DIM / 2);
        subBoards[1] = new SubBoard(DIM / 2);
        subBoards[2] = new SubBoard(DIM / 2);
        subBoards[3] = new SubBoard(DIM / 2);
    }

    /**
     * Returns the index of the subBoard where the given field index belongs to.
     * @param i the index of the field.
     * @return the index of the subBoard.
     */
    //@requires isField(i);
    //@ensures \result >= 0 && \result < 4;
    public int getSubBoard(int i) {
        int row = i / DIM;
        int col = i % DIM;
        int result = 0;
        if (col >= DIM / 2) {
            result++;
        }
        if (row >= DIM / 2) {
            result += 2;
        }
        return result;
    }

    /**
     * Sets a field to a mark, of both this board and the subBoard of the field.
     * @param i the index of the field to be changed.
     * @param mark the mark the field needs to be set to.
     */
    //@requires mark != null;
    //@ensures getField(i) != Mark.EMPTY;
    @Override
    public void setField(int i, Mark mark) {
        int index = getSubBoard(i);
        int row = (i / DIM) % (DIM / 2);
        int col = (i % DIM) % (DIM / 2);
        int j = subBoards[0].getIndex(row, col);
        subBoards[index].setField(j, mark);
        fields[i] = mark;
    }


    /**
     * Creates a deepCopy of this GameBoard, with the subBoards also copied over.
     * @return the copied board
     */
    /*@
    ensures (\forall int i; i>= 0 && i < 4;\result.subBoards[i] != this.subBoards[i]);
    ensures (\forall int i; i>= 0 && i < 4; (\forall int j; (j >= 0 && j < dim*dim);
    \result.subBoards[i].fields[j] == this.subBoards[i].fields[j]));
    */
    @Override
    public GameBoard deepCopy() {
        GameBoard copyBoard = new GameBoard();
        for (int i = 0; i < fields.length; i++) {
            copyBoard.setField(i, this.getField(i));
        }
        return copyBoard;
    }


    /**
     * Rotates the given subBoard to the right.
     * @param i the index of the subBoard
     */
    //@requires i >= 0 && i < 4;
    public void rotateRight(int i) {
        subBoards[i].rotateRight();
        updateBoard(i);
    }


    /**
     * Rotates the given subBoard to the left.
     * @param i the index of the subBoard
     */
    //@requires i >= 0 && i < 4;
    public void rotateLeft(int i) {
        subBoards[i].rotateLeft();
        updateBoard(i);
    }

    /**
     * Updates the board so that the fields match the subBoard of the given index.
     * To be used in rotateRight and rotateLeft
     * @param index the index of the subBoard
     */
    //@requires index >= 0 && index < 4;
    private void updateBoard(int index) {
        int row = DIM / 2;
        int col = DIM / 2;
        if (index % 2 == 0) {
            col = 0;
        }
        if (index < 2) {
            row = 0;
        }
        for (int i = 0; i < DIM / 2; i++)  {
            for (int j = 0; j < DIM / 2; j++) {
                fields[getIndex(row + i, col + j)] = subBoards[index].getField(i, j);
            }
        }
    }

    /**
     * Resets the gameBoard.
     * Sets all the fields to Mark.EMPTY:
     */
    //@ ensures (\forall int i; (i >= 0 && i < DIM*DIM); fields[i] == Mark.EMPTY);
    public void reset() {
        for (int i = 0; i < DIM * DIM; i++) {
            setField(i, Mark.EMPTY);
        }
    }


    /**
     * Checks whether the board is full.
     * @return true if all fields are not empty, false otherwise
     */
    //@ ensures (\forall int i; (i >= 0 && i < DIM*DIM); fields[i] != Mark.EMPTY) ==> \result;
    //@ ensures !(\forall int i; (i >= 0 && i < DIM*DIM); fields[i] != Mark.EMPTY) ==> !\result;
    public boolean isFull() {
        boolean result = true;
        for (int i = 0; i < DIM * DIM; i++) {
            if (getField(i).equals(Mark.EMPTY)) {
                result = false;
            }
        }
        return result;
    }

    /**
     * Checks whether a given mark covers a line by winning conditions.
     * @param mark represents a mark to check
     * @return true if there are 5 marks in a row, false otherwise
     */
    //@requires mark != Mark.EMPTY && mark != null;
    public boolean winLine(Mark mark) {
        boolean result = false;
        int counter;
        for (int row = 0; row < DIM; row++) {
            counter = 0;
            for (int col = 0; col < DIM; col++) {
                if (!(getField(row, col).equals(mark)) && col > 0) {
                    break;
                } else if (getField(row, col).equals(mark)) {
                    counter++;
                } else {
                    continue;
                }
                if (counter == 5) {
                    result = true;
                }
            }
        }
        return result;
    }

    /**
     * Checks whether a given mark covers a column by winning conditions.
     * @param mark represents a mark to check
     * @return true if there are 5 marks in a column, false otherwise
     */
    //@requires mark != Mark.EMPTY && mark != null;
    public boolean winCol(Mark mark) {
        boolean result = false;
        int counter;
        for (int col = 0; col < DIM; col++) {
            counter = 0;
            for (int row = 0; row < DIM; row++) {
                if (!(getField(row, col).equals(mark)) && row > 0) {
                    break;
                } else if (getField(row, col).equals(mark)) {
                    counter++;
                } else {
                    continue;
                }
                if (counter == 5) {
                    result = true;
                }
            }
        }
        return result;
    }

    /**
     * Checks whether the given mark covers one of the main diagonals (with 6 fields).
     * @param mark represents a mark to check
     * @return true if there are 5 marks in one of the main diagonals, false otherwise
     */
    //@requires mark != Mark.EMPTY && mark != null;
    public boolean winDiagonal(Mark mark) {
        int counter1 = 0;
        int counter2 = 0;
        for (int pair = 0; pair < DIM; pair += 1) {
            if (!getField(pair, pair).equals(mark) && pair > 0) {
                break;
            } else if (getField(pair, pair).equals(mark)) {
                counter1++;
            }
        }
        for (int pair = 0; pair < DIM; pair += 1) {
            if (!getField(DIM - 1 - pair, pair).equals(mark) && pair > 0) {
                break;
            } else if (getField(DIM - 1 - pair, pair).equals(mark)) {
                counter2++;
            }
        }
        return counter1 >= DIM - 1 || counter2 >= DIM - 1;

    }


    /**
     * Checks whether the given mark covers one of the other diagonals (with 5 fields).
     * @param mark represents a mark to check
     * @return true if there are 5 marks in one of the other diagonals, false otherwise
     */
    //@requires mark != Mark.EMPTY && mark != null;
    public boolean winIrregularDiagonal(Mark mark) {
        int counter1 = 0;
        int counter2 = 0;
        //right irregular diagonal : starts from 1 or 6
        for (int i = 1; i < DIM * DIM; i += DIM + 1) {
            if (getField(i).equals(mark)) {
                counter1++;
            } else if (i == 1 && getField(i + (DIM - 1)).equals(mark)) {
                counter1++;
                i += DIM - 1;
            } else {
                break;
            }
        }
        //left irregular diagonal : starts from 4 or 11
        for (int i = DIM - 2; i < DIM * DIM; i += DIM - 1) {
            if (getField(i).equals(mark)) {
                counter2++;
            } else if (i == 4 && getField(i + DIM + 1).equals(mark)) {
                counter2++;
                i += DIM + 1;
            } else {
                break;
            }
        }

        return counter1 == 5 || counter2 == 5;
    }

    /**
     * Returns a String representation of the board, such that the current board state is clear.
     * Also shows the indexes of the fields
     */
    public String toString() {
        String s = "";
        for (int i = 0; i < DIM; i++) {
            String row = "";
            for (int j = 0; j < DIM; j++) {
                row = row + " " + getField(i, j).toString().substring(0, 1).replace("E", " ") + " ";
                if (j < DIM - 1) {
                    row = row + "|";
                }
            }
            s = s + row + DELIM + NUMBERS[i];
            if (i < DIM - 1) {
                s = s + "\n" + LINE + DELIM + LINE + "\n";
            }
        }
        return s;
    }

    /**
     * Checks if a Mark (that isn't Mark.EMPTY) fulfills a win-condition.
     * @param mark represents the mark of player
     * @return true if one of players is a winner in either direction
     */
    //@requires mark != Mark.EMPTY && mark != null;
    public boolean isWinner(Mark mark) {
        return winLine(mark) || winCol(mark) || winDiagonal(mark) || winIrregularDiagonal(mark);
    }

}
