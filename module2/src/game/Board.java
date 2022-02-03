package src.game;

/**
 * Interface for both the GameBoard and SubBoard.
 */
public interface Board {
    /**
     * Returns the index of the given row and column of the board.
     * @param row row of the board
     * @param col column of the board
     * @return index of the field
     */
    int getIndex(int row, int col);

    /**
     * Returns the Mark of the field i.
     * @param i the index of the field requested.
     * @return the Mark of the field requested.
     */
    Mark getField(int i);

    /**
     * Returns the Mark of the field in given row and column.
     * @param row row of the field requested
     * @param col column of the field requested
     * @return mark of the field requested
     */
    Mark getField(int row, int col);

    /**
     * Checks if given index is a field of the board.
     * @return true if i is a valid index of fields, false otherwise
     */
    boolean isField(int i);


    /**
     * Sets a field to a mark.
     * @param i the index of the field to be changed.
     * @param mark the mark the field needs to be set to.
     */
    void setField(int i, Mark mark);

    /**
     * Creates a deep copy of this board.
     */
    Board deepCopy();
}
