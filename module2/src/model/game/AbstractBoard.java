package src.model.game;

/**
 * Abstract class that implements the Board interface.
 * Implements the shared methods of GameBoard and SubBoard
 */
public abstract class AbstractBoard implements Board{
    public final int dim;
    protected Mark[] fields;

    /**
     * Constructor: sets all the fields to empty mark.
     */
    public AbstractBoard(int dim) {
        this.dim = dim;
        fields = new Mark[dim*dim];
        for (int i = 0; i < dim*dim; i++) {
            fields[i] = Mark.EMPTY;
        }
    }

    /**
     * Returns the index of the given row and column of the board.
     * @param row row of the field requested
     * @param col column of the field requested
     * @return index of the field
     */
    //@requires row < dim && row >= 0;
    //@requires col < dim && col >= 0;
    //@pure;
    public int getIndex(int row, int col) {
        return row*dim + col;
    }

    /**
     * Returns the Mark of the field i.
     * @param i the index of the field requested.
     * @return the Mark of the field requested.
     */
    //@ requires isField(i);
    //@ ensures \result == fields[i];
    //@pure;
    public Mark getField(int i) {
        return fields[i];
    }


    /**
     * Returns the Mark of the field in given row and column.
     * @param row row of the field requested
     * @param col column of the field requested
     * @return mark of the field requested
     */
    //@requires isField(getIndex(row, col));
    //@pure;
    public Mark getField(int row, int col) {
        return fields[getIndex(row, col)];
    }


    /**
     * Checks if given index is a field of the board.
     * @return true if i is a valid index of fields, false otherwise
     */
    //@ensures i < fields.length && i >= 0 ==> \result == true;
    //@pure;
    public boolean isField(int i) {
        return (i < fields.length && i >= 0);
    }


    /**
     * Sets a field to a mark.
     * @param i the index of the field to be changed.
     * @param mark the mark the field needs to be set to.
     */
    //@requires isField(i);
    //@requires mark != null;
    public void setField(int i, Mark mark) {
        fields[i] = mark;
    }

    /**
     * Creates a deep copy of this board.
     */
    //@ensures \result != this;
    //@ensures (\forall int i; (i >= 0 && i < dim*dim); \result.fields[i] == this.fields[i]);
    //@pure;
    public abstract AbstractBoard deepCopy();
}
