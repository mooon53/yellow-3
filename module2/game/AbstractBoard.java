package game;

public abstract class AbstractBoard implements Board{
    protected final int dim;
    protected Mark[] fields;

    public AbstractBoard(int dim) {
        this.dim = dim;
        fields = new Mark[dim*dim];
        for (int i = 0; i < dim*dim; i++) {
            fields[i] = Mark.EMPTY;
        }
    }

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

    //@requires isField(getIndex(row, col));
    //@pure;
    public Mark getField(int row, int col) {
        return fields[getIndex(row, col)];
    }


    /**
     * @return true if i is a valid index of fields, true if it's not.
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
}


