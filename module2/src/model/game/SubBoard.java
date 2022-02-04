package src.model.game;

public class SubBoard extends AbstractBoard {

    /**
     * Constructor: creates a subBoard with given dimension
     * @param dim dimension of the subBoard
     */
    public SubBoard(int dim) {
        super(dim);
    }


    /**
     * Creates a deepCopy of this subBoard.
     * @return a different subBoard with the same exact fields
     */
    //@ ensures \result != this;
    @Override
    public SubBoard deepCopy() {
        SubBoard copyBoard = new SubBoard(dim);
        System.arraycopy(this.fields, 0, copyBoard.fields, 0, dim * dim);
        return copyBoard;
    }


    /**
     * Rotates the subBoard to the right for 90 degrees.
     */
    //@ensures \old(fields[0]).equals(fields[2]);
    public void rotateRight() {
        Board copy = deepCopy();
        for (int i = 0; i < dim; i++)  {
            for (int j = 0; j < dim; j++) {
                fields[getIndex(i, j)] = copy.getField(dim - 1 - j, i);
            }
        }
    }

    /**
     * Rotates the subBoard to the left for 90 degrees.
     */
    //@ensures \old(fields[0]).equals(fields[6]);
    public void rotateLeft() {
        Board copy = deepCopy();
        for (int i = 0; i < dim; i++)  {
            for (int j = 0; j < dim; j++) {
                fields[getIndex(i, j)] = copy.getField(j, dim - 1 - i);
            }
        }
    }
}
