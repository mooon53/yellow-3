package src.game;

public class SubBoard extends AbstractBoard{

    public SubBoard(int DIM) {
        super(DIM);
    }



    /**
     * Creates a deep copy of this subBoard.
     */
    //@ensures \result != this;
    //@ensures (\forall int i; (i >= 0 && i < dim*dim); \result.fields[i] == this.fields[i]);
    //@pure;
    public SubBoard deepCopy() {
        SubBoard copyBoard = new SubBoard(dim);
        System.arraycopy(this.fields, 0, copyBoard.fields, 0, dim * dim);
        return copyBoard;
    }


    /**
     * Rotates the subBoard to the right for 90 degrees.
     */
    //@ensures \old(fields[0]).equals(fields[2]);
    public void rotateRight(){
        Board copy = deepCopy();
        for(int i = 0; i < dim; i++)  {
            for(int j = 0; j < dim; j++) {
                fields[getIndex(i , j)] = copy.getField(dim-1-j, i);
            }
        }
    }

    /**
     * Rotates the subBoard to the left for 90 degrees.
     */
    //@ensures \old(fields[0]).equals(fields[6]);
    public void rotateLeft(){
        Board copy = deepCopy();
        for(int i = 0; i < dim; i++)  {
            for(int j = 0; j < dim; j++) {
                fields[getIndex(i , j)] = copy.getField(j, dim-1-i);
            }
        }
    }
}
