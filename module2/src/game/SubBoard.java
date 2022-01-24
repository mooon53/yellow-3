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
     * Rotates the subBoard to the right
     */
    public void rotateRight(){
        Board copy = deepCopy();
        /*//Hardcoding, change maybe?
        fields[0] = copy.getField(2, 0);
        fields[1] = copy.getField(1, 0);
        fields[2] = copy.getField(0, 0);
        fields[3] = copy.getField(2, 1);
        fields[4] = copy.getField(1, 1);
        fields[5] = copy.getField(0, 1);
        fields[6] = copy.getField(2, 2);
        fields[7] = copy.getField(1, 2);
        fields[8] = copy.getField(0, 2);*/

        for(int i = 0; i < dim; i++)  {
            for(int j = 0; j < dim; j++) {
                fields[getIndex(i , j)] = copy.getField(dim-1-j, i);
            }
        }
    }

    public void rotateLeft(){
        Board copy = deepCopy();
        /*//Hardcoding, change maybe?
        fields[0] = copy.getField(0,2);
        fields[1] = copy.getField(1,2);
        fields[2] = copy.getField(2,2);
        fields[3] = copy.getField(0,1);
        fields[4] = copy.getField(1,1);
        fields[5] = copy.getField(2,1);
        fields[6] = copy.getField(0,0);
        fields[7] = copy.getField(1,0);
        fields[8] = copy.getField(2,0);*/

        for(int i = 0; i < dim; i++)  {
            for(int j = 0; j < dim; j++) {
                fields[getIndex(i , j)] = copy.getField(j, dim-1-i);
            }
        }
    }
}
