package src.game;

public class GameBoard extends AbstractBoard{
    /*@ public invariant fields.length == DIM*DIM;
        public invariant (\forall int i; (i >= 0 && i < DIM*DIM); fields[i] == Mark.EMPTY || fields[i] == Mark.XX || fields[i] == Mark.OO);
    @*/

    private static final String[] NUMBERING = {" 0 | 1 | 2 | 3 | 4 | 5 ", "---+---+---+---+---+---",
            " 6 | 7 | 8 | 9 | 10 | 11 ", "---+---+---+---+---+---", " 12 | 13 | 14 | 15 | 16 | 17 ", "---+---+---+---+---+---",
            " 18 | 19 | 20 | 21 | 22 | 23 ", "---+---+---+---+---+---" , " 24 | 25 | 26 | 27 | 28 | 29", "---+---+---+---+---+---",
            " 30 | 31 | 32 | 33 | 34 | 35"};

    public final static int DIM = 6;
    public SubBoard[] subBoards = new SubBoard[4];


    /**
     * Constructor: creates a new Board where all fields are empty.
     */
    //@ ensures (\forall int i; (i >= 0 && i < DIM*DIM); fields[i] == Mark.EMPTY);
    public GameBoard() {
        super(DIM);
        subBoards[0] = new SubBoard(DIM/2);
        subBoards[1] = new SubBoard(DIM/2);
        subBoards[2] = new SubBoard(DIM/2);
        subBoards[3] = new SubBoard(DIM/2);
    }

    /**
     * Returns the index of the subBoard where the given field index belongs to.
     * @param i the index of the field.
     * @return the index of the subBoard.
     */
    //@requires isField(i);
    //@ensures \result >= 0 && \result < 4;
    public int getSubBoard(int i) {
        int row = i/DIM;
        int col = i%DIM;
        int result = 0;
        if (col >= DIM/2) {
            result++;
        }
        if (row >= DIM/2) {
            result += 2;
        }
        return result;
    }

    /**
     * Sets a field to a mark, of both this board and the subBoard of the field.
     * @param i the index of the field to be changed.
     * @param mark the mark the field needs to be set to.
     */
    @Override
    public void setField(int i, Mark mark) {
        int index = getSubBoard(i);
        int row = (i/DIM)%(DIM/2);
        int col = (i%DIM)%(DIM/2);
        int j = subBoards[0].getIndex(row, col);
        subBoards[index].setField(j, mark);
        fields[i] = mark;
    }


    /**
     * Rotates the given subBoard to the right
     * @param i the index of the subBoard
     */
    //@requires i >= 0 && i < 4;
    public void rotateRight(int i) {
        subBoards[i].rotateRight();
        updateBoard(i);
    }


    /**
     * Rotates the given subBoard to the left
     * @param i the index of the subBoard
     */
    //@requires i >= 0 && i < 4;
    public void rotateLeft(int i) {
        subBoards[i].rotateLeft();
        updateBoard(i);
    }

    /**
     * Updates the board so that the fields match the subBoard of the given index.
     * To be used in rotateRight and rotateLeft.
     * @param index the index of the subBoard
     */
    //@requires index >= 0 && index < 4;
    public void updateBoard(int index) {
        int row = DIM/2;
        int col = DIM/2;
        if (index%2 == 0) {
            col = 0;
        }
        if (index < 2) {
            row = 0;
        }
        for(int i = 0; i < DIM/2; i++)  {
            for(int j = 0; j < DIM/2; j++) {
                fields[getIndex(row+ i, col + j)] = subBoards[index].getField(i , j);
            }
        }
    }

    public void reset(){
        for (int i = 0; i<DIM*DIM;i++){
           setField(i,Mark.EMPTY);
        }
    }

    public boolean isFull() {
        boolean result = true;
        for(int i = 0; i<DIM*DIM; i++){
            if(getField(i).equals(Mark.EMPTY)){
                result = false;
            }
        }
        return result;
    }
    /**
     * Check whether a given mark covers a line by winning conditions
     * @param mark represents a mark to check
     * @return true if there are 5 marks in a row
     */
    //@requires mark != Mark.EMPTY;
    public boolean winLine(Mark mark){
        boolean result = false;
        int counter;
        for(int row=0; row<DIM; row++){
            counter = 0;
            for(int col = 0; col< DIM; col++){
                if (!(getField(row,col).equals(mark)) && col > 0){
                    break;
                } else if (getField(row,col).equals(mark)){
                    counter++;
                } else{
                    continue;
                }
                if (counter==5){
                    result = true;
                }
            }
        }
        return result;
    }

    /**
     * Check whether a given mark covers a column by winning conditions
     *@param mark represents a mark to check
     *@return true if there are 5 marks in a column
     */
    public boolean winCol (Mark mark){
        boolean result = false;
        int counter;
        for(int col=0; col<DIM; col++){
            counter = 0;
            for(int row = 0; row< DIM; row++){
                if (!(getField(row,col).equals(mark)) && row > 0){
                    break;
                } else if (getField(row,col).equals(mark)){
                    counter++;
                } else{
                    continue;
                }
                if (counter==5){
                    result = true;
                }
            }
        }
        return result;
    }

    public boolean winDiagonal(Mark mark){
        int counter1 = 0;
        int counter2 = 0;
        for (int pair = 0; pair<DIM; pair+=1){
            if(!getField(pair,pair).equals(mark) && pair > 0){
                break;
            } else if (getField(pair,pair).equals(mark)){
                counter1++;
            }
        }
        for (int pair = 0; pair<DIM; pair+=1){
            if(!getField((DIM-1-pair),pair).equals(mark) && pair>0){
                break;
            } else if (getField((DIM-1-pair),pair).equals(mark)){
                counter2++;
            }
        }
        return (counter1>=5) || (counter2>=5);

    }

    public boolean winIrregularDiagonal(Mark mark){
        boolean result = false;
        int counter1 = 0;
        int counter2 = 0;
        int pair =0;
        while(pair <DIM*DIM){
            if(!(getField(pair).equals(mark)) && (pair != 0)){
                break;
            } else if(!(getField(pair).equals(mark)) && (pair == 0)){
                pair++;
            }else{
                pair+=7;
                counter1++;
            }
        }
        pair = 0;
        while(pair <DIM*DIM){
            if(!(getField(pair).equals(mark)) && (pair != 5)){
                break;
            } else if(!(getField(pair).equals(mark)) && (pair == 0)){
                pair++;
            }else{
                pair+=5;
                counter2++;
            }
        }

        return counter1 == 5 || counter2 == 5;

    }
}
