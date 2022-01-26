package src.game;

public abstract class Player {
    private String name; //name of the HumanPlayer
    private Mark mark; //represents mark assigned to a player


    //creates new Player object
    public Player(String name, Mark mark){
        this.name = name;
        this.mark = mark;
    }

    //default getters
    //@pure;
    public String getName() {
        return this.name;
    }
    //@pure;
    public Mark getMark() {
        return this.mark;
    }

    /**
     * Assigns the following move of Player
     * @param board represents current playable board
     * @return index of player's next move
     */
    public abstract int chooseMove(GameBoard board);

    /**
     * Assigns the rotation that the Player wants to make
     * @param board represents current playable board
     * @return index of the subBoard the player want to rotate, +4 for rotation to the left
     */
    public abstract int chooseRotation(GameBoard board);

    /**
     * Commits the chosen move of the player to the board
     * @param board represents current playable board
     */
    public void makeMove(GameBoard board){
        int move = chooseMove(board);
        int rotation = chooseRotation(board);
        if (rotation/4 == 1) { //this means player has chosen rotation to the left
            board.rotateLeft(rotation%4);
        } else { //this means player has chosen rotation to the right
            board.rotateRight(rotation);
        }
        board.setField(move, getMark());
    }
}
