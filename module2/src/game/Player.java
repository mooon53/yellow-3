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
     * Assigns the following move of Human Player
     * @param board represents current playable board
     * @return index of player's next move
     */
    public abstract int chooseMove(Board board);

    public void makeMove(Board board){
        int move = chooseMove(board);
        board.setField(move, getMark());
    }
}
