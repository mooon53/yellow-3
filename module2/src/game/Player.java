package src.game;

/**
 * Abstract class that both ComputerPlayer and HumanPlayer extend.
 * Implements the shared methods and fields of both classes
 */
public abstract class Player {
    private final String name;
    private final Mark mark;

    /**
     * Constructor: create a Player with the given name and mark.
     * @param name username of the player
     * @param mark mark of the player
     */
    public Player(String name, Mark mark) {
        this.name = name;
        this.mark = mark;
    }

    /**
     * Returns name of the player
     * @return name
     */
    //@pure;
    public String getName() {
        return this.name;
    }

    /**
     * Asks the player which move it wants to play
     * @param board current board state
     * @return the move to be played in an array of integers
     */
    public abstract int[] turn(GameBoard board);

    /**
     * Returns the mark of the player.
     * @return mark
     */
    //@pure;
    public Mark getMark() {
        return this.mark;
    }
}
