package src.game;

public abstract class Player {
    private final String name;
    private final Mark mark;

    public Player(String name, Mark mark) {
        this.name = name;
        this.mark = mark;
    }

    public String getName() {
        return this.name;
    }

    public abstract int[] turn(GameBoard board);


    public Mark getMark() {
        return this.mark;
    }
}
