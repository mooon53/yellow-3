package src.game;

public abstract class Player {
    private String name;

    public Player(String name){
        this.name = name;
    }

    public String getName() {
        return this.name;
    }

    public abstract int chooseMove(Board board);

    public abstract int chooseRotation(GameBoard board);
}
