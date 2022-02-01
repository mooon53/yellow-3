package src.game;

public abstract class Player {
    private String name;
    private int playerID;
    private Mark mark;
    private boolean yourTurn;

    public Player(String name, Mark mark){
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

    public boolean getYourTurn(){
        return yourTurn;
    }

    public void setYourTurn(boolean yourTurn){
        this.yourTurn = yourTurn;
    }

    public int getPlayerID() {
        return playerID;
    }

    public void setPlayerID(int playerID) {
        this.playerID = playerID;
    }
}
