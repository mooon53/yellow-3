package src.game;

public abstract class Player {
    private String name;
    private boolean yourTurn;
    private Mark mark;

    public Player(String name){
        this.name = name;
    }

    public String getName() {
        return this.name;
    }

    public abstract int[] turn(GameBoard board);

    public void assignMark(int index) {
        if (index == 1) {
            this.mark= Mark.XX;
        } else {
            this.mark= Mark.OO;
        }
    }
    public boolean getTurn(){
        return yourTurn;
    }
    public boolean getTurnByName(String name){
        boolean res = false;
        if(this.getName().equals(name)){
            res = this.getTurn();
        }
        return res;
    }
    public void setTurn(){
        if(yourTurn){
            this.yourTurn = false;
        } else{
            this.yourTurn = true;
        }
    }

    public Mark getMark() {
        return this.mark;
    }
}
