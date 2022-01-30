package src.game;

public abstract class Player {
    private String name;
    private Mark mark;
    private boolean yourTurn;

    public Player(String name, boolean turn){
        this.name = name;
        this.yourTurn = turn;
    }

    public String getName() {
        return this.name;
    }

    public abstract int[] turn(GameBoard board);

    public void setMark(int index) {
        if (index == 1) {
            this.mark = Mark.XX;
        } else {
            this.mark = Mark.OO;
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
        return mark;
    }
}
