package src.game;

public abstract class Player {
    private String name;
    private Mark mark;

    public Player(String name){
        this.name = name;
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

    public Mark getMark() {
        return mark;
    }
}
