package src.game;

public interface Board {
    int getIndex(int row, int col);

    Mark getField(int i);

    Mark getField(int row, int col);

    boolean isField(int i);

    void setField(int i, Mark mark);

    Board deepCopy();
}
