package src.test;



import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import src.game.Mark;


import static org.junit.jupiter.api.Assertions.assertEquals;


public class MarkChangeTest {
    private Mark mark;

    @BeforeEach
    public void setup(){
        mark = Mark.XX;
    }

    @Test
    public void ifMarkChange(){
        assertEquals(Mark.OO, mark.other());
        mark = Mark.OO;
        assertEquals(Mark.XX, mark.other());
        mark = Mark.EMPTY;
        assertEquals(Mark.EMPTY, mark.other());

    }
}
