package src.test;



import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import src.game.Mark;


import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Checks mark.other().
 */
public class MarkChangeTest {
    private Mark mark;

    /**
     * Set mark to Mark.XX.
     */
    @BeforeEach
    public void setup() {
        mark = Mark.XX;
    }

    /**
     * Tests if mark.other() works
     */
    @Test
    public void ifMarkChange() {
        assertEquals(Mark.OO, mark.other());
        mark = Mark.OO;
        assertEquals(Mark.XX, mark.other());
        mark = Mark.EMPTY;
        assertEquals(Mark.EMPTY, mark.other());

    }
}
