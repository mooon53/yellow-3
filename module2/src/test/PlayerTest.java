package src.test;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import src.game.HumanPlayer;
import src.game.Mark;
import src.game.Player;

import static org.junit.jupiter.api.Assertions.assertEquals;


public class PlayerTest {
    private Player player;
    String name;
    Mark mark;

    @Test
    public void getDataTest(){
        name = "player";
        mark = Mark.XX;
        player = new HumanPlayer(name, mark);
        assertEquals("player", player.getName());
        assertEquals(Mark.XX, player.getHumanMark());
    }
}
