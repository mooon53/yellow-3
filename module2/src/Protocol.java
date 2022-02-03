package src;


import java.util.*;

/**
 * The Protocol that both the server and the client need to follow.
 */
public class Protocol {
    /**
     * argument separator.
     */
    public static final String AS = "~";

    /**
     * CommandsIdentifiers to save meaning of commands.
     */
    public enum CommandsIdentifier {
        HELLO, //greeting
        LOGIN, //login by client
        ALREADYLOGGEDIN, //username is already logged in
        LIST, //list of logged clients of game
        NEWGAME, //new game
        MOVE, //move
        GAMEOVER, //game over : disconnect/victory/draw
        PING, //send
        PONG, //receive
        QUIT, //disconnect
        ERROR, //the command is triggered by error
        QUEUE //waiting queue of players
    }



    /**
     * Transform received string to protocol format.
     *
     * @param string protocol format string
     * @return list of strings, created by splitting the original string with ~
     */
    public static List<String> decodeProtocolMessage(String string) {
        return Arrays.asList(string.split(AS));
    }


    /**
     * Encodes the text to send as HELLO command.
     * @param text to encode
     * @return encoded HELLO command
     */
    public static String greeting(String text) {
        return "HELLO" + AS + text;
    }

    /**
     * Encodes the message to send as ERROR command.
     * @param message to encode
     * @return encoded ERROR command
     */
    public static String error(String message) {
        return "ERROR~" + message;
    }

    /**
     * Encodes an ERROR command.
     * @return encoded ERROR command
     */
    public static String error() {
        return "ERROR";
    }

    /**
     * Encodes a NEWGAME command.
     * @param player1 player that has the first turn
     * @param player2 second player
     * @return encoded NEWGAME command
     */
    public static String newGame(String player1, String player2) {
        return "NEWGAME~" + player1 + "~" + player2;
    }

    /**
     * Encodes a LOGIN command.
     * @param username to login with
     * @return encoded LOGIN command.
     */
    public static String login(String username) {
        return "LOGIN~" + username;
    }

    /**
     * Encodes a LOGIN command.
     * @return encoded LOGIN command.
     */
    public static String login() {
        return "LOGIN";
    }

    /**
     * Encodes a MOVE command.
     * @param index the field of the move
     * @param rotation the rotation of the move
     * @return encoded MOVE command
     */
    public static String move(int index, int rotation) {
        return "MOVE~" + index + AS + rotation;
    }

    /**
     * Encodes a GAMEOVER command.
     * @param reason the reason that the game is finished
     * @param username the winner of the game
     * @return encoded GAMEOVER command
     */
    public static String gameover(String reason, String username) {
        if (reason.equals("DRAW")) {
            return "GAMEOVER" + AS + "DRAW";
        } else {
            return "GAMEOVER" + AS + reason + AS + username;
        }
    }

    /**
     * Encodes a LIST command.
     * @param names the list that needs to be sent
     * @return encoded LIST command
     */
    public static String list(ArrayList<String> names) {
        String res = "LIST";
        for (String name : names) {
            res += AS + name;
        }
        return res;
    }

    /**
     * Encodes a LIST command.
     * @return encoded LIST command.
     */
    public static String list() {
        return "LIST";
    }

    /**
     * Encodes a QUEUE command.
     * @return encoded QUEUE command
     */
    public static String queue() {
        return "QUEUE";
    }

    /**
     * Encodes an ALREADYLOGGEDIN command.
     * @return encoded ALREADYLOGGEDIN command
     */
    public static String alreadyLoggedIn() {
        return "ALREADYLOGGEDIN";
    }

    /**
     * Encodes a QUIT command.
     * @return encoded QUIT command
     */
    public static String quit() {
        return "QUIT";
    }

    /**
     * Encodes a PING command.
     * @return encoded PING command
     */
    public static String ping() {
        return "PING";
    }

    /**
     * Encodes a PONG command.
     * @return encoded PONG command
     */
    public static String pong() {
        return "PONG";
    }

}
