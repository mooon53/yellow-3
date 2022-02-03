package src;


import java.util.*;

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



    public static String greeting(String text) {
        return "HELLO" + AS + text;
    }


    public static String error(String message) {
        return "ERROR~" + message;
    }

    public static String error() {
        return "ERROR";
    }

    //----------------------------------------------------
    public static String newGame(String player1, String player2) {
        return "NEWGAME~" + player1 + "~" + player2;
    }
    public static String login(String username) {
        return "LOGIN~" + username;
    }
    public static String login() {
        return "LOGIN";
    }
    public static String move(int index, int rotation) {
        return "MOVE~" + index + AS + rotation;
    }
    public static String gameover(String reason, String username) {
        if (reason.equals("DRAW")) {
            return "GAMEOVER" + AS + "DRAW";
        } else {
            return "GAMEOVER" + AS + reason + AS + username;
        }
    }
    public static String list(ArrayList<String> names) {
        String res = "LIST";
        for (String name : names) {
            res += AS + name;
        }
        return res;
    }

    public static String list() {
        return "LIST";
    }

    public static String queue() {
        return "QUEUE";
    }
    public static String queue(String username) {
        return "QUEUE" + AS + username;
    }

    public static String alreadyLoggedIn() {
        return "ALREADYLOGGEDIN";
    }

    public static String quit() {
        return "QUIT";
    }

    public static String ping() {
        return "PING";
    }

    public static String pong() {
        return "PONG";
    }

}
