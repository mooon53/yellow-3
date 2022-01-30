package src;

import src.game.Mark;

import java.util.*;

public class Protocol {
    /**
     * board dimension
     */
    public static final int[] DIMS = {6, 6};
    /**
     * argument separator
     */
    public static final String AS = "~";
    /**
     * command separator
     */
    public static final String CS = "\n";

    /**
     * CommandsIdentifiers to save meaning of commands
     */
    public enum CommandsIdentifier {
        HELLO, //greeting
        LOGIN, //login by client
        ALREADYLOGGEDIN, //username is already logged in
        LIST, //list of logged clients of game
        NEWGAME, //new game
        SENDTURN, //turn of current player
        MOVE, //move
        GAMEOVER, //game over : disconnect/victory/draw
        PING, //send
        PONG, //receive
        QUIT, //disconnect
        ERROR, //the command is triggered by error
        QUEUE; //waiting queue of players
    }



    /**
     * Transform received string to protocol format
     *
     * @param Pstring protocol format string
     * @return
     */
    public static List<String> decodeProtocolMessage(String Pstring) {
        List<String> list = Arrays.asList(Pstring.split(AS));
        return list;
    }


    public static String[] parseCommands(String line){
        return line.strip().split(CS);
    }

    public static String[] parseArr(String line) {
        return line.strip().split(AS);
    }

    public static String encodeArray(String[] array){
        StringBuilder stringBuilder = new StringBuilder();

        for(int i = 0; i< array.length; i++){
            stringBuilder.append(array[i]);
            if (i != array.length-1){
                stringBuilder.append(AS);
            }
        }
        stringBuilder.append(CS);
        return stringBuilder.toString();
    }



    public static String greeting(String text){
        //System.out.println("HELLO"+AS+text);
        return "HELLO"+AS+text;
    }


    public static String error (String message){
        return "ERROR~"+message;
    }

    public static String error(){
        return "ERROR";
    }

    //----------------------------------------------------
    public static String newGame(String player1, String player2){
        return "NEWGAME~"+player1+"~"+player2;
    }
    public static String login(String username){
        return "LOGIN~"+username;
    }
    public static String login(){
        return "LOGIN";
    }
    public static String move(int index, int rotation){
        return "MOVE~"+index+AS+rotation;
    }
    public static String sendTurn(String text){
        return "SENDTURN~"+text;
    }
    public static  String sendTurn(){
        return "SENDTURN";
    }
    public static String gameover(String reason){
        return "GAMEOVER"+AS+reason;
    }
    public static String list(ArrayList<String> names){
        String res = "LIST";
        for(String name : names){
            res+=(AS+name);
        }
        return res;
    }

    public static String list(){
        return "LIST";
    }

    public static String queue(){
        return "QUEUE";
    }
    public static String queue(String username){
        return "QUEUE"+AS+username;
    }

    public static String alreadyLoggedIn(){
        return "ALREADYLOGGEDIN";
    }

    public static String quit(){
        return "QUIT";
    }

    public static String ping(){
        return "PING";
    }

    public static String pong(){
        return "PONG";
    }

}
