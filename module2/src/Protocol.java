package src;

import src.game.Mark;

import java.util.ArrayList;
import java.util.Objects;

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
        MOVE, //move
        GAMEOVER, //game over : disconnect/victory/draw
        PING, //send
        PONG, //receive
        QUIT, //disconnect
        ERROR, //the command is triggered by error
        QUEUE; //waiting queue of players
    }

    /**
     * Code array of objects into protocol format to use stream exchange data
     *
     * @param objects the array to be encoded to protocol
     * @return string to be sent in format of protocol
     */
    public static String protocolMessage(Object[] objects) {
        StringBuilder stringBuilder = new StringBuilder();

        for (int i = 0; i < objects.length; i++) {
            Object object = objects[i];
            if (object.getClass().isArray()) {
                stringBuilder.append(encodeArray((Object[]) object));
            } else {
                stringBuilder.append(object);
            }

            if (i != objects.length - 1) {
                stringBuilder.append(CS);
            }
        }
        return stringBuilder.toString();
    }

    /**
     * Transform received string to protocol format
     *
     * @param Pstring protocol format string
     * @return
     */
    public static ArrayList<Object> decodeProtocolMessage(String Pstring) {
        ArrayList<Object> objects = new ArrayList<>();
        String[] commands = parseCommands(Pstring);
        for (String string : commands) {
            if (string.contains(AS)) {
                objects.add(parseArr(string));
            } else {
                objects.add(string);
            }
        }
        return objects;
    }


    public static String[] parseCommands(String line){
        return line.strip().split(CS);
    }

    public static String[] parseArr(String line) {
        return line.strip().split(AS);
    }

    public static String encodeArray(Object[] array){
        StringBuilder stringBuilder = new StringBuilder();

        for(int i = 0; i< array.length; i++){
            stringBuilder.append(array[i].toString());
            if (i != array.length-1){
                stringBuilder.append(AS);
            }
        }
        stringBuilder.append(CS);
        return stringBuilder.toString();
    }


   public static String greeting(String[] params ){
        if (params != null){
            return protocolMessage(new Object[]{CommandsIdentifier.HELLO, params});
        }
        return CommandsIdentifier.HELLO.toString();
    }
    public static String greeting(String username){
        return greeting(new String[]{username});
    }

    public static String error(String[] params){
       if(params!=null){
           return protocolMessage(new Object[]{CommandsIdentifier.ERROR, params});
       }
       return CommandsIdentifier.ERROR.toString();
    }

    public static String error (String message){
        return error(new String[]{message});
    }

    public static String error(){
        return error((String[]) null);
    }

    //----------------------------------------------------
    public static String newGame(String player1, String player2){
        return protocolMessage(new Object[]{CommandsIdentifier.NEWGAME, player1, player2});
    }
    public static String login(String username){
        return protocolMessage(new Object[]{CommandsIdentifier.LOGIN, username});
    }
    public static String move(int index, int rotation, int side){
        return protocolMessage(new Object[]{CommandsIdentifier.MOVE, index, rotation, side});
    }
    public static String gameover(String reason){
        return protocolMessage(new Object[]{CommandsIdentifier.GAMEOVER, reason});
    }
    public static String list(String[] names){
        return protocolMessage(new Object[]{CommandsIdentifier.LIST, names});
    }

    public static String quit(){
        return protocolMessage(new Object[]{CommandsIdentifier.QUIT});
    }

    public static String ping(){
        return protocolMessage(new Object[]{CommandsIdentifier.PING});
    }

    public static String pong(){
        return protocolMessage(new Object[]{CommandsIdentifier.PONG});
    }

}
