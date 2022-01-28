package src.server;

import src.Protocol;

import java.io.*;
import java.util.ArrayList;

public class Logic extends Thread {
    private ClientHandler clientHandler;
    private GameClient player;
    private BufferedReader reader;
    private BufferedWriter writer;

    /**
     * Constructor that takes input of clientHandler's socket
     *
     * @param handler
     */
    public Logic(ClientHandler handler) {
        this.clientHandler = handler;
        try {
            this.writer = new BufferedWriter(new OutputStreamWriter(handler.getSocket().getOutputStream()));
            this.reader = new BufferedReader(new InputStreamReader(handler.getSocket().getInputStream()));
        } catch (IOException e) {
            System.out.println("Something went wrong while creating logic communicator.");
        }
    }

    /**
     * Constructor that takes input from client's socket
     *
     * @param client
     */
    public Logic(GameClient client) {
        if (client != null) {
            this.player = client;
            try {
                this.reader = new BufferedReader(new InputStreamReader(client.getSocket().getInputStream()));
            } catch (IOException e) {
                System.out.println("Something went wrong while creating logic communicator.");
            }
        }
    }

    //getters
    //@requires clientHandler!=null;
    //@pure;
    public ClientHandler getClientHandler() {
        return this.clientHandler;
    }

    //@requires player!=null;
    //@pure;
    public GameClient getPlayer() {
        return this.player;
    }

    public void receiveMessageFromClient() {
        boolean run = true;
        while (run) {
            String protocolMessage = null;
            try {
                protocolMessage = reader.readLine();
                System.out.println("Command: " + clientHandler.getUsername() + "-" + protocolMessage);
            } catch (IOException e) {
                System.out.println(e.getMessage());
            }
            if(protocolMessage == null){
                this.clientHandler.close();
                break;
            }
            ArrayList<Object> decode = Protocol.decodeProtocolMessage(protocolMessage);
            String command = (String) decode.get(0);
            if(command != null){
                Protocol.CommandsIdentifier commandsIdentifier = Protocol.CommandsIdentifier.valueOf(command);

                switch(commandsIdentifier){
                    case LOGIN:
                        String username = (String) decode.get(1);
                        clientHandler.connect(username);
                        break;
                    case NEWGAME:
                        clientHandler.play();
                        System.out.println(Protocol.encodeArray(decode.toArray()).toString());
                        break;
                    case MOVE:
                        int move = Integer.parseInt((String) decode.get(1));
                        int rotation = Integer.parseInt((String) decode.get(2));
                        int size = Integer.parseInt((String) decode.get(3));
                        clientHandler.makeMove(move, rotation, size);
                        break;
                    case GAMEOVER:
                        clientHandler.getGame().gameOver();
                        System.out.println(Protocol.CommandsIdentifier.GAMEOVER.toString()+Protocol.AS+(String) decode.get(1)+Protocol.CS);
                    default:
                        System.out.println("Your input is not correct.");

                }
            }

        }
    }
}
