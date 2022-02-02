package src.server;

import src.Protocol;

import java.io.*;
import java.util.List;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

public class Logic extends Thread {
    private GameServer server;
    private GameClient client;
    private BufferedReader reader;
    private Lock lock = new ReentrantLock();
    private ClientHandler clientHandler;

    /**
     * Constructor that takes input of clientHandler's socket
     *
     * @param clientHandler
     */
    public Logic(ClientHandler clientHandler) {
        this.clientHandler = clientHandler;
        try {
            this.reader = new BufferedReader(new InputStreamReader(clientHandler.getSocket().getInputStream()));
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
        this.client = client;
        try {
            this.reader = new BufferedReader(new InputStreamReader(client.getSocket().getInputStream()));
        } catch (IOException e) {
            System.out.println("Something went wrong while creating logic communicator.");
        }
    }


    //@requires client!=null;
    //@pure;
    public GameClient getClient() {
        return this.client;
    }

    public ClientHandler getClientHandler() {
        return this.clientHandler;
    }


    public void receiveMessageFromClient(){
        while (true) {
            String protocolMessage;
            try {
                protocolMessage = reader.readLine();
                System.out.println(protocolMessage);
            } catch (IOException e) {
                this.clientHandler.shutDown();
                break;
            }
            if (protocolMessage == null) {
                this.clientHandler.shutDown();
                break;
            }
            List<String> decode = Protocol.decodeProtocolMessage(protocolMessage);
            String command = decode.get(0);
            if (command != null) {
                Protocol.CommandsIdentifier commandsIdentifier = Protocol.CommandsIdentifier.valueOf(command);
                String com = null;

                switch (commandsIdentifier) {
                    case LOGIN:
                        String name = decode.get(1);
                        com = this.getClientHandler().getServer().loginClient(name);
                        System.out.println(com);
                        this.getClientHandler().sendMessage(com);
                        break;
                    case HELLO:
                        System.out.println(decode.get(1));
                        com = this.getClientHandler().getServer().greeting();
                        this.getClientHandler().getServer().getViewer().displayServerStatus();
                        this.getClientHandler().sendMessage(com);
                        break;
                    case LIST:
                        com = (this.getClientHandler().getServer().sendList());
                        System.out.println(com);
                        this.getClientHandler().sendMessage(com);
                        break;
                    case QUEUE:
                        this.getClientHandler().getServer().addToQueue(this.clientHandler);
                        this.getClientHandler().getServer().createGame();
                        break;
                    case MOVE:
                        int move = Integer.parseInt(decode.get(1));
                        int rotation = Integer.parseInt(decode.get(2));
                        this.getClientHandler().getServer().makeMove(move, rotation, clientHandler);
                        break;
                    case QUIT:
                        clientHandler.shutDown();
                        break;
                    case PING:
                        clientHandler.getServer().pong(clientHandler);
                        break;
                    case PONG:
                        this.getClientHandler().getServer().ping();
                        break;
                    default:
                        break;
                }
            }

        }
        clientHandler.getServer().removeClient(clientHandler);
    }

    public void receiveMessageFromServer() {
        while (true) {
            String protocolMessage;
            try {
                protocolMessage = reader.readLine();
            } catch (IOException e) {
                System.out.println("Server connection lost :(");
                break;
            }
            if (protocolMessage == null) {
                break;
            }

            List<String> decode = Protocol.decodeProtocolMessage(protocolMessage);
            String command = decode.get(0);
            if (command != null) {
                Protocol.CommandsIdentifier commandsIdentifier = Protocol.CommandsIdentifier.valueOf(command);
                //System.out.println(decode); //for testing purposes
                switch (commandsIdentifier) {
                    case LOGIN:
                        this.getClient().joinList();
                        break;
                    case HELLO:
                        this.getClient().login();
                        break;
                    case ALREADYLOGGEDIN:
                        this.getClient().getViewer().announce("It seems such username already taken. Please, choose another one.^^");
                        this.getClient().setConnection();
                        break;
                    case LIST:
                        this.getClient().joinQueue();
                        break;
                    case NEWGAME:
                        if(decode.get(1).equals(this.getClient().getUsername())){
                            this.getClient().setupGame(0);
                        } else if (decode.get(2).equals(this.getClient().getUsername())){
                            this.getClient().setupGame(1);
                        }
                        break;
                    case MOVE:
                        this.getClient().move(Integer.parseInt(decode.get(1)) , Integer.parseInt(decode.get(2)));
                        break;
                    case GAMEOVER:
                        String reason = decode.get(1);
                        if (decode.size() > 2) {
                            client.getViewer().endGame(reason, decode.get(2).equals(client.getUsername()));
                        } else {
                            client.getViewer().endGame(reason, false);
                        }
                        break;
                    case QUIT:
                        this.getClient().quit();
                        break;
                    case PING:
                        this.getClient().pong();
                        break;
                    case PONG:
                        this.getClient().ping();
                        break;
                    default:
                        break;

                }
            }
        }

    }

    public void run() {
        if (this.client != null) {
            this.receiveMessageFromServer();
        }
        if (this.clientHandler != null) {
            this.receiveMessageFromClient();
        }

        try {
            reader.close();
        } catch (IOException e) {
            System.out.println(Protocol.error());
        }
    }
}
