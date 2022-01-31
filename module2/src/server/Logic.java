package src.server;

import src.Protocol;

import java.io.*;
import java.sql.SQLOutput;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

public class Logic extends Thread {
    private GameServer server;
    private GameClient player;
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
        this.player = client;
        try {
            this.reader = new BufferedReader(new InputStreamReader(client.getSocket().getInputStream()));
        } catch (IOException e) {
            System.out.println("Something went wrong while creating logic communicator.");
        }
    }


    //@requires player!=null;
    //@pure;
    public GameClient getPlayer() {
        return this.player;
    }

    public ClientHandler getClientHandler() {
        return this.clientHandler;
    }


    public void receiveMessageFromClient() throws IOException{
        while (true) {
            String protocolMessage = null;
            try {
                protocolMessage = reader.readLine();
                System.out.println(protocolMessage);
            } catch (IOException e) {
                System.out.println("Pipiska");
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
                        String uname = decode.get(1);//Client by name
                        com = this.getClientHandler().getServer().greeting(uname);
                        this.getClientHandler().getServer().getViewer().displayServerStatus();
                        System.out.println(com);
                        this.getClientHandler().sendMessage(com);
                        break;
                    case LIST:
                        com = (this.getClientHandler().getServer().sendList());
                        System.out.println(com);
                        this.getClientHandler().sendMessage(com);
                        break;
                    case QUEUE:
                        this.getClientHandler().getServer().addToQueue(this.clientHandler);
                        System.out.println(this.getClientHandler().getServer().createGame());
                        break;
                    case MOVE:
                        int move = Integer.parseInt(decode.get(1));
                        int rotation = Integer.parseInt(decode.get(2));
                        com = this.getClientHandler().getServer().makeMove(move, rotation, clientHandler.getUsername());
                        System.out.println(com);
                        break;
                    case SENDTURN:
                        String nameToTurn = decode.get(1);
                        com = this.getClientHandler().getServer().sendTurn(nameToTurn);
                        System.out.println(com);
                        this.getClientHandler().sendMessage(com);
                        break;
                    case QUIT:
                        com = this.getClientHandler().getServer().removeClient(this.getClientHandler());
                        System.out.println(com);
                        this.getClientHandler().sendMessage(com);
                        this.clientHandler.shutDown();
                        break;
                    case PING:
                        this.getClientHandler().getServer().pong();
                        break;
                    case PONG:
                        this.getClientHandler().getServer().ping();
                        break;
                    default:
                        System.out.println(protocolMessage);
                        break;
                }
            }

        }
        clientHandler.getServer().removeClient(clientHandler);
    }

    public void receiveMessageFromServer() {
        while (true) {
            String protocolMessage = null;
            try {
                protocolMessage = reader.readLine();
            } catch (IOException e) {
                System.out.println("Syka blyat");
            }
            if (protocolMessage == null) {
                break;
            }

            List<String> decode = Protocol.decodeProtocolMessage(protocolMessage);
            String command = decode.get(0);
            if (!command.equals(null)) {
                Protocol.CommandsIdentifier commandsIdentifier = Protocol.CommandsIdentifier.valueOf(command);
                switch (commandsIdentifier) {
                    case LOGIN:
                        this.getPlayer().greeting(this.getPlayer().getUsername());
                        break;
                    case HELLO:
                        this.getPlayer().joinList();
                        break;
                    case ALREADYLOGGEDIN:
                        this.getPlayer().getViewer().announce("It seems such username already taken. Please, choose another one.^^");
                        this.getPlayer().setConnection();
                        break;
                    case LIST:
                        this.getPlayer().joinQueue();
                        break;
                    case NEWGAME:
                        if(decode.get(1).equals(this.getPlayer().getUsername())){
                            this.getPlayer().setOpponentUsername(decode.get(2));
                        } else{
                            this.getPlayer().setOpponentUsername(decode.get(1));
                        }
                        this.getPlayer().setupGame();
                        break;
                    case SENDTURN:
                        this.getPlayer().move();
                        break;
                    case MOVE:
                        this.getPlayer().sendTurn(this.getPlayer().getUsername());
                        break;
                    case GAMEOVER:
                        String reason = decode.get(1);
                        this.getPlayer().getViewer().endGame(reason);
                        break;
                    case QUIT:
                        this.getPlayer().quit();
                        break;
                    case PING:
                        this.getPlayer().pong();
                        break;
                    case PONG:
                        this.getPlayer().ping();
                        break;
                    default:
                        System.out.println(protocolMessage);
                        break;

                }
            }
        }

    }

    public void run() {
        if (this.player != null) {
            this.receiveMessageFromServer();
        }
        if (this.clientHandler != null) {
            try {
                this.receiveMessageFromClient();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }

        try {
            reader.close();
        } catch (IOException e) {
            System.out.println(Protocol.error());
        }
    }
}
