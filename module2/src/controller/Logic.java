package src.controller;

import src.Protocol;

import java.io.*;
import java.util.List;

/**
 * Class that implements the Protocol.
 * Client and clientHandlers use it to process incoming commands
 */
public class Logic extends Thread {
    private GameClient client;
    private BufferedReader reader;
    private ClientHandler clientHandler;

    /**
     * Constructor that takes input of clientHandler's socket.
     * @param ch the clientHandler that the Logic Thread will be bound to
     */
    public Logic(ClientHandler ch) {
        clientHandler = ch;
        try {
            reader = new BufferedReader(new InputStreamReader(ch.getSocket().getInputStream()));
        } catch (IOException e) {
            System.out.println("Something went wrong while creating logic communicator.");
            ch.shutDown();
        }
    }

    /**
     * Constructor that takes input from client's socket.
     * @param client the Client that the Logic Thread will be bound to
     */
    public Logic(GameClient client) {
        this.client = client;
        try {
            reader = new BufferedReader(new InputStreamReader(client.getSocket().getInputStream()));
        } catch (IOException e) {
            System.out.println("Something went wrong while creating logic communicator.");
        }
    }

    /**
     * Processes commands sent by the connected client.
     * To be used by a clientHandler to process commands
     */
    private void receiveMessageFromClient() {
        while (true) {
            String protocolMessage;
            try {
                protocolMessage = reader.readLine();
                System.out.println(protocolMessage);
            } catch (IOException e) {
                clientHandler.shutDown();
                break;
            }
            if (protocolMessage == null) {
                clientHandler.shutDown();
                break;
            }
            List<String> decode = Protocol.decodeProtocolMessage(protocolMessage);
            String command = decode.get(0);
            if (command != null) {
                Protocol.CommandsIdentifier comId = Protocol.CommandsIdentifier.valueOf(command);
                String com;

                switch (comId) {
                    case LOGIN:
                        String name = decode.get(1);
                        com = clientHandler.getServer().loginClient(name);
                        System.out.println(com);
                        clientHandler.sendMessage(com);
                        break;
                    case HELLO:
                        System.out.println(decode.get(1));
                        com = clientHandler.getServer().greeting();
                        clientHandler.getServer().getViewer().displayServerStatus();
                        clientHandler.sendMessage(com);
                        break;
                    case LIST:
                        com = clientHandler.getServer().sendList();
                        System.out.println(com);
                        clientHandler.sendMessage(com);
                        break;
                    case QUEUE:
                        clientHandler.getServer().addToQueue(clientHandler);
                        clientHandler.getServer().createGame();
                        break;
                    case MOVE:
                        int move = Integer.parseInt(decode.get(1));
                        int rotation = Integer.parseInt(decode.get(2));
                        clientHandler.getServer().makeMove(move, rotation, clientHandler);
                        break;
                    case QUIT:
                        clientHandler.shutDown();
                        break;
                    case PING:
                        clientHandler.getServer().pong(clientHandler);
                        break;
                    case PONG:
                        clientHandler.getServer().ping();
                        break;
                    default:
                        break;
                }
            }

        }
        clientHandler.getServer().removeClient(clientHandler);
    }

    /**
     * Processes commands sent by the connected server.
     * To be used by a client to process commands
     */
    private void receiveMessageFromServer() {
        while (true) {
            String protocolMessage;
            try {
                protocolMessage = reader.readLine();
            } catch (IOException e) {
                System.out.println("Server connection lost :(");
                client.close();
                break;
            }
            if (protocolMessage == null) {
                break;
            }

            List<String> decode = Protocol.decodeProtocolMessage(protocolMessage);
            String command = decode.get(0);
            if (command != null) {
                Protocol.CommandsIdentifier comId = Protocol.CommandsIdentifier.valueOf(command);
                switch (comId) {
                    case LOGIN:
                        client.joinList();
                        break;
                    case HELLO:
                        client.login();
                        break;
                    case ALREADYLOGGEDIN:
                        client.getViewer().announce("It seems such username already taken. " +
                                "Please, choose another one.^^");
                        client.setConnection();
                        break;
                    case LIST:
                        client.joinQueue();
                        break;
                    case NEWGAME:
                        if (decode.get(1).equals(client.getUsername())) {
                            client.setupGame(0);
                        } else if (decode.get(2).equals(client.getUsername())) {
                            client.setupGame(1);
                        }
                        break;
                    case MOVE:
                        client.move(Integer.parseInt(decode.get(1)), Integer.parseInt(decode.get(2)));
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
                        client.quit();
                        client.close();
                        break;
                    case PING:
                        client.pong();
                        break;
                    case PONG:
                        client.ping();
                        break;
                    default:
                        break;

                }
            }
        }

    }

    public void run() {
        if (client != null) {
            receiveMessageFromServer();
        }
        if (clientHandler != null) {
            receiveMessageFromClient();
        }

        try {
            reader.close();
        } catch (IOException e) {
            System.out.println(Protocol.error());
        }
    }
}
