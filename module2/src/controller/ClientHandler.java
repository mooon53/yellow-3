package src.controller;


import src.model.game.GameBoard;
import src.model.game.Mark;

import java.io.*;
import java.net.Socket;

/**
 * ClientHandler of the server that is bounded to a connected client.
 */
public class ClientHandler extends Thread {
    private GameServer server;
    private Socket socket;
    private GameBoard board;
    private String username;
    private Mark mark;
    private BufferedReader reader;
    private PrintStream writer;

    /**
     * Constructor: creates a new ClientHandler bound to the server and a client.
     * @param socket socket of the connected client that this is bounded to
     * @param server which server this belongs to
     */
    public ClientHandler(Socket socket, GameServer server) {
        try {
            this.socket = socket;
            this.server = server;
            this.writer = new PrintStream(getSocket().getOutputStream());
            this.reader = new BufferedReader(new InputStreamReader(getSocket().getInputStream()));
            setupLogic();
        } catch (IOException e) {
            shutDown();
        }
    }

    //getters

    /**
     * Returns the username of the bounded client.
     * @return username
     */
    //@pure;
    public String getUsername() {
        return this.username;
    }

    /**
     * Returns the board state of the bounded client.
     * @return board
     */
    //@pure;
    public GameBoard getBoard() {
        return board;
    }

    /**
     * Returns the mark of the bounded client.
     * @return mark
     */
    //@pure;
    public Mark getMark() {
        return mark;
    }

    /**
     * Returns the socket of the bounded client.
     * @return socket
     */
    //@pure;
    public Socket getSocket() {
        return this.socket;
    }

    /**
     * Returns the server this belongs to.
     * @return server
     */
    //@pure;
    public GameServer getServer() {
        return server;
    }


    //queries

    /**
     * Creates a new Logic Thread and binds it to this.
     */
    private synchronized void setupLogic() {
        try {
            Thread logic = new Logic(this);
            reader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
            new Thread(logic).start();
        } catch (IOException e) {
            System.out.println("Something went wrong when setting up logic");
            shutDown();
        }

    }

    /**
     * Writes a message to the connected socket.
     * @param message String to send
     */
    public void sendMessage(String message) {
        if (message != null) {
            writer.println(message);
            writer.flush();
        }

    }

    /**
     * Sets the board to the given board.
     * @param board new value of board
     */
    public void setBoard(GameBoard board) {
        this.board = board;
    }

    /**
     * Sets the mark to the given mark.
     * @param mark new value of mark
     */
    public void setMark(Mark mark) {
        this.mark = mark;
    }

    /**
     * Sets the username to the given name.
     * @param username new value of username
     */
    public void setUsername(String username) {
        this.username = username;
    }

    /**
     * Shuts down this clientHandler.
     */
    public void shutDown() {
        this.getServer().removeClient(this);
        try {
            socket.close();
            reader.close();
            writer.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
