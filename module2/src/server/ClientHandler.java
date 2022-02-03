package src.server;


import src.game.GameBoard;
import src.game.Mark;

import java.io.*;
import java.net.Socket;


public class ClientHandler extends Thread {
    private GameServer server;
    private Socket socket;
    private GameBoard board;
    private String username;
    private Mark mark;
    private BufferedReader reader;
    private PrintStream writer;


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

    //@pure;
    public String getUsername() {
        return this.username;
    }

    //@pure;
    public GameBoard getBoard() {
        return board;
    }

    //@pure;
    public Mark getMark() {
        return mark;
    }

    //@pure;
    public Socket getSocket() {
        return this.socket;
    }

    //@pure;
    public GameServer getServer() {
        return server;
    }


    //queries


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

    public void sendMessage(String message) {
        if (message != null) {
            writer.println(message);
            writer.flush();
        }

    }

    public void setBoard(GameBoard board) {
        this.board = board;
    }

    public void setMark(Mark mark) {
        this.mark = mark;
    }

    public void setUsername(String username) {
        this.username = username;
    }


    public void shutDown() {
        this.getServer().removeClient(this);
        try {
            if (socket != null && reader != null && writer != null) {
                socket.close();
                reader.close();
                writer.close();
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
