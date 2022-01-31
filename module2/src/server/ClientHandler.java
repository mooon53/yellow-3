package src.server;


import src.Protocol;
import src.game.GameBoard;
import src.game.HumanPlayer;
import src.game.Mark;
import src.game.Player;

import java.io.*;
import java.net.Socket;


public class ClientHandler extends Thread {
    private GameServer server;
    private Socket socket;
    private Game game;
    private String username;
    private Mark mark;
    private BufferedReader reader;
    private PrintStream writer;
    private Thread logic;
    private int clienthandlerID;
    private boolean yourTurn = true;


    public ClientHandler(Socket socket, GameServer server) {
        try {
            this.socket = socket;
            this.server = server;
            this.writer = new PrintStream(getSocket().getOutputStream());
            this.reader = new BufferedReader(new InputStreamReader(getSocket().getInputStream()));
            this.setupLogic();
        } catch (IOException e) {
            close();
        }
    }

    //getters

    //@pure;
    public String getUsername() {
        return this.username;
    }

    public void setUsername(String username) {
        this.username = username;
    }

    //@pure;
    public Game getGame() {
        return game;
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
    public Thread getLogic() {
        return logic;
    }

    //@pure;
    public GameServer getServer() {
        return server;
    }


    //queries


    public synchronized void setupLogic() {
        try {
            logic = new Logic(this);
            this.reader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
            new Thread(this.logic).start();
        } catch (IOException e) {
            e.printStackTrace();
        }

    }

    public void sendMessage(String message) {
        if (message != null) {
            writer.println(message);
            writer.flush();
        }

    }





    public void close() {
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




    public void shutDown() {
        if (this.getGame() != null) {
            //this.getGame().endDisconnect();
            this.getServer().removeGame(this.getGame());
        }
        if (this.getUsername() != null) {
            this.getServer().removeClient(this);
        }
        close();
    }


}
