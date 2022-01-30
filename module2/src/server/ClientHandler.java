package src.server;


import src.Protocol;
import src.game.GameBoard;
import src.game.HumanPlayer;
import src.game.Mark;
import src.game.Player;

import java.io.*;
import java.net.Socket;
import java.util.ArrayList;
import java.util.Random;
import java.util.function.DoubleToIntFunction;

public class ClientHandler extends Thread {
    private GameServer server;
    private Socket socket;
    private Game game;
    private String username;
    private Mark mark;
    private BufferedReader reader;
    private PrintStream writer;
    private Thread logic;


    public ClientHandler(Socket socket, GameServer server) {
        try {
            this.socket = socket;
            this.server = server;
            this.writer = new PrintStream(getSocket().getOutputStream());
            this.setupLogic();
        } catch (IOException e) {
            close();
        }
    }

    //getters

    //@pure;
    public String getUsername() {
        return username;
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



    public synchronized void setupLogic(){
        try {
            logic = new Logic(this);
            this.reader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
            new Thread(this.logic).start();
        } catch (IOException e) {
            e.printStackTrace();
        }

    }

    public void sendMessage(String message){
        if(message!=null){
            writer.println(message);
            writer.flush();}

    }

    public void announce(String msg) {
        if (this.writer != null) {

            this.writer.println(msg);
            this.writer.flush();
        }
    }


    public void makeMove(int index, int rotation) {
        if (this.game.gameOver() == false) {
            int player = this.game.getIndexOfCurrentPlayer();
            GameBoard currentBoard = this.game.getBoard();
            currentBoard.setField(index, getMark());
            int choice = encodeRotation(rotation)[0];
            int side = encodeRotation(rotation)[1];
            if (side == 0) {
                this.game.getBoard().rotateRight(choice);
            } else if (side == 1) {
                this.game.getBoard().rotateLeft(choice);
            }
            this.game.next();
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



    public int[] encodeRotation(int index) {
        int[] result = new int[2];
        switch (index) {
            case 0:
                result[0] = 0;
                result[1] = 0;
                break;
            case 1:
                result[0] = 0;
                result[1] = 1;
                break;
            case 2:
                result[0] = 1;
                result[1] = 0;
                break;
            case 3:
                result[0] = 1;
                result[1] = 1;
                break;
            case 4:
                result[0] = 2;
                result[1] = 0;
                break;
            case 5:
                result[0] = 2;
                result[1] = 1;
                break;
            case 6:
                result[0] = 3;
                result[1] = 0;
                break;
            case 7:
                result[0] = 3;
                result[1] = 1;
                break;
        }
        return result;
    }

    public void shutDown() {
        if (this.getGame() != null) {
            //this.getGame().endDisconnect();
            this.getServer().removeGame(this.getGame());
        }
        if (this.getUsername() != null) {
            writer.close();
            this.getServer().removeClient(this);
        }
    }


}
