package src.server;



import src.game.GameBoard;
import src.game.Mark;

import java.io.*;
import java.net.Socket;

public class ClientHandler extends Thread {
    private GameServer server;
    private Socket socket;
    private String username;
    private Mark mark;
    private Game game;
    private BufferedReader reader;
    private BufferedWriter writer;
    private Thread logic;

    public ClientHandler(Socket socket, GameServer server) {
        try {
            this.socket = socket;
            this.reader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
            this.server = server;
            this.writer = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
            logic = new Logic(this);
            new Thread(this.logic).start();
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
    public void connect(String username) {
        if (username != null) {
            this.username = username;
            String msg = "New player connected";
            this.announce(msg);
        } else{
            String msg = "Invalid username.";
            this.announce(msg);
        }
    }
    public void announce(String msg){
        if(this.writer != null){
            try {
                this.writer.write(msg);
                this.writer.flush();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }

    public void play() {
        server.createGame(this);
    }

    public void makeMove(int index) {
        if(this.game.gameOver() == false){
            int player = this.game.getIndexOfCurrentPlayer();
            GameBoard currentBoard = this.game.getBoard();
            currentBoard.setField(index, getMark());
            this.game.next();
        }


    }

    public void setMark(int index) {
        if (index == 1) {
            this.mark = Mark.XX;
        } else {
            this.mark = Mark.OO;
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

    public void run(){
        try {
            this.logic.join();
        } catch (InterruptedException e) {
        }
    }

}
