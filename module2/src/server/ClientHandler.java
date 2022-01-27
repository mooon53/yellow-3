package src.server;



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

    public ClientHandler(Socket socket, GameServer server) {
        try {
            this.socket = socket;
            this.reader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
            this.server = server;
            this.writer = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
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

    //queries
    public void connect(String username) {
        if (username != null) {
            this.username = username;
            System.out.println("New player connected");
        }
    }

    public void play() {
        server.createGame(this);
    }

    public void makeMove(int index) {

    }

    public void setMark(int index) {
        if (index == 0) {
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

}
