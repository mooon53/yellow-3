package src.server;


import java.io.*;
import java.net.Socket;
import java.nio.CharBuffer;
import java.util.ArrayList;

public class ClientHandler implements Runnable {
    private Socket socket;
    private Server server;
    private BufferedReader reader;
    private BufferedWriter writer;
    private int playerID;
    private String username;


    public ArrayList<ClientHandler> clientHandlers = new ArrayList<>();


    public ClientHandler(Socket socket, Server server, int playerID) {
        try {
            this.socket = socket;
            this.reader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
            this.server = server;
            this.writer = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
            this.playerID = playerID;
            clientHandlers.add(this);
        } catch (IOException e) {
            close();
        }
    }

    @Override
    public void run() {
        try {
            writer.write(playerID);
            writer.flush();
            //game connection

        } catch (IOException e) {
            close();
        }
    }

    public void announceMessage(String message) {
        for (ClientHandler clientHandler : clientHandlers) {
            try {
                if (clientHandler.playerID != playerID) {
                    clientHandler.writer.write(message);
                    clientHandler.writer.newLine();
                    clientHandler.writer.flush();
                }
            } catch (IOException e) {
                close();
            }
        }
    }

    public void removeClientHandler() {
        clientHandlers.remove(this);
        announceMessage("" + playerID + " left game.");
    }

    public void close() {
        try {
            if (socket != null && reader != null && writer != null) {
                removeClientHandler();
                socket.close();
                reader.close();
                writer.close();
            }
        } catch (IOException e) {
            e.printStackTrace();
        }

    }
}
