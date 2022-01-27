package src.server;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;

public class GameServer implements Server {
    private ArrayList<ClientHandler> clientHandlers = new ArrayList<>();//list of clientHandlers from server
    private ArrayList<Game> games = new ArrayList<>(); //list of active games
    private ServerSocket serverSocket;

    public GameServer(ServerSocket serverSocket){
        System.out.println("_____Pentago Server_____");
        this.serverSocket = serverSocket;
        System.out.println("Connection opened at port: "+serverSocket.getLocalPort());

    }

    //getters
    //@requires clientHandlers.size()!=0;
    //@pure;
    public ArrayList<ClientHandler> getClientHandlers() {
        return this.clientHandlers;
    }

    //@requires games.size()!=0;
    //@pure;
    public ArrayList<Game> getGames() {
        return this.games;
    }


    @Override
    public void connect() {
        try {
            System.out.println("Waiting for players...");

            while (this.clientHandlers.size() < 2) {
                Socket socket = this.serverSocket.accept();
                ClientHandler ch = new ClientHandler(socket, this);
                this.clientHandlers.add(ch);
                System.out.println("Players connected: " + this.clientHandlers.size());
                (new Thread(ch)).start();

            }

            System.out.println("Game is full.");
        } catch (IOException var3) {
            System.out.println("Oops, unable to establish connection.");
            this.stop();
        }

    }

    @Override
    public int getPort() {
        return this.serverSocket.getLocalPort();
    }

    @Override
    public void stop() {
        try {
            if (this.serverSocket != null) {
                this.serverSocket.close();
            }
        } catch (IOException var2) {
            var2.printStackTrace();
        }
    }

    public Game createGame(ClientHandler clientHandler){
        Game newGame = null;
        if(clientHandler!=null){
            newGame = new Game(2,clientHandler);
            games.add(newGame);
        } else{
            System.out.println("Unable to create game.");
            stop();
        }
        return newGame;
    }
}
