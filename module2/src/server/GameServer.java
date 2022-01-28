package src.server;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;

public class GameServer implements Server {
    private ArrayList<ClientHandler> clientHandlers;//list of clientHandlers from server
    private ServerSocket serverSocket;
    private ServerViewer viewer;

    public GameServer(ServerSocket serverSocket){
        clientHandlers = new ArrayList<>();
        setViewer();
        System.out.println("_____Pentago Server_____");
        this.serverSocket = serverSocket;
        this.getViewer().announce("Connected to port: "+ serverSocket.getLocalPort());
    }

    //getters
    //@requires clientHandlers.size()!=0;
    //@pure;
    public ArrayList<ClientHandler> getClientHandlers() {
        return this.clientHandlers;
    }

    //@pure;
    public ServerSocket getServerSocket() {
        return serverSocket;
    }
    //@pure;
    public ServerViewer getViewer() {
        return viewer;
    }

    @Override
    public void connect() {
        try {
            System.out.println("Waiting for players...");

            while (this.clientHandlers.size() < 2) {
                Socket socket = this.serverSocket.accept();
                ClientHandler ch = new ClientHandler(socket, this);
                this.clientHandlers.add(ch);
                ch.setMark(clientHandlers.size());
                System.out.println("Players connected: " + this.clientHandlers.size());
                //System.out.println(ch.getMark().toString());
                (new Thread(ch)).start();

            }

            System.out.println("Game is full.");
        } catch (IOException var3) {
            System.out.println("Oops, unable to establish connection.");
            this.stop();
        }

    }


    public void removeClient(ClientHandler clientHandler){
        String msg = clientHandler.getUsername() + "left the game";
        this.getViewer().announce(msg);
        this.clientHandlers.remove(clientHandler);
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
            newGame = new Game(clientHandler);
        } else{
            System.out.println("Unable to create game.");
            stop();
        }
        return newGame;
    }

    public void setViewer(){
        this.viewer = new ServerViewer(this);
        new Thread(this.viewer).start();
    }

    public void run(){
        connect();
    }

}
