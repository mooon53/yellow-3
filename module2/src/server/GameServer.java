package src.server;

import src.Protocol;
import src.game.HumanPlayer;
import src.game.Mark;
import src.game.Player;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.Collection;

public class GameServer extends Thread implements Server{
    private ArrayList<ClientHandler> clientHandlers;//list of clientHandlers from server QUEUE
    private ServerSocket serverSocket;
    private ServerViewer viewer;
    private ArrayList<Game> games;
    private String username;
    private Mark mark;
    private Game game;
    private Socket socket;
    private ArrayList<ClientHandler> queue;
    private ArrayList<String> loggedPlayers = new ArrayList<>();
    private ArrayList<Player> players = new ArrayList<>();
    ;

    public GameServer(int port) {
        try {
            clientHandlers = new ArrayList<>();
            games = new ArrayList<>();
            queue = new ArrayList<>();
            setViewer();
            System.out.println("_____Pentago Server_____");
            this.serverSocket = new ServerSocket(port);
            this.getViewer().announce("Connected to port: " + serverSocket.getLocalPort());
            this.getViewer().displayServerStatus();
        } catch (IOException e) {
            System.out.println(Protocol.error("Unable to set connection"));
            this.stop();
        }

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

    public Socket getSocket() {
        return this.socket;
    }

    @Override
    public synchronized void connect() {


    }

    public void addClientHandler(ClientHandler clientHandler) {
        this.clientHandlers.add(clientHandler);
        getViewer().displayServerStatus();
    }


    public void removeClient(ClientHandler clientHandler) {
        this.clientHandlers.remove(clientHandler);
    }

    @Override
    public int getPort() {
        return this.serverSocket.getLocalPort();
    }


    public ArrayList<ClientHandler> getQueue() {
        return queue;
    }

    public void setViewer() {
        this.viewer = new ServerViewer(this);
        new Thread(this.viewer).start();
    }

    public synchronized String loginClient(String username) {
        String command = null;
        if (availableUsername(username)) {
            loggedPlayers.add(username);
            this.username = username;
            command = Protocol.login();
        } else {
            String no = "choose another username";
            System.out.println(no);
            command = Protocol.alreadyLoggedIn();
        }
        if (clientHandlers.size() > 1) {
            notify();
        }
        return command;
    }

    public synchronized String addToQueue(ClientHandler clientHandler) {
        String command = null;
        int state = this.getQueue().size();
        if (state == 0) {
            this.queue.add(clientHandler);
            state++;
            command = (Protocol.queue());
        } else if (state == 1) {
            queue.add(clientHandler);
            for (ClientHandler ch : this.queue) {
                Player player = new HumanPlayer(ch.getUsername());
                players.add(player);
                sendList();
                state++;
            }
            if (players.size() == 2) {
                this.createGame();
            } else {
                try {
                    System.out.println("WAAAAITING");
                    this.wait();

                } catch (InterruptedException e) {
                    System.out.println(Protocol.error("Waiting interrupted"));
                }
            }
        }
        return command;
    }

    public synchronized String createGame() {
        game = new Game(players.get(0), players.get(1));
        players.get(0).setMark(0);
        players.get(1).setMark(1);
        String command = Protocol.newGame(players.get(0).getName(), players.get(1).getName());
        players.remove(0);
        players.remove(1);
        this.getClientHandlers().clear();
        return command;
    }

    public synchronized String greeting(String username) {
        String command = Protocol.greeting(username.replace("Client by ", "Server by "));//Server by Name
        return command;
    }

    public String quit() {
        this.stop();
        String command = Protocol.quit();
        return command;

    }


    public boolean availableUsername(String username) {
        boolean is = true;
        if (!this.getClientHandlers().isEmpty()) {
            for (ClientHandler clientHandler : this.getClientHandlers()) {
                if (clientHandler.getUsername() != null && !clientHandler.getUsername().equals("") && clientHandler.getUsername().equals(username)) {
                    is = false;
                }
            }
        }
        return is;
    }

    public synchronized String sendList() {
        String command = Protocol.list(loggedPlayers);
        return command;
    }

    public void ping() {
        System.out.println("PING");
    }

    public void pong() {
        System.out.println("PONG");
    }


    public ArrayList<Game> getGames() {
        return this.games;
    }
    public void run(){
        try{
            while (true){
                Socket sock = serverSocket.accept();
                ClientHandler handler = new ClientHandler(sock, this);
                this.addClientHandler(handler);
            }

        } catch (IOException e){
            System.out.println(e.getMessage());
        }
    }

    public void removeGame(Game game) {
    }
}
