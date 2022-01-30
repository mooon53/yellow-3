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

public class GameServer extends Thread implements Server {
    private ArrayList<ClientHandler> clientHandlers;//list of clientHandlers from server QUEUE
    private ServerSocket serverSocket;
    private ServerViewer viewer;
    private ArrayList<Game> games = new ArrayList<>();
    private String username;
    private Mark mark;
    private Game game;
    private Socket socket;
    private ArrayList<ClientHandler> queue;
    private ArrayList<String> loggedPlayers = new ArrayList<>();
    private ArrayList<Player> players = new ArrayList<>();


    public GameServer(int port) {
        try {
            clientHandlers = new ArrayList<>();
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

    public Game getGame(String username) {
        Game giveGame = null;
        for (Game game : this.getGames()) {
            for (Player player : game.getPlayers()) {
                if (username.equals(player.getName())) {
                    return giveGame = game;
                }
            }
        }
        return giveGame;
    }

    @Override
    public synchronized void connect() {


    }

    public void addClientHandler(ClientHandler clientHandler) {
        this.clientHandlers.add(clientHandler);
        getViewer().displayServerStatus();
    }


    public String removeClient(ClientHandler clientHandler) {
        this.clientHandlers.remove(clientHandler);
        return Protocol.gameover("DISCONNECT");
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
            command = Protocol.alreadyLoggedIn();
            loggedPlayers.remove(loggedPlayers.size()-1);
        }
        if (clientHandlers.size() > 1) {
            notify();
        }
        return command;
    }

    public synchronized void addToQueue(ClientHandler clientHandler) {
        int state = this.getQueue().size();
        if (state == 0) {
            this.queue.add(clientHandler);
            state++;
        } else if (state == 1) {
            queue.add(clientHandler);
            for (ClientHandler ch : this.queue) {
                Player player = new HumanPlayer(ch.getUsername(), false);
                players.add(player);
                sendList();
                state++;
            }
        }
    }

    public String createGame() {
        String command = null;
        if (players.size() == 2) {
            game = new Game(players.get(0), players.get(1));
            games.add(game);
            viewer.displayServerStatus();
            players.get(0).setMark(0);
            players.get(1).setMark(1);

            command = Protocol.newGame(players.get(0).getName(), players.get(1).getName());


            for (ClientHandler clientHandler : queue) {
                clientHandler.sendMessage(command);
            }
            players.remove(1);
            players.remove(0);
            this.queue.clear();
            return command;
        }
        return command;
    }

    public synchronized String[] getTurnByName(ArrayList<Player> parr) {
        String[] com = new String[2];
        for (Game game : getGames()) {
            if (game.getPlayers().equals(parr)) {
                String curPlayer = game.getPlayer().getName();
                com[0] = curPlayer;
                String waitingPlayer;
                for (String name : game.getUsernames()) {
                    if (!name.equals(curPlayer)) {
                        waitingPlayer = name;
                        com[1] = waitingPlayer;
                    }
                }
            }
        }
        return com;
    }

    public synchronized String setMoveByName(String username) {
        String turnByProtocol = null;
        if (getGame(username) != null && getGame(username).getPlayers().get(0).getName().equals(username)) {
            turnByProtocol = Protocol.sendTurn((getTurnByName(getGame(username).getPlayers()))[1]);
        } else {
            turnByProtocol = Protocol.sendTurn((getTurnByName(getGame(username).getPlayers()))[0]);
        }
        return turnByProtocol;
    }

    public synchronized void sendTurn(String username) {
        for (ClientHandler ch : queue) {
            System.out.println(ch.getUsername()+" ppppp");
            if(ch.getUsername().equals(username)){
                ch.sendMessage(setMoveByName(ch.getUsername()));
            }
        }
    }

    public synchronized String move(int move, int rotation) {
        String command = null;
        int yourTurn = 0;
        for (ClientHandler clientHandler : clientHandlers) {
            clientHandler.makeMove(move, rotation);
            command = Protocol.move(move, rotation);
            if (yourTurn == 0) {
                yourTurn = 1;
            } else {
                yourTurn = 0;
            }
        }
        return command;
    }

    public synchronized String greeting(String username) {
        this.username = username.replace("Client by ", "");
        clientHandlers.get(clientHandlers.size() - 1).setUsername(this.username);
        String command = Protocol.greeting(username.replace("Client by ", "Server by "));//Server by Name
        return command;
    }



    public boolean availableUsername(String username) {
        boolean is = true;
        if (!this.getClientHandlers().isEmpty()) {
            for (String player : this.loggedPlayers) {
                if (player != null && !player.equals("") && player.equals(username)) {
                    is = false;
                }
            }
        }
        return is;
    }

    public synchronized String sendList() {
        String command = Protocol.list(loggedPlayers);
        viewer.displayServerStatus();
        return command;
    }

    public String ping() {
        return Protocol.ping();
    }

    public void pong() {
        System.out.println("PONG");
    }


    public ArrayList<Game> getGames() {
        return this.games;
    }

    public void run() {
        try {
            while (true) {
                Socket sock = serverSocket.accept();
                ClientHandler handler = new ClientHandler(sock, this);
                this.addClientHandler(handler);
            }

        } catch (IOException e) {
            System.out.println(e.getMessage());
        }
    }

    public void removeGame(Game game) {
    }
}
