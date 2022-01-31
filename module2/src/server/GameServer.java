package src.server;

import src.Protocol;
import src.game.HumanPlayer;
import src.game.Mark;
import src.game.Player;

import java.io.IOException;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

public class GameServer extends Thread implements Server {
    private ArrayList<ClientHandler> clientHandlers;
    private ServerSocket serverSocket;
    private ServerViewer viewer;
    private ArrayList<Game> games = new ArrayList<>();
    private String username;
    private Mark mark;
    private Game game;
    private Socket socket;
    private Player currentPlayer;
    private ArrayList<ClientHandler> queue;
    private ArrayList<String> loggedPlayers = new ArrayList<>();
    private Map<Player, Mark> players = new HashMap<Player, Mark>();
    private ArrayList<Player> playerSet = new ArrayList<>();
    private int turn = 0;


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
        return Protocol.gameover("DISCONNECT", clientHandlers.get(0).getUsername());
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
            clientHandlers.get(clientHandlers.size() - 1).setUsername(username);
            loggedPlayers.add(username);
            this.username = username;
            command = Protocol.login();
        } else {
            command = Protocol.alreadyLoggedIn();
            loggedPlayers.remove(loggedPlayers.size() - 1);
        }
        return command;
    }

    public synchronized void addToQueue(ClientHandler clientHandler) {
        int state = this.getQueue().size();
        int id = 0;
        if (state == 0) {
            this.queue.add(clientHandler);
            state++;
        } else if (state == 1) {
            queue.add(clientHandler);
            for (ClientHandler ch : this.queue) {
                Player player = new HumanPlayer(ch.getUsername());
                playerSet.add(player);
                player.assignMark(id);
                id = 1;
                players.put(player, player.getMark());
                sendList();
                state++;
            }

        }
    }

    public String createGame() {
        String command = null;
        if (queue.size() == 2) {
            game = new Game(playerSet.get(0), playerSet.get(1));
            games.add(game);
            viewer.displayServerStatus();
            command = Protocol.newGame(playerSet.get(0).getName(), playerSet.get(1).getName());
            for (ClientHandler clientHandler : queue) {
                clientHandler.sendMessage(command);
            }
            this.queue.clear();
            return command;
        }
        return command;
    }

    public String makeMove(int index, int rotation, String user) {
        for (Player player : players.keySet()) {
            if (player.getName().equals(user)) {
                currentPlayer = player;
            }
        }
        this.game.getBoard().setField(index, players.get(currentPlayer));
        int choice = encodeRotation(rotation)[0];
        int side = encodeRotation(rotation)[1];
        if (side == 0) {
            this.game.getBoard().rotateRight(choice);
        } else if (side == 1) {
            this.game.getBoard().rotateLeft(choice);
        }
        System.out.println(this.game.getBoard().toString());
        String command = Protocol.move(index, rotation);
        //the move is done, now we check if the game has ended
        if (game.getBoard().isFull() || game.getBoard().isWinner(Mark.XX) || game.getBoard().isWinner(Mark.OO)){
            String gameOver;
            String winner = null;
            if (game.getBoard().isWinner(Mark.XX)) {
                for (Player player : players.keySet()) {
                    if (players.get(player) == Mark.XX) {
                        winner = player.getName();
                    }
                }
                gameOver = Protocol.gameover("VICTORY", winner);
            } else if (game.getBoard().isWinner(Mark.OO)) {
                for (Player player : players.keySet()) {
                    if (players.get(player) == Mark.OO) {
                        winner = player.getName();
                    }
                }
                gameOver = Protocol.gameover("VICTORY", winner);
            } else {
                gameOver = Protocol.gameover("DRAW", winner);
            }
            for (ClientHandler clientHandler : clientHandlers) { //should actually be currentPlayers only
                clientHandler.sendMessage(gameOver);
            }
            games.remove(game); //not sure if needed
        }
        for (ClientHandler clientHandler : clientHandlers) { //should actually be currentPlayers only
            clientHandler.sendMessage(command);
        }
        return command;
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

    public synchronized String sendTurn(String username) {
        String com = null;
        for (Player player : this.playerSet) {
            if (player.getName().equals(username) && players.get(player).equals(Mark.XX)) {
                com = Protocol.sendTurn();
                this.currentPlayer = player;
            } else if (player.getName().equals(username)&& players.get(player).equals(Mark.OO)) {
                com = Protocol.sendTurn();
                this.currentPlayer = player;
                this.turn = 0;
            }
        }
        return com;
    }

  /*  public synchronized String move(int move, int rotation) {
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
    }*/

    public synchronized String greeting(String username) {
        this.username = username.replace("Client by ", "");
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
