package src.server;

import src.Protocol;
import src.ai.ComputerPlayer;
import src.game.GameBoard;
import src.game.HumanPlayer;
import src.game.Mark;
import src.game.Player;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.PrintStream;
import java.net.Socket;
import java.util.ArrayList;
import java.util.Scanner;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

public class GameClient extends Thread {
    private Lock lock = new ReentrantLock();
    private Socket socket;
    private BufferedReader reader;
    private PrintStream writer;
    private ArrayList<Player> players;

    private ComputerPlayer cp = null;
    private String username;
    private String opponentUsername;
    private int clientID;
    private GameBoard myBoard;
    private Thread logic;
    private ClientViewer viewer;
    private Game game;

    Scanner scanner = new Scanner(System.in);

    public GameClient() {
        this.viewer = new ClientViewer(this);
        Thread view = new Thread(viewer);
        players = new ArrayList<>();
        view.start();
        this.myBoard = new GameBoard();
        try {
            socket = new Socket("localhost", viewer.getPort());
            this.writer = new PrintStream(getSocket().getOutputStream());
            setupLogic();
            setConnection();
        } catch (IOException e) {
            System.out.println("Unable to join port.");
            Protocol.quit();
        }

    }

    //getters
    //@pure;
    public Socket getSocket() {
        return socket;
    }

    public ClientViewer getViewer() {
        return viewer;
    }

    public ArrayList<Player> getPlayers() {
        return players;
    }

    //@pure;
    public String getUsername() {
        return username;
    }

    //@pure;
    public String getOpponentUsername() {
        return opponentUsername;
    }

    //@pure;
    public GameBoard getMyBoard() {
        return myBoard;
    }

    //@pure;
    public int getClientID() {
        return clientID;
    }

    //@pure;
    public Thread getLogic() {
        return this.logic;
    }

    //set player - matk - ID connection
    public void setSides() {
        if (this.players.get(0).getName().equals(getUsername())) {
            this.clientID = 0;
            this.opponentUsername = this.players.get(this.clientID).getName();
            this.players.get(0).assignMark(0);
        } else {
            this.clientID = 1;
            this.opponentUsername = this.players.get(this.clientID).getName();
            this.players.get(0).assignMark(1);
        }
    }

    public void setOpponentUsername(String opponentUsername) {
        this.opponentUsername = opponentUsername;
        this.getViewer().displayOpponentUsername();
    }


    public void sendMove(int currentPlayer) {
        int[] position = null;
        if (currentPlayer == clientID) {
            position = this.players.get(currentPlayer).turn(this.myBoard);
            String command = Protocol.move(position[0], position[1]);
            writer.println(command);
            writer.flush();
        }
        if (position != null && cp != null) {
            try {
                Thread.sleep(200);
            } catch (InterruptedException e) {
                System.out.println(Protocol.error());
            }
        }

    }

    public void printBoard() {
        myBoard.toString();
    }

    public synchronized void setupLogic() {
        Logic logicc = new Logic(this);
        this.logic = new Thread(logicc);
        this.logic.start();
    }


    public synchronized void setConnection() {
        String username = viewer.getClientName();
        this.username = username;
        login();


    }

    public synchronized void setupGame() {
        Player player1 = new HumanPlayer(getUsername());
        player1.assignMark(0);
        Mark mark1 = player1.getMark();
        this.players.add(player1);
        Player player2 = new HumanPlayer(getOpponentUsername());
        this.players.add(player2);
        player2.assignMark(1);
        Mark mark2 = player2.getMark();
        this.game = new Game(player1, player2);
        System.out.println("CHEKK: "+player1.getName()+mark1);
        System.out.println("CHEKK: "+player2.getName()+mark2);
        sendTurn(player1.getName());
    }

    public synchronized void sendTurn(String username) {
        String com = Protocol.sendTurn(username);
        writer.println(com);
        writer.flush();

    }

    public synchronized void move(String uname) {
        String com = null;
        if (!game.gameOver()) {
            if (players.get(0).getName().equals(uname)) {
                int[] move = players.get(0).turn(game.getBoard());
                com = Protocol.move(move[0], move[1]);
                writer.println(com);
                writer.flush();
                game.update();
                game.printBoard();
                game.next();
                game.gameOver();

            }
        } else {
            com = Protocol.quit();
            writer.println(com);
            writer.flush();
        }
    }

    //logic queries
    public synchronized void greeting(String name) {
        String command = Protocol.greeting("Client by "+name);
        writer.println(command);
        writer.flush();
    }

    public synchronized void login() {
        String command = Protocol.login(this.username);
        writer.println(command);
        writer.flush();
    }

    public void quit() {
        viewer.endGame(getOpponentUsername() + " left.");
        String command = Protocol.quit();
        writer.println(command);
        writer.flush();
    }

    public synchronized void joinList() {
        String command = Protocol.list();
        writer.println(command);
        writer.flush();
    }

    public synchronized void joinQueue() {
        System.out.println("Play a game? 0-yes 1-no");
        int choice = Integer.parseInt(scanner.next());
        if (choice == 0) {
            String command = Protocol.queue();
            writer.println(command);
            writer.flush();
        } else if (choice == 1) {
            String command = Protocol.quit();
            writer.println(command);
            writer.flush();
        }
    }

    public void ping() {
        String command = Protocol.ping();
        writer.println(command);
        writer.flush();
    }

    public void pong() {
        System.out.println("PONG");
    }

    public void run() {
        try {
            this.logic.join();
        } catch (InterruptedException e) {
            System.out.println("Big oops..");
        }
    }

}




