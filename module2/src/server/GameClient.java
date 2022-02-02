package src.server;

import src.Protocol;
import src.ai.*;
import src.game.GameBoard;
import src.game.HumanPlayer;
import src.game.Mark;
import src.game.Player;
import java.io.IOException;
import java.io.PrintStream;
import java.net.Socket;
import java.util.ArrayList;
import java.util.Scanner;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

public class GameClient extends Thread {
    private Socket socket;
    private PrintStream writer;
    private ArrayList<Player> players;
    private int currentPlayer;
    private int level;
    private String currentBoard;
    private Player player = null;
    private String username;
    private String opponentUsername;
    private GameBoard board;
    private Thread logic;
    private ClientViewer viewer;
    private Game game;
    private Lock lock = new ReentrantLock();

    Scanner scanner = new Scanner(System.in);

    public GameClient() {
        this.viewer = new ClientViewer(this);
        Thread view = new Thread(viewer);
        players = new ArrayList<>();
        view.start();
        this.board = new GameBoard();
        try {
            socket = new Socket(viewer.getInetAddress(), viewer.getPort());
            this.writer = new PrintStream(getSocket().getOutputStream());
            setupLogic();
            setConnection();
        } catch (IOException e) {
           viewer.announce("Unable to join port.");
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

    public int getCurrentPlayer() {
        return currentPlayer;
    }

    //@pure;
    public String getUsername() {
        return username;
    }

    //@pure;
    public String getOpponentUsername() {
        return opponentUsername;
    }

    public String getCurrentBoard() {
        return currentBoard;
    }

    //set player - mark - ID connection
   /* public void setSides() {
        if (this.players.get(0).getName().equals(getUsername())) {
            this.clientID = 0;
            this.opponentUsername = this.players.get(this.clientID).getName();
            this.players.get(0).assignMark(0);
        } else {
            this.clientID = 1;
            this.opponentUsername = this.players.get(this.clientID).getName();
            this.players.get(0).assignMark(1);
        }
    }*/

    public void setOpponentUsername(String opponentUsername) {
        this.opponentUsername = opponentUsername;
        this.getViewer().displayOpponentUsername();
    }

    public void setBoard(String board){
        this.currentBoard = board;
        this.getViewer().displayCurrentBoard();
    }




    public synchronized void setupLogic() {
        Logic logicc = new Logic(this);
        this.logic = new Thread(logicc);
        this.logic.start();
    }


    public synchronized void setConnection() {
        String username = viewer.getClientName();
        int level = viewer.level();
        this.level = level;
        this.username = username;
        greeting(username);
    }



    public synchronized void setupGame(int currentPlayer) {//remove creation of boards for clients and assigning mark
        switch(this.level){
            case 1:
                Strategy strategy = new BasicStrategy();
                player = new ComputerPlayer(strategy, Mark.OO);
                break;
            case 2:
                Strategy strategy1 = new SmartStrategy();
                player = new ComputerPlayer(strategy1, Mark.OO);
                break;
            default:
                player = new HumanPlayer(getUsername(), Mark.OO);
                break;
        }
        player.assignMark(0);
        this.currentPlayer = currentPlayer;
        if (currentPlayer == 0) {
            sendMove();
        }
    }


    public void sendMove() {
        currentPlayer = 0;
        int[] move = player.turn(board);
        String command = Protocol.move(move[0], move[1]);
        writer.println(command);
        writer.flush();
        viewer.announce(board.toString());
    }


    public synchronized void move(int move, int rotation) {
        if (currentPlayer == 0) {
            board.setField(move, player.getMark());
            if (rotation % 2 == 1) { //rotate to the left if rotation is uneven
                board.rotateLeft(rotation / 2);
            } else { //else, rotate to the right
                board.rotateRight(rotation / 2);
            }
            currentPlayer++;
        } else {
            board.setField(move, player.getMark().other());
            if (rotation % 2 == 1) { //rotate to the left if rotation is uneven
                board.rotateLeft(rotation / 2);
            } else { //else, rotate to the right
                board.rotateRight(rotation / 2);
            }
            viewer.announce(board.toString());
            sendMove();
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
        viewer.announce("Play a game? 0-yes 1-no");
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
        viewer.announce("PONG");
    }

    public void run() {
        try {
            this.logic.join();
        } catch (InterruptedException e) {
            viewer.announce("Big oops..");
        }
    }

}




