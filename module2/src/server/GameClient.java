package src.server;

import src.ai.BasicStrategy;
import src.ai.ComputerPlayer;
import src.ai.DumbStrategy;
import src.ai.Strategy;
import src.game.GameBoard;
import src.game.HumanPlayer;
import src.game.Player;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.net.Socket;
import java.util.Scanner;

public class GameClient extends Thread {
    private Socket socket;
    private BufferedReader reader;
    private BufferedWriter writer;
    private Player player;
    private String username;
    private String opponentUsername;
    private int clientID;
    private GameBoard myBoard;
    private Thread logic;
    private GameBoard oppBoard;
    private ClientViewer viewer;

    Scanner scanner = new Scanner(System.in);

    public GameClient(int level, int port) {
        this.viewer = new ClientViewer(this);
        this.myBoard = new GameBoard();
        this.oppBoard = new GameBoard();
        try {
            socket = new Socket("localhost", port);
            if (level == 1) {
                Strategy strategy = new BasicStrategy();
                this.player = new ComputerPlayer(strategy);
            } else if (level == 2) {
                Strategy strategy = new DumbStrategy();
                this.player = new ComputerPlayer(strategy);
            } else {
                setUsername();
                this.player = new HumanPlayer(this.username);
            }
        } catch (IOException e) {
            System.out.println("Unable to join port.");
        }
        this.setupLogic();
    }

    //getters
    //@pure;
    public Socket getSocket() {
        return socket;
    }

    //@requires player!=null;
    //@pure;
    public Player getPlayer() {
        return this.player;
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

    //commands related connection
    public void successConnection(String state) {
        viewer.checkConnection();
        viewer.announce(state);
    }

    public void failedConnection(String state) {
        viewer.checkConnection();
        viewer.announce(state);
        this.username = "-";
    }

    public void setSides(String[] users) {
        if (users[0].equals(getUsername())) {
            this.clientID = 1;
            this.opponentUsername = users[1];
        } else {
            this.clientID = 2;
            this.opponentUsername = users[0];
        }
    }

    public void setMove(int currentPlayer) {
        if (currentPlayer == clientID) {
            boolean run = true;
            int moveIndex = -1;
            int rotation;
            moveIndex = player.chooseMove(getMyBoard());
            rotation = player.chooseRotation(getMyBoard());

            if (moveIndex != -1 && this.player instanceof ComputerPlayer) {
                try {
                    Thread.sleep(200);
                } catch (InterruptedException e) {
                    e.printStackTrace();
                }
                getMyBoard().updateBoard(rotation);
                printBoard();
            }
        }

    }

    public void printBoard() {
        myBoard.toString();
    }


    public void endGame(int winnerID) {
        if (winnerID == clientID) {
            System.out.println("Congrats! You are the king of pentago!");
        } else {
            System.out.println("Sorry, you lose this time ((");
        }
    }

    public void setupLogic() {
        this.logic = new Logic(this);
        new Thread(logic).start();
    }


    public void setUsername() {
        System.out.println("Enter your username: ");
        this.username = scanner.nextLine();
    }


    public void run() {
        try {
            this.logic.join();
        } catch (InterruptedException e) {
            System.out.println("Big oops..");
        }
    }
}




