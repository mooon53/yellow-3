package src.server;

import src.Protocol;
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
import java.io.PrintStream;
import java.net.Socket;
import java.util.Scanner;

public class GameClient extends Thread {
    private Socket socket;
    private BufferedReader reader;
    private PrintStream writer;
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
            this.writer = new PrintStream(getSocket().getOutputStream());
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
        this.setupGame();
    }

    public void failedConnection(String state) {
        viewer.checkConnection();
        viewer.announce(state);
        this.username = "-";
        this.setConnection();
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


    public void sendMove(int currentPlayer) throws IOException {
        int[] position=null;
        if (currentPlayer == clientID) {
            position = this.getPlayer().turn(this.myBoard);
            String command = Protocol.move(position[0], position[1], position[2]);
            writer.println(command);
            writer.flush();
        }
        if(position!=null && this.player instanceof ComputerPlayer){
            try{
                Thread.sleep(200);
            } catch (InterruptedException e) {
                System.out.println(Protocol.error());
            }
        }

    }

    public void printBoard() {
        myBoard.toString();
    }


    public void endGame(int winnerID) {
        String reason;
        if (winnerID == clientID) {
            viewer.endGame(getUsername(), "WINNER");
        } else if(myBoard.isFull()){
            viewer.endGame(getUsername(),"DRAW");
        }
    }

    public void setupLogic() {
        this.logic = new Logic(this);
        new Thread(logic).start();
    }


    public void setUsername() {
        System.out.println(">Enter your username: ");
        this.username = scanner.nextLine();
    }

    public void setConnection(){
        String username = viewer.getClientName();
        this.username = username;
        String command = Protocol.login(username);
        writer.println(command);
        writer.flush();
    }

    public void setupGame(){
        int size = 2;
        String command = Protocol.newGame(getUsername(), getOpponentUsername());
        writer.println(command);
        writer.flush();
    }


    public void run() {
        try {
            this.logic.join();
        } catch (InterruptedException e) {
            System.out.println("Big oops..");
        }
    }
}




