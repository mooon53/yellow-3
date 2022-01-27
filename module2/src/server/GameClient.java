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
import java.net.UnknownHostException;
import java.util.Scanner;

public class GameClient extends Thread {
    private Socket socket;
    private BufferedReader reader;
    private BufferedWriter writer;
    private Player player;
    private String username;
    private String opponentUsername;
    private int clientID;
    private GameBoard board;

    Scanner scanner = new Scanner(System.in);

    public GameClient(int level) {
        this.board = new GameBoard();
        if(level ==1){
            Strategy strategy = new BasicStrategy();
            this.player = new ComputerPlayer(strategy);
        } else if(level == 2){
            Strategy strategy = new DumbStrategy();
            this.player = new ComputerPlayer(strategy);
        } else{
            setUsername();
            this.player = new HumanPlayer(this.username);
        }
        connectGame();
    }

    //getters
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
    public GameBoard getBoard() {
        return board;
    }
    //@pure;
    public int getClientID() {
        return clientID;
    }

    //commands
    public void startGame(String[] users){}
    public void getMove(int currentPlayer){}
    public void setMove(int index){}
    public void setUsername(){
        System.out.println("Enter your username: ");
        this.username = scanner.nextLine();
    }
    public void connectGame(){
        try {
            System.out.println("Join port: ");
            int port = scanner.nextInt();
            Socket socket = new Socket("localhost", port);
            System.out.println("Choose game:\n 0: multiplayer\n 1: single (easy)\n 2: single(medium)");
            int level = scanner.nextInt();
            new GameClient(level);
        } catch (UnknownHostException e) {
            System.out.println("Unknown host.");
        } catch (IOException e) {
            System.out.println("This game is already full or does not exist. Please, choose another port.");
        }
    }

    public void run(){
        System.out.println("test");
    }
}




