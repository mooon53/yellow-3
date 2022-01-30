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
    private ArrayList<Player> players = new ArrayList<>();
    private ComputerPlayer cp = null;
    private String username;
    private String opponentUsername;
    private int clientID;
    private GameBoard myBoard;
    private Thread logic;
    private ClientViewer viewer;

    Scanner scanner = new Scanner(System.in);

    public GameClient(int level) {
        this.viewer = new ClientViewer(this);
        Thread view = new Thread(viewer);
        view.start();
        this.myBoard = new GameBoard();
        try {
            socket = new Socket("localhost", viewer.getPort());
            this.writer = new PrintStream(getSocket().getOutputStream());
            setupLogic();
            if (level == 1) {
                Strategy strategy = new BasicStrategy();
                players.add(new ComputerPlayer(strategy));
                players.add(new HumanPlayer(this.username));
            } else if (level == 2) {
                Strategy strategy = new DumbStrategy();
                players.add(new ComputerPlayer(strategy));
                players.add(new HumanPlayer(this.username));
            } else {
                players.add(new HumanPlayer(this.username));
            }
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


    public void setSides(String[] users) {
        if (users[0].equals(getUsername())) {
            this.clientID = 1;
            this.opponentUsername = users[1];
        } else {
            this.clientID = 2;
            this.opponentUsername = users[0];
        }
    }


    public void sendMove(int currentPlayer){
        int[] position=null;
        if (currentPlayer == clientID) {
            position = this.players.get(currentPlayer).turn(this.myBoard);
            String command = Protocol.move(position[0], position[1]);
            writer.println(command);
            writer.flush();
        }
        if(position!=null && cp!=null){
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
            viewer.endGame("WINNER");
        } else if(myBoard.isFull()){
            viewer.endGame("DRAW");
        } else{
            viewer.endGame("DISCONNECT");
        }
    }

    public synchronized void setupLogic() {
        Logic logicc = new Logic(this);
        this.logic = new Thread(logicc);
        this.logic.start();
        System.out.println("HEY NEW CLIENT");
    }


    public synchronized void setConnection(){

        String username = viewer.getClientName();
        this.username = username;
        viewer.checkConnection();
        greeting("Client by "+username);


    }

    public void setupGame(){
        ArrayList<Player> players = new ArrayList<>();
        players.add(new HumanPlayer(opponentUsername));
        players.add(new HumanPlayer(username));
        Game game = new Game(players.get(0), players.get(1));
        String command = Protocol.newGame(getUsername(), getOpponentUsername());
        writer.println(command);
        writer.flush();
    }

    //logic queries
    public synchronized void greeting(String name){
        String command = Protocol.greeting(name);
        System.out.println("GREETING");
        writer.println(command);
        writer.flush();
    }
    public synchronized void login(){
        String command = Protocol.login(this.username);
        writer.println(command);
        writer.flush();
    }
    public void quit(){
        String command = Protocol.quit();
        writer.println(command);
        writer.flush();
    }

    public synchronized void joinList(){
        String command = Protocol.list();
        writer.println(command);
        writer.flush();
    }

    public synchronized void joinQueue(){
        System.out.println("Play a game? 0-yes 1-no");
        int choice = Integer.parseInt(scanner.next());
        if(choice==0){
            String command = Protocol.queue();
            writer.println(command);
            writer.flush();
        } else if(choice==1){
            String command = Protocol.quit();
            writer.println(command);
            writer.flush();
        }
    }

    public void ping(){
        String command = Protocol.ping();
        writer.println(command);
        writer.flush();
    }
    public void pong(){
        String command = Protocol.pong();
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




