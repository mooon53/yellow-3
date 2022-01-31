package src.server;

import src.Protocol;
import src.ai.BasicStrategy;
import src.ai.ComputerPlayer;
import src.ai.DumbStrategy;
import src.ai.Strategy;
import src.game.GameBoard;
import src.game.HumanPlayer;
import src.game.Mark;
import src.game.Player;
import java.io.IOException;
import java.io.PrintStream;
import java.net.Socket;
import java.util.ArrayList;
import java.util.Scanner;

public class GameClient extends Thread {
    private Socket socket;
    private PrintStream writer;
    private ArrayList<Player> players;
    private int level;

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
            socket = new Socket(viewer.getInetAddress(), viewer.getPort());
            this.writer = new PrintStream(getSocket().getOutputStream());
            setupLogic();
            setConnection();
        } catch (IOException e) {
            System.out.println("Unable to join port.");
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


    //set player - mark - ID connection
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
        if (level == 0){
            login();
        } else{
           ComputerClient computerClient = new ComputerClient();
           Thread cp = new Thread(computerClient);
           cp.start();
        }
    }

    public synchronized void setupGame() {
        Player player1 = null;
        switch(this.level){
            case 1:
                Strategy strategy = new DumbStrategy();
                player1 = new ComputerPlayer(strategy);
                break;
            case 2:
                Strategy strategy1 = new BasicStrategy();
                player1 = new ComputerPlayer(strategy1);
                break;
            default:
                player1 = new HumanPlayer(getUsername());
                player1.assignMark(0);
                break;
        }
        Mark mark1 = player1.getMark();
        this.players.add(player1);
        Player player2 = new HumanPlayer(getOpponentUsername());
        this.players.add(player2);
        player2.assignMark(1);
        Mark mark2 = player2.getMark();
        this.game = new Game(player1, player2);
        sendTurn(player1.getName());
        System.out.println(game.getBoard().toString());
    }

    public synchronized void sendTurn(String username) {
        String com = Protocol.sendTurn(username);
        writer.println(com);
        writer.flush();

    }


    public synchronized void move() {
        String com = null;
        if (!game.gameOver()) {
            int[] move = game.getPlayer().turn(game.getBoard());
            com = Protocol.move(move[0], move[1]);
            writer.println(com);
            writer.flush();
            game.getBoard().setField(move[0], game.getPlayer().getMark());
            int subBoard = encodeRotation(move[1])[0];
            int rotation = encodeRotation(move[1])[1];
            if(rotation==0){
                game.getBoard().rotateRight(subBoard);
            } else{
                game.getBoard().rotateLeft(subBoard);
            }
            System.out.println(game.getBoard().toString());
            game.update();
            game.next();
            game.gameOver();

        } else {
            com = Protocol.quit();
            writer.println(com);
            writer.flush();
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




