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
import java.util.Scanner;

public class GameClient extends Thread {
    private Socket socket;
    private PrintStream writer;
    private int currentPlayer;
    private int level;
    private Player player = null;
    private String username;
    private GameBoard board;
    private Thread logic;
    private ClientViewer viewer;

    Scanner scanner = new Scanner(System.in);

    public GameClient() {
        viewer = new ClientViewer(this);
        Thread view = new Thread(viewer);
        view.start();
        this.board = new GameBoard();
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

    //@pure;
    public String getUsername() {
        return username;
    }

    //@pure;
    public String getCurrentBoard() {
        return board.toString();
    }




    public synchronized void setupLogic() {
        logic = new Thread(new Logic(this));
        logic.start();
    }


    public synchronized void setConnection() {
        username = viewer.getClientName();
        level = viewer.level();
        greeting(username);
    }



    public synchronized void setupGame(int currentPlay) {
        board.reset();
        switch (level) {
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
        currentPlayer = currentPlay;
        if (currentPlayer == 0) {
            sendMove();
        }
    }


    public void sendMove() {
        currentPlayer = 0;
        System.out.println(board.toString());
        System.out.println();
        int[] move = player.turn(board);
        String command = Protocol.move(move[0], move[1]);
        writer.println(command);
        writer.flush();
    }


    public synchronized void move(int move, int rotation) {
        if (currentPlayer == 0) {
            board.setField(move, player.getMark());
            if (rotation % 2 == 0) { //rotate to the left if rotation is even
                board.rotateLeft(rotation / 2);
            } else { //else, rotate to the right
                board.rotateRight(rotation / 2);
            }
            currentPlayer++;
        } else {
            board.setField(move, player.getMark().other());
            if (rotation % 2 == 0) {
                board.rotateLeft(rotation / 2);
            } else {
                board.rotateRight(rotation / 2);
            }
            sendMove();
        }
    }



    //logic queries
    public synchronized void greeting(String name) {
        String command = Protocol.greeting("Client by " + name);
        writer.println(command);
        writer.flush();
    }

    public synchronized void login() {
        String command = Protocol.login(this.username);
        writer.println(command);
        writer.flush();
    }

    public void quit() {
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
        System.out.println("PONG");
    }

    public void pong() {
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




