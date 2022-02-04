package src.controller;

import src.Protocol;
import src.model.ai.*;
import src.model.game.GameBoard;
import src.viewer.ClientViewer;
import src.viewer.HumanPlayer;
import src.model.game.Mark;
import src.model.game.Player;
import java.io.IOException;
import java.io.PrintStream;
import java.net.Socket;

/**
 * The client that can play Pentago.
 */
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

    /**
     * Constructor: create a new GameClient.
     * Asks the viewer to provide an IP and port.
     */
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

    /**
     * Returns the socket the client is connected to
     *
     * @return socket
     */
    //@pure;
    public Socket getSocket() {
        return socket;
    }

    /**
     * Returns the viewer of the client
     *
     * @return viewer
     */
    //@pure;
    public ClientViewer getViewer() {
        return viewer;
    }

    /**
     * Returns the username of the player using the client
     *
     * @return username
     */
    //@pure;
    public String getUsername() {
        return username;
    }

    /**
     * Returns the current board state in a String, so it can be shown to the user
     *
     * @return current board state
     */
    //@pure;
    public String getCurrentBoard() {
        return board.toString();
    }


    /**
     * Creates a logic Thread and binds it to this.
     */
    public synchronized void setupLogic() {
        logic = new Thread(new Logic(this));
        logic.start();
    }

    /**
     * Connects to the server by sending HELLO command.
     * Asks the viewer for a username to greet with
     * Also asks the viewer what type of Player should be created
     */
    public synchronized void setConnection() {
        username = viewer.getClientName();
        level = viewer.level();
        greeting(username);
    }


    /**
     * Creates a game.
     * Resets the board and creates a new Player
     *
     * @param currentPlay 0 if this client has first turn, 1 otherwise
     */
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

    /**
     * Asks the player for a move to send to the server.
     */
    public void sendMove() {
        currentPlayer = 0;
        viewer.announce(board.toString());
        viewer.announce(""); //print new line
        int[] move = player.turn(board);
        String command = Protocol.move(move[0], move[1]);
        writer.println(command);
        writer.flush();
    }

    /**
     * Plays the move that the server sends on the board of the client.
     *
     * @param move     index of the field
     * @param rotation integer of rotation
     */
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


    /**
     * Sends a HELLO command to the server.
     *
     * @param name username to greet with.
     */
    public synchronized void greeting(String name) {
        String command = Protocol.greeting("Client by " + name);
        writer.println(command);
        writer.flush();
    }

    /**
     * Sends a LOGIN command to the server.
     */
    public synchronized void login() {
        String command = Protocol.login(this.username);
        writer.println(command);
        writer.flush();
    }

    /**
     * Sends a QUIT command to the server.
     */
    public void quit() {
        String command = Protocol.quit();
        writer.println(command);
        writer.flush();
    }

    /**
     * Sends a LIST command to the server.
     * Asks the server for the list of players connected
     */
    public synchronized void joinList() {
        String command = Protocol.list();
        writer.println(command);
        writer.flush();
    }

    /**
     * Sends a QUEUE command to the server.
     * Queues the client for another game
     */
    public synchronized void joinQueue() {
        int choice = viewer.queue();
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

    /**
     * Reaction if server sends PONG command
     */
    public void ping() {
        viewer.announce("PONG");
    }

    /**
     * Sends PONG command to the server.
     */
    public void pong() {
        String command = Protocol.pong();
        writer.println(command);
        writer.flush();
    }

    public void run() {
        try {
            logic.join();
        } catch (InterruptedException e) {
            System.out.println("Big oops..");
        }
    }

    /**
     * Terminates the client.
     */
    public void close() {
        writer.close();
    }
}



