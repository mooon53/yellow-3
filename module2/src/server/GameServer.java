package src.server;

import src.Protocol;
import src.game.GameBoard;
import src.game.Mark;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;

/**
 * The server which Pentago runs on.
 */
public class GameServer extends Thread {
    private ArrayList<ClientHandler> clientHandlers;
    private ServerSocket serverSocket;
    private ServerViewer viewer;
    private ArrayList<GameBoard> boards;
    private ArrayList<ClientHandler> queue;
    private ArrayList<String> loggedPlayers;

    /**
     * Constructor: starts a new Server on the given port
     * @param port port to start the server on
     */
    public GameServer(int port) {
        try {
            boards = new ArrayList<>();
            loggedPlayers = new ArrayList<>();
            clientHandlers = new ArrayList<>();
            queue = new ArrayList<>();
            setViewer();
            viewer.announce("_____Pentago Server_____");
            serverSocket = new ServerSocket(port);
            viewer.announce("Connected to port: " + serverSocket.getLocalPort());
            viewer.displayServerStatus();
        } catch (IOException e) {
            System.out.println(Protocol.error("Unable to set connection"));
        }

    }

    //getters


    /**
     * Returns a list of all connected clientHandlers
     * @return ArrayList of clientHandlers
     */
    //@requires clientHandlers.size()!=0;
    //@pure;
    public ArrayList<ClientHandler> getClientHandlers() {
        return this.clientHandlers;
    }

    /**
     * Returns the connected viewer
     * @return viewer
     */
    //@pure;
    public ServerViewer getViewer() {
        return viewer;
    }

    /**
     * Adds a clientHandler to the list.
     * Also displays the status of the server
     * @param clientHandler the clientHandler to add to the list
     */
    private void addClientHandler(ClientHandler clientHandler) {
        clientHandlers.add(clientHandler);
        viewer.displayServerStatus();
    }

    /**
     * Removes a clientHandler from the list.
     * Also removes it from the queue
     * If the clientHandler was in a game, it informs the other clientHandler in that game.
     * @param clientHandler the clientHandler that disconnected
     */
    public void removeClient(ClientHandler clientHandler) {
        clientHandlers.remove(clientHandler);
        queue.remove(clientHandler);
        GameBoard board = clientHandler.getBoard();
        loggedPlayers.remove(clientHandler.getUsername());
        if (board != null) {
            for (ClientHandler ch : clientHandlers) {
                if (ch.getBoard() == board) {
                    ch.sendMessage(Protocol.gameover("DISCONNECT", ch.getUsername()));
                    ch.setMark(null);
                    ch.setBoard(null);
                    boards.remove(board);
                }
            }
        }
    }


    /**
     * Creates a new viewer for the server.
     */
    private void setViewer() {
        viewer = new ServerViewer(this);
        new Thread(viewer).start();
    }

    /**
     * Response to a LOGIN command of a client.
     * @param username the username of the client
     * @return the command that needs to be sent in response
     */
    public synchronized String loginClient(String username) {
        String command;
        if (availableUsername(username)) {
            clientHandlers.get(clientHandlers.size() - 1).setUsername(username);
            loggedPlayers.add(username);
            command = Protocol.login();
        } else {
            command = Protocol.alreadyLoggedIn();
        }
        return command;
    }


    /**
     * Adds the given clientHandler to the queue.
     * Response to the QUEUE command
     * @param clientHandler to add to the queue
     */
    public synchronized void addToQueue(ClientHandler clientHandler) {
        int state = queue.size();
        if (state == 0) {
            queue.add(clientHandler);
        } else if (state == 1) {
            queue.add(clientHandler);
            sendList();
        }
    }

    /**
     * Creates a new game if the queue consists of 2 clients.
     * Sends NEWGAME command to the clients in the queue
     * Also removes those clients from the queue
     */
    public void createGame() {
        if (queue.size() == 2) {
            GameBoard board = new GameBoard();
            boards.add(board);
            viewer.displayServerStatus();
            String com = Protocol.newGame(queue.get(1).getUsername(), queue.get(0).getUsername());
            queue.get(1).setMark(Mark.OO);
            queue.get(0).setMark(Mark.XX);
            for (ClientHandler clientHandler : queue) {
                clientHandler.setBoard(board);
                clientHandler.sendMessage(com);
            }
            queue.clear();
        }
    }

    /**
     * Response to a MOVE command.
     * Checks if the move is legal
     * If it is, it plays it and sends it to the clientHandlers in that game
     * @param index the field to place a piece on
     * @param rotation the rotation sent
     * @param user the clientHandler that sent the move
     */
    public void makeMove(int index, int rotation, ClientHandler user) {
        GameBoard board = user.getBoard();
        ClientHandler opponent = null;
        for (ClientHandler ch : clientHandlers) {
            if (ch.getBoard() == board && ch.getMark() != user.getMark()) {
                opponent = ch;
                //should only be 1 option, so break if the opponent is found
                break;
            }
        }
        //if opponent == null, something went wrong
        if (opponent == null) {
            user.sendMessage(Protocol.error("Internal server error, no opponent found"));
            user.setBoard(null);
            user.setMark(null);
            return;
        }

        if (board.getField(index) != Mark.EMPTY) {
            user.sendMessage(Protocol.error("Illegal move, try again"));
            return;
        }


        //now execute the move
        board.setField(index, user.getMark());
        if (rotation % 2 == 0) {
            board.rotateLeft(rotation / 2);
        } else {
            board.rotateRight(rotation / 2);
        }
        user.sendMessage(Protocol.move(index, rotation));
        opponent.sendMessage(Protocol.move(index, rotation));

        //the move is done, now we check if the game has ended
        if (board.isFull() || board.isWinner(Mark.XX) || board.isWinner(Mark.OO)) {
            String gameOver;
            if (board.isWinner(user.getMark())) {
                gameOver = Protocol.gameover("VICTORY", user.getUsername());
            } else if (board.isWinner(opponent.getMark())) {
                gameOver = Protocol.gameover("VICTORY", opponent.getUsername());
            } else {
                gameOver = Protocol.gameover("DRAW", "");
            }
            //clear board and mark fields of clientHandlers
            user.sendMessage(gameOver);
            user.setBoard(null);
            user.setMark(null);
            opponent.sendMessage(gameOver);
            opponent.setBoard(null);
            opponent.setMark(null);
            boards.remove(board);
        }
    }

    /**
     * Response to a HELLO command
     * @return a HELLO command to be sent to the client
     */
    public synchronized String greeting() {
        return Protocol.greeting("PentagoServer of Katy and Niels :)");
    }

    /**
     * Checks if there exists no client with the given username
     * @param username the name to be checked
     * @return false if there exists a client with that username, true otherwise
     */
    private boolean availableUsername(String username) {
        boolean is = true;
        for (String player : this.loggedPlayers) {
            if (player != null && !player.equals("") && player.equals(username)) {
                is = false;
                break;
            }
        }
        return is;
    }

    /**
     * Response to LIST command
     * @return a LIST command to be sent to the client
     */
    public synchronized String sendList() {
        String command = Protocol.list(loggedPlayers);
        viewer.displayServerStatus();
        return command;
    }

    /**
     * Response to PONG command
     */
    public void ping() {
        viewer.announce("PONG");
    }

    /**
     * Response to PING command
     * @param ch the clientHandler sending the PING command
     */
    public void pong(ClientHandler ch) {
        ch.sendMessage(Protocol.pong());
    }

    /**
     * Returns a list of the boards currently in play
     * @return boards
     */
    public ArrayList<GameBoard> getBoards() {
        return boards;
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

}
