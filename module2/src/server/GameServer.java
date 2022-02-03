package src.server;

import src.Protocol;
import src.game.GameBoard;
import src.game.Mark;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;

public class GameServer extends Thread {
    private ArrayList<ClientHandler> clientHandlers;
    private ServerSocket serverSocket;
    private ServerViewer viewer;
    private ArrayList<GameBoard> boards;
    private ArrayList<ClientHandler> queue;
    private ArrayList<String> loggedPlayers;


    public GameServer(int port) {
        try {
            boards = new ArrayList<>();
            loggedPlayers = new ArrayList<>();
            clientHandlers = new ArrayList<>();
            queue = new ArrayList<>();
            setViewer();
            System.out.println("_____Pentago Server_____");
            serverSocket = new ServerSocket(port);
            viewer.announce("Connected to port: " + serverSocket.getLocalPort());
            viewer.displayServerStatus();
        } catch (IOException e) {
            System.out.println(Protocol.error("Unable to set connection"));
        }

    }

    //getters
    //@requires clientHandlers.size()!=0;
    //@pure;
    public ArrayList<ClientHandler> getClientHandlers() {
        return this.clientHandlers;
    }


    //@pure;
    public ServerViewer getViewer() {
        return viewer;
    }


    public void addClientHandler(ClientHandler clientHandler) {
        clientHandlers.add(clientHandler);
        viewer.displayServerStatus();
    }


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



    private void setViewer() {
        viewer = new ServerViewer(this);
        new Thread(viewer).start();
    }

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

    public synchronized void addToQueue(ClientHandler clientHandler) {
        int state = queue.size();
        if (state == 0) {
            queue.add(clientHandler);
        } else if (state == 1) {
            queue.add(clientHandler);
            sendList();
        }
    }

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
        System.out.println(board); //for testing purposes
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

    public synchronized String greeting() {
        return Protocol.greeting("PentagoServer of Katy and Niels :)");
    }


    public boolean availableUsername(String username) {
        boolean is = true;
        for (String player : this.loggedPlayers) {
            if (player != null && !player.equals("") && player.equals(username)) {
                is = false;
                break;
            }
        }
        return is;
    }

    public synchronized String sendList() {
        String command = Protocol.list(loggedPlayers);
        viewer.displayServerStatus();
        return command;
    }

    public void ping() {
        System.out.println("PONG");
    }

    public void pong(ClientHandler ch) {
        ch.sendMessage(Protocol.pong());
    }


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
