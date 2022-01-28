package src.server;

import src.Protocol;
import src.game.GameBoard;

import java.util.ArrayList;
import java.util.Scanner;

public class Game {
    public static final int NUMBER_OF_PLAYERS = 2;
    private ArrayList<ClientHandler> players;
    private GameBoard board;
    private int indexOfCurrentPlayer = 0;
    Scanner scanner = new Scanner(System.in);

    public Game(ClientHandler player) {
        this.players = new ArrayList<>();
        this.board = new GameBoard();
        this.players.add(player);
        System.out.println("Your mark is: " + player.getMark().toString());
    }

    //getters

    //@pure;
    public ArrayList<ClientHandler> getPlayers() {
        return players;
    }

    //@requires players!=null;
    // @ensures \result.size() == players.size();
    public String[] getUsernames() {
        String[] usernames = new String[players.size()];
        int i = 0;
        for (ClientHandler player : players) {
            usernames[i] = player.getUsername();
            i++;
        }
        return usernames;
    }

    public GameBoard getBoard() {
        return board;
    }

    //@pure;
    public int getIndexOfCurrentPlayer() {
        return indexOfCurrentPlayer;
    }

    public int getOpponentIndex() {
        int oppIndex = 0;
        if (this.indexOfCurrentPlayer == 0) {
            oppIndex = 1;
        }
        return oppIndex;
    }

    //queries
    public void addPlayer(ClientHandler client) {
        this.players.add(client);
        if (this.isLobbyFull()) {
            String command = Protocol.newGame(players.get(0).getUsername(), players.get(1).getUsername());
            this.sendMessage(command);
        }
    }

    public boolean isLobbyFull() {
        if (this.players.size() == NUMBER_OF_PLAYERS) {
            return true;
        } else {
            return false;
        }
    }


    public void play() {

    }

    private void update() {
        ClientHandler winner;
        if (win()) {
            winner = isWinner(this.indexOfCurrentPlayer) ? players.get(0) : players.get(1);
            System.out.println(winner.getName() + "is the king of Pentago today!");
        }
    }

    public void next() {
        if (indexOfCurrentPlayer == 0) {
            this.indexOfCurrentPlayer = 1;
        } else {
            this.indexOfCurrentPlayer = 0;
        }
    }

    /**
     * Game is over either if there are no empty fields or there is a winner
     *
     * @return true if the game is over
     */
    public boolean gameOver() {
        String reason;
        String command;
        if (board.isFull() || win()) {
            if (board.isFull()) {
                reason = "DRAW";
                command = Protocol.gameover(reason);
                sendMessage(command);
            } else if (win()) {
                reason = "VICTORY";
                command = Protocol.gameover(reason);
                sendMessage(command);
            }
            closeGame();
            closeConnection();
            return true;
        } else {
            return false;
        }
    }

    public void disconnect() {
        String reason = Protocol.gameover("DISCONNECT");
        Protocol.quit();
        sendMessage(reason);

    }

    public void closeConnection() {
        this.getPlayers().get(0).close();
        this.getPlayers().get(1).close();
    }

    public void sendTurn() {
        String command = Protocol.ping();
        this.sendMessage(command);
    }

    public void getTurn(){
        String command = Protocol.pong();
        this.sendMessage(command);
    }

    /**
     * @return true if one of players is a winner
     */
    public boolean win() {
        return isWinner(indexOfCurrentPlayer);
    }

    /**
     * @param indexOfCurrentPlayer represents the current player to be checked
     * @return true if one of players is a winner in either direction
     */
    public boolean isWinner(int indexOfCurrentPlayer) {
        return board.winLine(players.get(indexOfCurrentPlayer).getMark()) ||
                board.winCol(players.get(indexOfCurrentPlayer).getMark()) ||
                board.winDiagonal(players.get(indexOfCurrentPlayer).getMark()) ||
                board.winIrregularDiagonal(players.get(indexOfCurrentPlayer).getMark());
    }

    public void closeGame() {
        this.getPlayers().get(0).close();
        this.getPlayers().get(1).close();
    }

    public void sendMessage(String msg){
        players.get(0).sendMessage(msg);
        players.get(1).sendMessage(msg);
    }

}
