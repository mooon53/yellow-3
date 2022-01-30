package src.server;

import src.Protocol;
import src.game.GameBoard;
import src.game.Mark;
import src.game.Player;

import java.util.ArrayList;
import java.util.Scanner;

public class Game {
    public static final int NUMBER_OF_PLAYERS = 2;
    private ArrayList<Player> players;
    private GameBoard board;
    private int indexOfCurrentPlayer = 0;
    private Mark mark;
    Scanner scanner = new Scanner(System.in);

    public Game(Player player1, Player player2) {
        this.players = new ArrayList<>();
        this.players.add(player1);
        this.players.add(player2);
        setupBoard();
    }

    //getters

    //@pure;
    public ArrayList<Player> getPlayers() {
        return players;
    }

    //@requires players!=null;
    // @ensures \result.size() == players.size();
    public String[] getUsernames() {
        String[] usernames = new String[players.size()];
        int i = 0;
        for (Player player : players) {
            usernames[i] = player.getName();
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

    public void setMark(Player player, int index) {
        if (index == 1) {
            this.mark = Mark.XX;
        } else {
            this.mark = Mark.OO;
        }

    }

    public boolean isLobbyFull() {
        if (this.players.size() == NUMBER_OF_PLAYERS) {
            return true;
        } else {
            return false;
        }
    }


    public void setupBoard() {
        this.board = new GameBoard();
    }

    private void update() {
        Player winner;
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
                //sendMessage(command);
            } else if (win()) {
                reason = "VICTORY";
                command = Protocol.gameover(reason);
                //sendMessage(command);
            }
            return true;
        } else {
            return false;
        }
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





}
