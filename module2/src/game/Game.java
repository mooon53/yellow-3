package src.game;

import java.util.Scanner;

import static src.game.GameBoard.DIM;

public class Game {
    public static final int NUMBER_OF_PLAYERS = 2;
    private GameBoard board;
    /**players.length == NUMBER_OF_PLAYERS;**/
    public Player[] players;
    private int indexOfCurrentPlayer; //index of current player
    Scanner scanner = new Scanner(System.in);

    public Game(Player player1, Player player2) {
        board = new GameBoard();
        players = new Player[NUMBER_OF_PLAYERS];
        players[0] = player1;
        players[1] = player2;
        indexOfCurrentPlayer = 0;
    }

    /**
     * Starts the game. Asks whether game should start again after each completed set
     * until negative answer is received;
     */
    public void start() {
        boolean continueGame = true;
        while (continueGame) {
            indexOfCurrentPlayer=0;
            board.reset();
            playGame();
            System.out.println("Play again? (y/n)");
            continueGame = scanner.nextBoolean();
        }
    }
    /**
     * Play a game starting with the empty board and switching players after each approved move
     * If game is over or there is a winner, finish game and determine winner if such exists
     */
    private void playGame(){
        while(!gameOver()){
           if (players[indexOfCurrentPlayer].equals(players[0])){
               players[indexOfCurrentPlayer].makeMove(board);
               indexOfCurrentPlayer++;
           } else{
               players[indexOfCurrentPlayer].makeMove(board);
               indexOfCurrentPlayer=0;
           }
        }
        update();
    }

    /**
     * Determines the winner and shows corresponding message
     */
    private void update(){
        Player winner;
        if(win()){
            winner = isWinner(players[0].getMark()) ? players[0] : players[1];
            System.out.println(winner.getName() + "is the king of Pentago today!");
        } else {
            System.out.println("No winner this time :D");
        }
    }

    /**
     * Game is over either if there are no empty fields or there is a winner
     * @return true if the game is over
     */
    //@ ensures board.isFull() || win() ==> \result == true;
    public boolean gameOver(){
        return (board.isFull() || win());
    }

    /**
     *
     * @return true if one of players is a winner
     */
    public boolean win(){
        return isWinner(players[0].getMark()) || isWinner(players[1].getMark());
    }

    /**
     *
     * @param candidate represents the mark of player
     * @return true if one of players is a winner in either direction
     */
    //@requires !candidate.equals(Mark.EMPTY);
    public boolean isWinner(Mark candidate){
        return board.winLine(candidate) || board.winCol(candidate) || board.winDiagonal(candidate) || board.winIrregularDiagonal(candidate);
    }

}
