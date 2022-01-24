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
        if(winLine(candidate)) /*|| winCol(candidate) || winDiagLeft(candidate) ||winDiagRight(candidate))*/{
            return true;
        } else {
            return false;
        }
    }

    /**
     * Check whether a given mark covers a line by winning conditions
     * @param mark represents a mark to check
     * @return true if there are 5 marks in a row
     */
    private boolean winLine(Mark mark){
        boolean result = false;
        for(int row=0; row< board.dim; row++){
            for(int col = 0; col< board.dim; col++){
                if(board.getField(row,col)!=mark && col != 1){
                    break;
                }
                if (col== board.dim-1){
                    result = true;

                }
            }
        }
        return result;
    }
}
