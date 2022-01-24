package src.game;


import java.util.Scanner;

public class HumanPlayer extends Player {
    //Scanner to read user's input
    Scanner scanner = new Scanner(System.in);

    /*@requires name != null;
      @requires mark==Mark.XX || mark ==Mark.OO;
    */
     public HumanPlayer(String name, Mark mark){
         super(name, mark);
     }

    /**
     *
     * @param board represents current playable board
     * @return
     */
    @Override
    public int chooseMove(Board board) {
         String prompt = "> "+ getName() + " ("+ getMark().toString()+") your turn: ";
         System.out.println(prompt);
         //take input from user as index of tile
         int choice = scanner.nextInt();
         //check is the given field is free
         boolean free = board.isField(choice) && (board.getField(choice).equals(src.game.Mark.EMPTY));
         //in case chosen field is occupied, ask user to input another index until it is free
         while(!free) {
             System.out.println("Oops, chosen tile is not valid. Try again: ");
             System.out.println(prompt);
             choice = scanner.nextInt();
             free =  board.isField(choice) && (board.getField(choice).equals(src.game.Mark.EMPTY));
         }
        return choice;
    }
}
