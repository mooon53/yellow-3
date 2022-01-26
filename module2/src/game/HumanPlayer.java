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


    @Override
    public int chooseMove(GameBoard board) {
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

    @Override
    public int chooseRotation(GameBoard board) {
        System.out.println("Which subboard do you want to rotate?");
        //take input from user as index of subBoard
        int choice = scanner.nextInt();
        //check whether the given index is valid
        boolean free = choice >= 0 && choice < 4;
        //in case chosen field is occupied, ask user to input another index until it is free
        while(!free) {
            System.out.println("Oops, chosen index is not valid. Try again: ");
            choice = scanner.nextInt();
            free = choice >= 0 && choice < 4;
        }
        //now ask for the rotation
        System.out.println("Which way should it rotate? Enter 0 for right, 1 for left");
        //take input from user
        int rotation = scanner.nextInt();
        //check whether the given integer is valid
        free = rotation == 0 || rotation == 1;
        //in case chosen field is occupied, ask user to input another index until it is free
        while(!free) {
            System.out.println("Oops, chosen index is not valid. Try again: ");
            rotation = scanner.nextInt();
            free = rotation == 0 || rotation == 1;
        }

        return choice+(rotation*4);
    }
}
