package src.game;

import java.util.Scanner;

public class HumanPlayer extends Player{

    public HumanPlayer(String name){
        super(name);
    }


    @Override
    public void chooseMove(Board board) {
        String prompt = "> " + getName() + " your turn: ";
        System.out.println(prompt);
    }
    public int chooseRotation(GameBoard board) {
        Scanner scanner = new Scanner(System.in);
        System.out.println("Which subboard do you want to rotate?");
        //take input from user as index of subBoard
        int choice = scanner.nextInt();
        //check whether the given index is valid
        boolean free = choice >= 0 && choice < 4;
        //in case chosen field is occupied, ask user to input another index until it is free
        while (!free) {
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
        while (!free) {
            System.out.println("Oops, chosen index is not valid. Try again: ");
            rotation = scanner.nextInt();
            free = rotation == 0 || rotation == 1;
        }

        return choice + (rotation * 4);
    }
}
