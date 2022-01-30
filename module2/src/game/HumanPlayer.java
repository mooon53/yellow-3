package src.game;

import src.Protocol;

import java.util.Scanner;

public class HumanPlayer extends Player {
    private Mark mark;

    public HumanPlayer(String name) {
        super(name);
    }


    @Override
    public int[] turn(GameBoard board) {
        int[] result = new int[2];
        Scanner scanner = new Scanner(System.in);
        String prompt = ">" + getName() + " your turn: ";
        System.out.println(prompt);
        result[0] = scanner.nextInt();
        boolean free = result[0] >= 0 && result[0] < 36;
        while (!free) {
            System.out.println(Protocol.error("Unacceptable input. Try again: "));
            result[0] = scanner.nextInt();
            free = result[0] >= 0 && result[0] < 36;
        }
        System.out.println("Which subboard do you want to rotate?");
        //take input from user as index of subBoard
        int rotation = scanner.nextInt();
        //check whether the given index is valid
        free =rotation >= 0 && rotation < 4;
        //in case chosen field is occupied, ask user to input another index until it is free
        while (!free) {
            System.out.println(Protocol.error("Oops, chosen index is not valid. Try again: "));
            rotation = scanner.nextInt();
            free = rotation >= 0 && rotation < 4;
        }
        //now ask for the rotation
        System.out.println("Which way should it rotate? Enter 0 for right, 1 for left");
        //take input from user
        int direction  = scanner.nextInt();
        //check whether the given integer is valid
        free = direction == 0 || direction == 1;
        //in case chosen field is occupied, ask user to input another index until it is free
        while (!free) {
            System.out.println(Protocol.error("Oops, chosen index is not valid. Try again: "));
            direction = scanner.nextInt();
            free = direction == 0 || direction == 1;
        }
        result[1] = rotation+(direction*4);
        return result;
    }


}
