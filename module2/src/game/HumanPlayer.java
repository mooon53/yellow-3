package src.game;

import src.Protocol;
import src.ai.DumbStrategy;

import java.util.Scanner;

public class HumanPlayer extends Player {
    private final DumbStrategy random;

    public HumanPlayer(String name, Mark mark) {
        super(name, mark);
        random = new DumbStrategy();
    }


    @Override
    public int[] turn(GameBoard board) {
        int[] result = new int[2];
        Scanner scanner = new Scanner(System.in);
        String prompt = ">" + getName() + " your turn: \n Enter the index of a field, or enter HINT for an example move";
        System.out.println(prompt);
        String input = scanner.nextLine();
        if (input.equalsIgnoreCase("hint")) {
            int[] example = random.determineMove(board, getMark());
            String rotation;
            if (example[1] % 2 == 0) {
                rotation = "left";
            } else {
                rotation = "right";
            }
            System.out.println("Example move: enter field " +example[0]+
                    ", rotate subboard " +example[1]/2+ ", and rotate it to the " +rotation);
            result[0] = scanner.nextInt();
        } else {
            result[0] = Integer.parseInt(input);
        }
        boolean free = result[0] >= 0 && result[0] < 36 && board.getField(result[0]) == Mark.EMPTY;
        while (!free) {
            System.out.println("Unacceptable input. Try again: ");
            result[0] = scanner.nextInt();
            free = result[0] >= 0 && result[0] < 36;
        }
        System.out.println("Which subboard do you want to rotate?");
        System.out.println("Enter 0 for top left, 1 for top right, 2 for bottom left, 3 for bottom right");
        //take input from user as index of subBoard
        int rotation = scanner.nextInt();
        //check whether the given index is valid
        free =rotation >= 0 && rotation < 4;
        //in case chosen field is occupied, ask user to input another index until it is free
        while (!free) {
            System.out.println("Oops, chosen index is not valid. Try again: ");
            rotation = scanner.nextInt();
            free = rotation >= 0 && rotation < 4;
        }
        //now ask for the rotation
        System.out.println("Which way should it rotate? Enter 0 for left, 1 for right");
        //take input from user
        int direction  = scanner.nextInt();
        //check whether the given integer is valid
        free = direction == 0 || direction == 1;
        //in case chosen field is occupied, ask user to input another index until it is free
        while (!free) {
            System.out.println("Oops, chosen index is not valid. Try again: ");
            direction = scanner.nextInt();
            free = direction == 0 || direction == 1;
        }
        result[1] = (rotation*2) +direction;
        return result;
    }


}
