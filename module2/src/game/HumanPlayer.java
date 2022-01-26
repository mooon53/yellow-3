package src.game;

import java.io.*;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.Scanner;

public class HumanPlayer extends Player{
    //Scanner to read user's input
    Scanner scanner = new Scanner(System.in);

    private static GameClient client;
    protected int playerID=0;
    private String name;
    private Mark mark;


    /*@requires name != null;
      */
    public HumanPlayer(String name) {
        super(name);
    }

    public Mark assignMark() {
        if (this.playerID == 1) {
            mark = Mark.XX;
            playerID++;
        } else if (this.playerID == 2) {
            mark = Mark.OO;
        } else{
            System.out.println("Can't access playerID.");
        }
        return mark;
    }


    public int chooseMove(GameBoard board) {
        String prompt = "> " + getName() + " (" + getMark().toString() + ") your turn: ";
        System.out.println(prompt);
        //take input from user as index of tile
        int choice = scanner.nextInt();
        //check is the given field is free
        boolean free = board.isField(choice) && (board.getField(choice).equals(src.game.Mark.EMPTY));
        //in case chosen field is occupied, ask user to input another index until it is free
        while (!free) {
            System.out.println("Oops, chosen tile is not valid. Try again: ");
            System.out.println(prompt);
            choice = scanner.nextInt();
            free = board.isField(choice) && (board.getField(choice).equals(src.game.Mark.EMPTY));
        }
        return choice;
    }


    public int chooseRotation(GameBoard board) {
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

    public void connectToServer() {
        try {
            System.out.println("Join port: ");
            int port = scanner.nextInt();
            Socket socket = new Socket("localhost", port);
            client = new GameClient(socket);
        } catch (UnknownHostException e) {
            System.out.println("Unknown host.");
        } catch (IOException e) {
            System.out.println("This game is already full. Please, choose another port.");
        }
    }


    //client connection class Player -> Client
    private class GameClient {
        private Socket socket;
        private BufferedReader reader;
        private BufferedWriter writer;
        private String username;


        public GameClient(Socket socket) {
            System.out.println("_____Client_____");
            try {
                this.socket = socket;
                this.reader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
                this.writer = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
                this.username = getName();
                writer.write(username);
                writer.flush();
                playerID = Integer.parseInt(String.valueOf(reader.read()));
                System.out.println("assigned as: "+playerID);
            } catch (IOException e) {
                System.out.println("Unable to create client.");
            }
        }
    }

    public static void main(String[] args) {
        Scanner sc = new Scanner(System.in);
        System.out.println("Enter your username: ");
        String username = sc.nextLine();
        Player p = new HumanPlayer(username);
        p.connectToServer();

    }

}
