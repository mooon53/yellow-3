package src;


import src.server.GameClient;
import src.server.ServerMain;

import java.util.Scanner;


public class Pentago {
    static Scanner scanner = new Scanner(System.in);

    public static void startGameServer() {
        ServerMain server = new ServerMain();
        Thread thread = new Thread(server);
        thread.start();
        System.out.println("Restart Pentago to join the game.");
    }

    public static void startGameClient() {
        GameClient client = null;
        System.out.println("How would you like to play: multiplayer or singleplayer?");
        String option = scanner.nextLine().toLowerCase();
        int port;
        if (option.equals("multiplayer")) {
            System.out.println("Join port: ");
            port = scanner.nextInt();
            client = new GameClient(0,port);
            new Thread(client).start();
        } else if (option.equals("singleplayer")) {
            System.out.println("Choose level: easy or normal?");
            String choice = scanner.nextLine().toLowerCase();
            if (choice.equals("easy")) {
                System.out.println("Join port: ");
                port = scanner.nextInt();
                client = new GameClient(1,port);
                new Thread(client).start();
            } else if (choice.equals("normal")) {
                System.out.println("Join port: ");
                port = scanner.nextInt();
                client = new GameClient(2,port);
                new Thread(client).start();
            } else {
                System.out.println("your input is not clear ._.");
            }
        } else {
            System.out.println("your input is not clear ._.");
        }
    }

    public static void main(String[] args) {
        System.out.println("Hello! Welcome to Pentago!\n To create game SERVER, to join game choose CLIENT");
        String input = scanner.nextLine().toUpperCase();
        while (!input.equals("SERVER") && !input.equals("CLIENT")) {
            System.out.println("your input is not clear ._.");
            input = scanner.nextLine().toUpperCase();
        }
        if (input.equals("SERVER")) {
            startGameServer();

        } else if (input.equals("CLIENT")) {
            startGameClient();
        }


    }
}
