package src;


import src.server.GameClient;
import src.server.ServerMain;

import java.util.Scanner;


public class Pentago {
    static Scanner scanner = new Scanner(System.in);

    public synchronized static void startGameServer() {
        ServerMain server = new ServerMain();
        Thread thread = new Thread(server);
        thread.start();
    }

    public static void startGameClient() {
        GameClient client = null;
        System.out.println("How would you like to play: multiplayer or singleplayer?");
        String option = scanner.nextLine().toLowerCase();
        if (option.equals("multiplayer")) {
            client = new GameClient(0);
            new Thread(client).start();
        } else if (option.equals("singleplayer")) {
            System.out.println("Choose level: easy or normal?");
            String choice = scanner.nextLine().toLowerCase();
            if (choice.equals("easy")) {
                client = new GameClient(1);
                new Thread(client).start();
            } else if (choice.equals("normal")) {
                client = new GameClient(2);
                new Thread(client).start();
            } else {
                System.out.println("your input is not clear ._.");
            }
        } else {
            System.out.println("your input is not clear ._.");
        }
    }

    public static void main(String[] args) {
        System.out.println("Hello! Welcome to Pentago!\n To be a host choose SERVER, to join game choose CLIENT");
        String input = scanner.nextLine().toUpperCase();
        if (input.equals("SERVER")) {
            startGameServer();
        } else if (input.equals("CLIENT")) {
            startGameClient();
        } else {
            System.out.println("your input is not clear ._.");
        }

    }
}
