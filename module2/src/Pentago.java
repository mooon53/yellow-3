package src;


import src.server.GameClient;
import src.server.GameServer;
import src.server.ServerMain;

import java.util.Scanner;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;


public class Pentago {
    static Scanner scanner = new Scanner(System.in);

    public static void startServer() {
        Scanner sc = new Scanner(System.in);
        System.out.print("Choose port: ");
        int port = sc.nextInt();
        GameServer server = new GameServer(port);
        Thread s = new Thread(server);
        s.start();
    }

    public static void startClient() {
        System.out.println("Enter 0 to play against humans, enter 1 to play vs computer");
        int input = scanner.nextInt();
        if (input == 0) {
            GameClient client = new GameClient(0);
            Thread c = new Thread(client);
            c.start();
        } else if (input == 1) {
            System.out.println("Enter 0 for easy game, 1 to check how smart are you :D");
            int level = scanner.nextInt();
            if (level == 0) {
                GameClient client1 = new GameClient(1);
                Thread c1 = new Thread(client1);
                c1.start();
            } else if (level == 1) {
                GameClient client2 = new GameClient(2);
                Thread c2 = new Thread(client2);
                c2.start();
            } else {
                System.out.println("No such level exists :>");
            }
        } else {
            System.out.println("Seems, you do not want to play. Bye then :(");
        }

}
    /*
    static Lock lock = new ReentrantLock();

    public static void startGameServer() {
        ServerMain server = new ServerMain();
        Thread thread = new Thread(server);
        thread.start();
        System.out.println("Restart Pentago to join the game.");
    }

    public static void startGameClient() {
        lock.lock();
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
        lock.unlock();
    }
    */

public static void main(String[]args){
        System.out.println("Enter SERVER to start Server, CLIENT to start Client");
        String choise=scanner.nextLine().toLowerCase();
        if(choise.equals("server")){
        startServer();
        }else if(choise.equals("client")){
        startClient();
        }else{
        System.out.println("Seems, you do not want to play. Bye then :(");
        }
        /*System.out.println("Hello! Welcome to Pentago!\n To create game SERVER, to join game choose CLIENT");
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
*/

        }
        }
