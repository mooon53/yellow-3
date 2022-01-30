package src;


import src.server.GameClient;
import src.server.GameServer;
import java.util.Scanner;


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
            GameClient client = new GameClient();
            Thread c = new Thread(client);
            c.start();
        } else if (input == 1) {
            System.out.println("Enter 0 for easy game, 1 to check how smart are you :D");
            int level = scanner.nextInt();
            //NO SERVER!
            if (level == 0) {
                GameClient client1 = new GameClient();
                Thread c1 = new Thread(client1);
                c1.start();
            } else if (level == 1) {
                GameClient client2 = new GameClient();
                Thread c2 = new Thread(client2);
                c2.start();
            } else {
                System.out.println("No such level exists :>");
            }
        } else {
            System.out.println("Seems, you do not want to play. Bye then :(");
        }

    }


    public static void main(String[] args) {
        System.out.println("Enter SERVER to start Server, CLIENT to start Client");
        String choise = scanner.nextLine().toLowerCase();
        if (choise.equals("server")) {
            startServer();
        } else if (choise.equals("client")) {
            startClient();
        } else {
            System.out.println("Seems, you do not want to play. Bye then :(");
        }


    }
}
