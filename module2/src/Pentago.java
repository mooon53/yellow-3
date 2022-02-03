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
        GameClient client = new GameClient();
        Thread c = new Thread(client);
        c.start();
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
