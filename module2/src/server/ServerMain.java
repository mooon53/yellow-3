package src.server;

import java.io.IOException;
import java.net.ServerSocket;
import java.util.Scanner;

public class ServerMain implements Runnable{

    @Override
    public void run() {
        ServerSocket ss;
        try {
            Scanner sc = new Scanner(System.in);
            System.out.print("Choose port: ");
            int port = sc.nextInt();
            ss = new ServerSocket(port);
            new GameServer(ss).connect();
        } catch (
                IOException e) {
            System.out.println("Unable to connect to the port.");
        }    }
}

