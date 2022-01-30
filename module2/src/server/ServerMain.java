package src.server;

import java.io.IOException;
import java.net.ServerSocket;
import java.util.Scanner;

public class ServerMain implements Runnable {

    @Override
    public void run() {
        Scanner sc = new Scanner(System.in);
        System.out.print("Choose port: ");
        int port = sc.nextInt();
        new GameServer(port);
    }
}

