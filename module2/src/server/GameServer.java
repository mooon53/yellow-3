package src.server;

import src.game.Player;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.Scanner;

public class GameServer implements Server {
    private ArrayList<ClientHandler> clientHandlers = new ArrayList();
    private ServerSocket serverSocket;
    private int numPlayers;

    public GameServer(ServerSocket serverSocket) {
        System.out.println("_____Pentago Server_____");
        this.numPlayers = 0;
        this.serverSocket = serverSocket;
    }

    @Override
    public void start() {
        try {
            System.out.println("Waiting for players...");

            while (this.numPlayers < 2) {
                Socket socket = this.serverSocket.accept();
                numPlayers++;
                System.out.println("Players connected: " + this.numPlayers);

                ClientHandler ch = new ClientHandler(socket, this, this.numPlayers);
                this.clientHandlers.add(ch);
                (new Thread(ch)).start();
            }

            System.out.println("Game is full.");
        } catch (IOException var3) {
            System.out.println("Oops, unable to establish connection.");
            this.stop();
        }

    }

    @Override
    public int getPort() {
        return this.serverSocket.getLocalPort();
    }

    @Override
    public void stop() {
        try {
            if (this.serverSocket != null) {
                this.serverSocket.close();
            }
        } catch (IOException var2) {
            var2.printStackTrace();
        }

    }

    public static void main(String[] args) throws IOException {
        Scanner sc = new Scanner(System.in);
        System.out.print("Choose port: ");
        int port = sc.nextInt();
        ServerSocket ss = new ServerSocket(port);
        GameServer gs = new GameServer(ss);
        gs.start();
    }
}
