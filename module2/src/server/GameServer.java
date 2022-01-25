package src.server;


import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;

public class GameServer implements Server, Runnable{
    protected int port;
    private List<GameClientHandler> clients = new ArrayList<>();
    private ServerSocket ss;
    private Socket socket;

    public GameServer(int port){
        this.port = port;
        try {
            this.ss =new ServerSocket(port);
            System.out.println("Started server at: "+getPort());
        } catch (IOException e) {
            System.out.println("Error: could not start server at: "+getPort());
        }
    }

    @Override
    public void run() {
        try {
            while(true){
                this.socket = ss.accept();
                System.out.println("Got connection from: "+ socket.getInetAddress());
                var ch = new GameClientHandler();
                clients.add(ch);
                new Thread(ch).start();
            }
        } catch (IOException e) {
            System.out.println("Server/socket closed, program terminated");
        }
    }

    @Override
    public void start() {
        new Thread(this).start();
    }

    @Override
    public int getPort() {
        return ss.getLocalPort();
    }

    @Override
    public void stop() {
        try {
            ss.close();
        } catch (IOException e) {
            System.out.println("Oops, something went wrong!");
        }
    }
}
