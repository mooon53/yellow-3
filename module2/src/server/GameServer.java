package src.server;



import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;

public class GameServer implements Server, Runnable{
    protected int port;
    private List<GameClientHandler> clients = new ArrayList<>(); //should only contain 2 clients
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
            int clientCounter = 0;
            while(clientCounter<2){
                this.socket = ss.accept();
                System.out.println("Got connection from: "+ socket.getInetAddress());
                var ch = new GameClientHandler(socket, this);
                clients.add(ch);
                new Thread(ch).start();
                clientCounter++;
            }
            //2 clients are found, game should be started now (TO DO)
        } catch (IOException e) {
            System.out.println("Something went wrong with the server!");
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


    /**
     * Sends the move to the board, and notifies the clients
     * @param index of the field on the board
     */
    //@requires index >= 0 && index < 36;
    public void sendMove(int index) {
        //send the move to the board (TO DO)
        for(GameClientHandler client : clients){
            client.printBoard();
        }
    }

}
