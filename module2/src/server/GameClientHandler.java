package src.server;

import java.io.*;
import java.net.Socket;

public class GameClientHandler implements Runnable{
    private Socket socket;
    private GameServer server;
    private BufferedReader reader;
    private PrintWriter writer;
    private String username;

    public GameClientHandler(Socket socket, GameServer server) {
        try {
            this.socket = socket;
            this.writer = new PrintWriter(socket.getOutputStream());
            this.reader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
            this.server = server;
        } catch (IOException e) {
            System.out.println("Something went wrong when creating gameClientHandler!");
        }
    }

    @Override
    public void run() {
        int counter  = 0;
        String line;
        while (!socket.isClosed()){
            try{
                line = reader.readLine();
                if (counter == 0 && line!=null){
                    this.username = line;
                    counter ++;
                } else{
                    if (line == null){
                        continue;
                    }
                    int index = Integer.parseInt(line);
                    if (index < 0 || index > 35) {
                        System.out.println("Invalid index");
                        continue;
                    }
                    server.sendMove(index);
                }

            } catch (IOException e) {
                System.out.println("Something went wrong with reading your message.");
            } catch (NumberFormatException n) {
                System.out.println("Not an integer");
            }
        }
    }

    public void printBoard(){
        //write board state to the socket
    }
}
