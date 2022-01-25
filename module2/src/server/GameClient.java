package src.server;


import java.io.*;
import java.net.InetAddress;
import java.net.Socket;

public class GameClient implements Client, Runnable{
    private Socket socket;
    private BufferedReader reader;
    private BufferedWriter writer;



    @Override
    public boolean connect(InetAddress address, int port) {
        try {
            socket = new Socket(address, port);
            writer = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
            reader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
            new Thread(this).start();
            return true;
        } catch (IOException e) {
            return false;
        }
    }

    @Override
    public void close() {
        try {
            writer.close();
            reader.close();
            socket.close();
        } catch (IOException e) {
            System.out.println("Something went wrong!");
        }
    }

    @Override
    public boolean sendMove(int index) {
        if (index > 35 || index < 0){
            System.out.println("invalid index");
            return false;
        } else {
            try {
                writer.newLine();
                writer.write(index);
                writer.flush();
                return true;
            } catch (IOException e) {
                System.out.println("Something went wrong with submitting move!");
                close();
                return false;
            }
        }
    }

    @Override
    public boolean sendUsername(String username) {
        try {
            writer.newLine();
            writer.write(username);
            writer.flush();
            return true;
        } catch (IOException e) {
            System.out.println("Something went wrong with submitting username!");
            close();
            return false;
        }
    }

    @Override
    public void run() {
        String line;
        while (!socket.isClosed()){
            try{
                line = reader.readLine();
                if (line == null){
                    continue;
                }
                System.out.println(line);
                //print board state
            } catch (IOException e) {
                System.out.println("Something went wrong with getting output from the server");
                close();
                break;
            }
        }
    }
}
