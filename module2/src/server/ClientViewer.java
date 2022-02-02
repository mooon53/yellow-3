package src.server;

import src.Protocol;
import src.game.Player;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.sql.SQLOutput;
import java.util.Scanner;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

public class ClientViewer extends Thread{
    private GameClient client;
    Scanner scanner = new Scanner(System.in);

    public  ClientViewer(GameClient client){
        this.client = client;
    }

    //getters
    //@pure;
    public GameClient getClient() {
        return client;
    }


    //methods
    public synchronized String getClientName(){
        System.out.println("Username: ");
        String name = scanner.next();
        return name;
    }

    public int getPort(){
        System.out.println("Join port: ");
        int port = scanner.nextInt();
        return  port;
    }
    public InetAddress getInetAddress(){
        InetAddress inetAddress=null;
        Scanner scanner = new Scanner(System.in);
        System.out.println("Join host: ");
        String string = scanner.next();
        while (true) {
            try {
                inetAddress = InetAddress.getByName(string);
                break;
            } catch (UnknownHostException e) {
                System.out.println(Protocol.error("unknown host"));
                System.out.println("Join host: ");
                string = scanner.next();
            }
        }
        return inetAddress;
    }

    public int level(){
        int level;
        while (true) {
            System.out.println("Choose type of game:\n -0: play as yourself \n -1: watch dumb AI play \n -2: watch smart AI play");
            level = scanner.nextInt();
            if (level >= 0 && level < 3) {
                return level;
            }
            System.out.println("Wrong input, try again");
        }

    }

    public void displayOpponentUsername(){
        System.out.println("Your opponent: "+getClient().getOpponentUsername());
    }

    public void displayCurrentBoard(){
        System.out.println(getClient().getCurrentBoard());
    }

    public void announce(String msg){
        System.out.println(msg);
    }


    public void endGame(String reason, boolean won){
        displayCurrentBoard();
        if (reason.equals("DRAW")) {
            System.out.println("There is no winner!");
        } else if (won) {
            System.out.println("You won because of " +reason);
        } else {
            System.out.println("You lost :(");
        }
        client.joinQueue();
    }

}
