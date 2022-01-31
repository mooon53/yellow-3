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
        try {
            inetAddress= InetAddress.getByName(string);
        } catch (UnknownHostException e) {
            System.out.println(Protocol.error("unknown host"));
        }
        return inetAddress;
    }

    public int level(){
        System.out.println("Choose type of game:\n -0: multiplayer \n -1: singleplayer(easy) \n -2: singleplayer(medium)");
        int level = scanner.nextInt();
        return level;
    }

    public void displayOpponentUsername(){
        System.out.println("Your opponent: "+getClient().getOpponentUsername());
    }

    public void displayCurrentBoard(){
        System.out.println("Updated board:\n"+getClient().getCurrentBoard());
    }

    public void announce(String msg){
        System.out.println(msg);
    }


    public void endGame(String reason){//add winners and draw
        for(Player player : this.getClient().getPlayers()){
            System.out.println(player.getName()+" disconnected.");
        }
    }

}
