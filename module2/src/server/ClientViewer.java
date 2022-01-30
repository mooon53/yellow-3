package src.server;

import src.game.Player;

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

    public void displayOpponentUsername(){
        System.out.println("Your opponent: "+getClient().getOpponentUsername());
    }

    public void announce(String msg){
        System.out.println(msg);
    }

    public void checkConnection(){
        if(this.client.getSocket().isConnected()){
            System.out.println("Good Connection");
        } else{
            System.out.println("No connection.");
        }
    }


    public void endGame(String reason){
        System.out.println("GAMEOVER~"+reason);
    }

}
