package src.server;

import java.util.Scanner;

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
    public String getClientName(){
        System.out.println("Username: ");
        String name = scanner.nextLine();
        return name;
    }

    public int getPort(){
        System.out.println("Join port: ");
        int port = scanner.nextInt();
        return  port;
    }

    public void getEnemyName(){
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

    public void endGame(String username, String reason){
        System.out.println("GAMEOVER~"+username+"~"+reason);
    }

}
