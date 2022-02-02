package src.server;

import src.Protocol;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Scanner;

public class ServerViewer extends Thread{
    private GameServer server;

    public ServerViewer(GameServer server){
        this.server = server;
    }

    //getters

    public GameServer getServer() {
        return server;
    }

    public InetAddress getInetAddress(){
        InetAddress inetAddress=null;
        Scanner scanner = new Scanner(System.in);
        System.out.println("Choose inetaddress: ");
        String string = scanner.next();
        try {
            inetAddress= InetAddress.getByName(string);
        } catch (UnknownHostException e) {
            System.out.println(Protocol.error("unknown host"));
        }
        return inetAddress;
    }


    public void displayLeftClients(ClientHandler clientHandler){
        System.out.println(clientHandler.getUsername()+" left game.");
    }

    public void displayServerStatus(){

        System.out.println("Currently connected players: " + this.getServer().getClientHandlers().size());
        System.out.println("Currently active games: " + this.getServer().getGames().size());
    }

    //commands
    public void announce(String msg){
        System.out.println(msg);
    }


}
