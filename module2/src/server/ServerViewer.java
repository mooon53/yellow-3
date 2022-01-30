package src.server;

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

    public int getPort(){
        Scanner scanner = new Scanner(System.in);
        System.out.println("Connect port: ");
        int port = scanner.nextInt();
        return port;
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
        System.out.println("<Server> "+msg);
    }


}
