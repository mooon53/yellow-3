package src.server;


public class ServerViewer extends Thread {
    private GameServer server;

    public ServerViewer(GameServer server) {
        this.server = server;
    }


    public void displayServerStatus() {

        System.out.println("Currently connected players: " + server.getClientHandlers().size());
        System.out.println("Currently active games: " + server.getBoards().size());
    }

    //commands
    public void announce(String msg) {
        System.out.println(msg);
    }


}
