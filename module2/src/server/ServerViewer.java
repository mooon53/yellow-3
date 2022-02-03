package src.server;

/**
 * Viewer class of a server.
 * Has methods to print stuff to the user if the server requests it
 */
public class ServerViewer extends Thread {
    private GameServer server;

    /**
     * Constructor: create a new ServerViewer bound to the given GameServer
     * @param server the GameServer which it should be bound to
     */
    //@requires server != null;
    public ServerViewer(GameServer server) {
        this.server = server;
    }

    /**
     * Displays the connected players and active games.
     */
    public void displayServerStatus() {

        System.out.println("Currently connected players: " + server.getClientHandlers().size());
        System.out.println("Currently active games: " + server.getBoards().size());
    }

    /**
     * Prints a String to the user
     * @param msg String that should be printed
     */
    public void announce(String msg) {
        System.out.println(msg);
    }


}
