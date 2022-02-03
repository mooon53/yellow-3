package src.viewer;

import src.Protocol;
import src.controller.GameClient;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Scanner;

/**
 * Viewer class of a client.
 * Has methods to print stuff to the user and ask the user for input
 */
public class ClientViewer extends Thread {
    private GameClient client;
    private Scanner scanner = new Scanner(System.in);

    /**
     * Constructor: create a new ClientViewer bound to the given GameClient.
     * @param client the GameClient which it should be bound to.
     */
    //@requires client != null;
    public ClientViewer(GameClient client) {
        this.client = client;
    }

    /**
     * Asks the user to choose a username.
     * @return the input that the user enters
     */
    public synchronized String getClientName() {
        System.out.println("Username: ");
        return scanner.next();
    }

    /**
     * Asks the user to choose a port to connect to.
     * @return the integer that the user enters
     */
    public int getPort() {
        System.out.println("Join port: ");
        return scanner.nextInt();
    }

    /**
     * Asks the user to choose an IP to connect to.
     * @return the InetAddress the user wants to connect to
     */
    public InetAddress getInetAddress() {
        InetAddress inetAddress;
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

    /**
     * Asks the user if they want to play themselves, or let an AI play.
     * @return the integer corresponding to the choice the user made
     */
    public int level() {
        int level;
        while (true) {
            System.out.println("Choose type of game:\n -0: play as yourself " +
                    "\n -1: watch dumb AI play \n -2: watch smart AI play");
            level = scanner.nextInt();
            if (level >= 0 && level < 3) {
                return level;
            }
            System.out.println("Wrong input, try again");
        }

    }

    /**
     * Displays the current board state.
     */
    public void displayCurrentBoard() {
        System.out.println(client.getCurrentBoard());
    }

    /**
     * Prints a String to the user
     * @param msg String that should be printed
     */
    public void announce(String msg) {
        System.out.println(msg);
    }

    /**
     * Tells the player the game has ended.
     * @param reason why the game ended
     * @param won if the player has won the game
     */
    public void endGame(String reason, boolean won) {
        displayCurrentBoard();
        if (reason.equals("DRAW")) {
            System.out.println("There is no winner!");
        } else if (won) {
            System.out.println("You won because of " + reason);
        } else {
            System.out.println("You lost :(");
        }
        client.joinQueue();
    }

    /**
     * Asks the player if they want to join the queue, or quit the program
     * @return 0 if user wants to queue, 1 if user wants to quit
     */
    public int queue() {
        int choice;
        System.out.println("Play a game? 0-yes 1-no");
        choice = scanner.nextInt();
        while (choice != 0 && choice != 1) {
            System.out.println("Play a game? 0-yes 1-no");
            choice = scanner.nextInt();
        }
        return choice;
    }
}
