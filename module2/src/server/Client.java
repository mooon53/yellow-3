package src.server;

import src.week7server.ChatListener;

import java.net.InetAddress;

public interface Client {
    /**
     * Connects to a server
     * @param address of the server
     * @param port to connect to
     * @return true if the connection succeeded, false if the connection failed
     */
    boolean connect(InetAddress address, int port);

    /**
     * Closes the client
     */
    void close();

    /**
     * Sends a move of the player to the server
     * @param index the index of the field selected
     * @return true on success, false on failure
     */
    boolean sendMove(int index);

}
