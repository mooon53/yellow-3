package src.server;

public interface Server {
    /**
     * Starts the server, using the port provided in the constructor.
     */
    void start();

    /**
     * Returns the port of the server.
     * @return port.
     */
    int getPort();

    /**
     * Stops the server.
     */
    void stop();

}
