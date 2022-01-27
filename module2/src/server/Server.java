package src.server;

public interface Server {
    /**
     * establish connection
     */
    public void connect();
    /**
     * returns port
     */
    //@pure;
    public int getPort();
    /**
     * stops connection;
     */
    public void stop();
}
