package src.server;

public interface Server {
    void start();

    int getPort();

    void stop();
}
