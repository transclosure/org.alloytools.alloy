package amalgam.cegis;

import amalgam.cegis.Engine;
import amalgam.cegis.CEGISException;

import java.io.IOException;
import java.util.logging.FileHandler;
import java.util.logging.Level;
import java.util.logging.LogManager;
import java.util.logging.SimpleFormatter;

/**
 * TODO
 */
public class Logger {
    private final static boolean writeLogFile = false; // turn on for debugging
    private final static java.util.logging.Logger logger = java.util.logging.Logger.getLogger(Engine.class.getName());

    /**
     * TODO
     * @throws CEGISException
     */
    public static void init() throws CEGISException {
        LogManager.getLogManager().reset(); // disable default handler
        logger.setLevel(Level.ALL);
        FileHandler textHandler = null;
        try {
            textHandler = new FileHandler("cegis-log.txt");
        } catch (IOException e) {
            throw new CEGISException(e);
        }
        textHandler.setFormatter(new SimpleFormatter());
        logger.addHandler(textHandler);
    }

    /**
     * TODO
     * @param l
     * @param s
     */
    public static void output(Level l, String s) {
        if(l.intValue() >= Level.INFO.intValue()) {
            // Print the string if it is INFO or more important
            System.out.println(s);
        }
        if(writeLogFile) {
            logger.log(l, s);
        }
    }

    /**
     * TODO
     * @param s
     */
    public static void output(String s) {
        output(Level.INFO, s);
    }
}
