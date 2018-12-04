package amalgam.cegis;

import amalgam.cegis.Engine;
import amalgam.cegis.CEGISException;
import kodkod.engine.Solution;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.logging.FileHandler;
import java.util.logging.Level;
import java.util.logging.LogManager;
import java.util.logging.SimpleFormatter;

/**
 * TODO
 */
class Logger {
    private final static boolean writeLogFile = false; // turn on for debugging
    private final static java.util.logging.Logger logger = java.util.logging.Logger.getLogger(Engine.class.getName());
    private static long startTime;
    private static long startCore;
    private final static Map<Util.CEGISPHASE, Long> transtotal = new HashMap<>();
    private final static Map<Util.CEGISPHASE, Long> solvetotal = new HashMap<>();
    private static long coreMinTotal;

    /**
     * TODO
     * @throws CEGISException
     */
    static void init() throws CEGISException {
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
    static void log(Level l, String s) {
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
     */
    static void startCore() {
        startCore = System.currentTimeMillis();
    }

    /**
     * TODO
     */
    static void endCore() {
        coreMinTotal += (System.currentTimeMillis() - startCore);
    }

    /**
     * TODO
     */
    static void startTime() {
        startTime = System.currentTimeMillis();
        coreMinTotal = 0;
        transtotal.clear();
        solvetotal.clear();
    }

    /**
     * TODO
     * @param sol
     * @param phase
     */
    static void updateTime(Solution sol, Util.CEGISPHASE phase) {
        // Core minimization time is recorded elsewhere
        String sat = sol.sat() ? "sat" : "unsat";
        long trans = sol.stats().translationTime();
        long solve = sol.stats().solvingTime();
        log(Level.FINE, phase+" trans ms: " + trans + "\tsolve ms: "+ solve + "\t sat: " + sat);
        updateTimeMap(transtotal, phase, trans);
        updateTimeMap(solvetotal, phase, solve);
    }

    /**
     * TODO
     * @param m
     * @param p
     * @param add
     */
    static void updateTimeMap(Map<Util.CEGISPHASE, Long> m, Util.CEGISPHASE p, long add) {
        if(!m.keySet().contains(Util.CEGISPHASE.SYNTH)) m.put(Util.CEGISPHASE.SYNTH, Long.valueOf(0));
        if(!m.keySet().contains(Util.CEGISPHASE.COUNTER)) m.put(Util.CEGISPHASE.COUNTER, Long.valueOf(0));
        if(!m.keySet().contains(Util.CEGISPHASE.PROXIMAL)) m.put(Util.CEGISPHASE.PROXIMAL, Long.valueOf(0));
        if(!m.keySet().contains(Util.CEGISPHASE.ROOT)) m.put(Util.CEGISPHASE.ROOT, Long.valueOf(0));
        m.put(p, m.get(p)+add);
    }

    /**
     * TODO
     * @return
     */
    static String endTime() {
        return "Total time (ms): "+(System.currentTimeMillis()-startTime)+
                ".\nTranslation: "+transtotal+
                ",\nsolve: "+solvetotal+
                ",\ncore minimization (note vulnerable to GC etc.): "+coreMinTotal;
    }
}
