package amalgam.cegis;

import kodkod.engine.satlab.SATFactory;

import java.util.logging.Level;

/**
 * Contains various CEGIS-engine parameters that the caller should be able to configure.
 */
public class CEGISOptions {
    // CEGIS option defaults
    /** Solver to use for incremental steps (only SYNTHESIS right now) */
    private SATFactory incrementalSolver = SATFactory.MiniSat;
    /** Solver to use for core-extraction steps (proximal, root)
     *  Note that for the moment, incrementality and core extraction are mutually exclusive. */
    private SATFactory coreSolver = SATFactory.MiniSatProver;
    /** Maximum number of CEGIS iterations */
    private int loopLimit = 1000;
    /** Number of states in a counterexample trace */
    private int numStates = 5;
    /** Kodkod bitwidth to use
     *  Note: maxInt and minInt are separate so that, if needed, the caller can narrow the number of
     *  integers actually used to improve performance. */
    private int bitwidth = 8; // [-128, 127] default
    /** Minumum integer value */
    private int minInt = -128;
    /** Maximum integer value */
    private int maxInt = 127;
    /** If true, log will be written to a file (all events regardless of log level) */
    private boolean writeLogFile = false;
    /** Log events of this level or higher will be printed to console. */
    private int printLogLevel = Level.INFO.intValue();

    ///////////////////////////////////
    // Restricting attention to safety properties for now. DO NOT SET THIS TO TRUE.
    // note this means that properties like "all states, next state..." will need to be written as
    //  "all states but last, next state..."
    static final boolean lasso = false;

    public SATFactory incrementalSolver() {
        return incrementalSolver;
    }

    public void setIncrementalSolver(SATFactory incrementalSolver) {
        this.incrementalSolver = incrementalSolver;
    }

    public SATFactory coreSolver() {
        return coreSolver;
    }

    public void setCoreSolver(SATFactory coreSolver) {
        this.coreSolver = coreSolver;
    }

    public int loopLimit() {
        return loopLimit;
    }

    public void setLoopLimit(int loopLimit) {
        this.loopLimit = loopLimit;
    }

    public int numStates() {
        return numStates;
    }

    public void setNumStates(int numStates) {
        this.numStates = numStates;
    }

    public int bitwidth() {
        return bitwidth;
    }

    public void setBitwidth(int bitwidth) throws CEGISException {
        if(bitwidth > 30)
            throw new CEGISException("Bitwidth given was too large (30 maximum)");
        if(minInt < -(1 << (bitwidth-1)))
            throw new CEGISException("Bitwidth given was too small to support minInt="+minInt+"; first increase minInt.");
        if(maxInt < (1 << (bitwidth-1)) - 1)
            throw new CEGISException("Bitwidth given was too small to support minInt="+minInt+"; first increase minInt.");
        this.bitwidth = bitwidth;
    }

    public int minint() {
        return minInt;
    }

    public int maxint() {
        return maxInt;
    }

    public void setMinInt(int minInt) throws CEGISException {
        if(minInt < -(1 << (this.bitwidth-1)))
            throw new CEGISException("Invalid minInt for bitwidth; first increase bitwidth.");
        this.minInt = minInt;
    }

    public void setMaxInt(int maxInt) throws CEGISException {
        if(maxInt > (1 << (this.bitwidth-1)) - 1)
            throw new CEGISException("Invalid maxInt for bitwidth; first increase bitwidth.");
        this.maxInt = maxInt;
    }

    public boolean writeLogFile() {
        return writeLogFile;
    }

    public void setWriteLogFile(boolean writeLogFile) {
        this.writeLogFile = writeLogFile;
    }

    public int printLogLevel() {
        return printLogLevel;
    }

    public void setPrintLogLevel(int printLogLevel) {
        this.printLogLevel = printLogLevel;
    }
}
