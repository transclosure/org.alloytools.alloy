package amalgam.cegis;

import kodkod.engine.Solution;

public class CEGISResult {
    /**
     * SSUCCESS: synthesis successful
     * SERROR: engine error encountered
     * SFAIL: synthesis failed; engine proved the goals could not be satisfied
     * STIMEOUT: synthesis terminated because max number of iterations was reached
     */
    enum Result {SSUCCESS, SERROR, SFAIL, STIMEOUT};
    private Result result;
    // TODO statistics should persist, not just be logged and then forgotten
    private Solution solution;
    private String message;
    private Problem problem;

    CEGISResult(Problem problem, Result result, String message) throws CEGISException {
        if(result == Result.SSUCCESS)
            throw new CEGISException("No-solution CEGISResult constructor called for successful run.");
        this.result = result;
        this.solution = null;
        this.message = message;
        this.problem = problem;
    }
    CEGISResult(Problem problem, Solution solution, String message) {
        this.result = Result.SSUCCESS;
        this.solution = solution;
        this.message = message;
        this.problem = problem;
    }

    public Result result() {
        return result;
    }
    public boolean success() {
        return result == Result.SSUCCESS;
    }
    public Solution getSolution() throws CEGISException {
        if(!success())
            throw new CEGISException("CEGIS was unsuccessful; no solution available.");
        return solution;
    }

    @Override
    public String toString() {
        if(result == Result.SSUCCESS) {
            return "Success: "+problem.prettyConfigFromSynth(solution)+"\n"+message;
        } else if(result == Result.SFAIL){
            return "Failure: "+message;
        } else {
            return "Error: "+message;
        }
    }

}
