package amalgam;

/**
 * A CEGIS engine exception
 */
public class CEGISException extends Exception {
    public CEGISException(String msg) {
        super(msg);
    }
    public CEGISException(Exception e) { super(e); }
}