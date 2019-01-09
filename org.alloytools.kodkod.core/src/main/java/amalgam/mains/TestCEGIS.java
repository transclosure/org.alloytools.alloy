package amalgam.mains;

import amalgam.cegis.CEGISOptions;
import amalgam.cegis.CEGISResult;
import amalgam.cegis.Engine;
import amalgam.cegis.CEGISException;
import amalgam.examples.*;

import java.io.IOException;
import java.util.logging.Level;

/**
 * Test CEGIS on current suite of examples
 */
public class TestCEGIS {

    /**
     * Requires runtime parameters:
     *
     * -Djava.library.path="<repo location>/org.alloytools.kodkod.nativesat/jni/<platform specific jni folder>"
     *
     */
    public static void main(String[] args) throws CEGISException, IOException {
        Engine cegis;
        CEGISOptions options = new CEGISOptions();


        testTempBackdoor();
        testXLocking();

        //cegis = new Engine(new OriginalTempBackdoor(options), options);
        //cegis.run();
        //cegis = new Engine(new WorkersTempBackdoor(options), options);
        //cegis.run();
        //cegis = new Engine(new XLockingDoor(false), options);
        //cegis.run();
        //cegis = new Engine(new XLockingDoor(true), options);
        //cegis.run();

        // Note: for RoadsSafety, soundness requires max num states >= |good|+|bad|.
        options.setLoopLimit(2000);
        options.setNumStates(6);
        cegis = new Engine(new RoadsSafety(4, 2), options);
        cegis.run();

        // Correct with 371 iterations @ |states|=7 (Jan 8 '19)
        //options.setNumStates(7);
        //cegis = new Engine(new RoadsSafety(5, 2), options);
        //cegis.run();

        // Correct with 927 iterations @ |states|=8 (Jan 2 '19)
        // options.setNumStates(8);
        // Before trying these, make sure |states| is big enough!
        //cegis = new Engine(new RoadsSafety(6, 2));
        //cegis.run();



        // Old liveness-property prototype. Disregard for now.
        //cegis = new Engine(new RoadsAndRoutes(2, 1));
        //cegis.run();
    }

    static void testXLocking() throws CEGISException {
        Engine cegis;
        CEGISOptions options = new CEGISOptions(); // defaults
        options.setPrintLogLevel(Level.OFF.intValue());
        System.out.println("Testing XLocking false");
        cegis = new Engine(new XLockingDoor(false), options);
        CEGISResult r;
        r = cegis.run();
        assertTrue(r.success());
        System.out.println("Testing XLocking true");
        cegis = new Engine(new XLockingDoor(true), options);
        r = cegis.run();
        assertTrue(r.success());
    }

    static void testTempBackdoor() throws CEGISException {
        Engine cegis;
        CEGISOptions options = new CEGISOptions(); // defaults
        options.setPrintLogLevel(Level.OFF.intValue());
        System.out.println("Testing Original temp/backdoor");
        cegis = new Engine(new OriginalTempBackdoor(options), options);
        CEGISResult r;
        r = cegis.run();
        assertTrue(r.success());
        System.out.println("Testing workers temp/backdoor");
        cegis = new Engine(new WorkersTempBackdoor(options), options);
        r = cegis.run();
        assertTrue(r.success());
    }

    static void assertTrue(boolean b) {
        if(!b) {
            throw new RuntimeException("Test failed, see stack");
        }
        // TODO: use JUnit
    }
}
