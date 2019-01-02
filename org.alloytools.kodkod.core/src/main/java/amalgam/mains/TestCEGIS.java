package amalgam.mains;

import amalgam.cegis.Engine;
import amalgam.cegis.CEGISException;
import amalgam.examples.OriginalTempBackdoor;
import amalgam.examples.RoadsAndRoutes;
import amalgam.examples.RoadsSafety;
import amalgam.examples.XLockingDoor;

import java.io.IOException;

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
        cegis = new Engine(new OriginalTempBackdoor(-128, 127));
        cegis.run();
        cegis = new Engine(new XLockingDoor(false));
        cegis.run();
        cegis = new Engine(new XLockingDoor(true));
        cegis.run();
        cegis = new Engine(new RoadsSafety(5, 2));
        cegis.run();

        // Old liveness-property prototype. Disregard for now.
        //cegis = new Engine(new RoadsAndRoutes(2, 1));
        //cegis.run();
    }
}
