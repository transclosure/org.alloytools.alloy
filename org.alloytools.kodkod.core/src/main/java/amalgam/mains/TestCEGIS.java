package amalgam.mains;

import amalgam.cegis.Engine;
import amalgam.cegis.CEGISException;
import amalgam.examples.OriginalTempBackdoor;
import amalgam.examples.XLockingDoor;

import java.io.IOException;

import static amalgam.cegis.Util.maxInt;
import static amalgam.cegis.Util.minInt;

public class TestCEGIS {

    /** Requires runtime parameters:
     *
     * -Djava.library.path="<repo location>/org.alloytools.kodkod.nativesat/jni/<platform specific jni folder>"
     *
     */
    public static void main(String[] args) throws CEGISException, IOException {
        Engine engine;
        engine = new Engine(new OriginalTempBackdoor(minInt, maxInt));
        engine.run();
        engine = new Engine(new XLockingDoor(false));
        engine.run();
        engine = new Engine(new XLockingDoor(true));
        engine.run();
    }
}
