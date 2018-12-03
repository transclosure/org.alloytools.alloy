package amalgam.mains;

import amalgam.CEGISEngine;
import amalgam.CEGISException;
import amalgam.examples.OriginalTempBackdoor;
import amalgam.examples.XLockingDoor;

import java.io.IOException;

import static amalgam.CEGISHelpers.maxInt;
import static amalgam.CEGISHelpers.minInt;

public class TestCEGIS {

    /** Requires runtime parameters:
     *
     * -Djava.library.path="<repo location>/org.alloytools.kodkod.nativesat/jni/<platform specific jni folder>"
     *
     */
    public static void main(String[] args) throws CEGISException, IOException {
        CEGISEngine engine;
        engine = new CEGISEngine(new OriginalTempBackdoor(minInt, maxInt));
        engine.run();
        engine = new CEGISEngine(new XLockingDoor(false));
        engine.run();
        engine = new CEGISEngine(new XLockingDoor(true));
        engine.run();
    }
}
