//- /source/Iface.java
package source;
public interface Iface {
    class /*@source_nested*/Nested {}
}
//- /source/Outer.java
package source;
public class Outer {
    public class Nested {}
    public enum /*@source_kind*/Kind { ONE }
    public record /*@source_point*/Point(int x) {}
    public interface /*@source_tag*/Tag {}
}
//- /binary/Iface.java lib:types
package binary;
public interface Iface {
    class Nested {}
}
//- /binary/Outer.java lib:types
package binary;
public class Outer {
    public class Nested {}
    public enum Kind { ONE }
    public record Point(int x) {}
    public interface Tag {}
}
//- /app/SourceUse.java
package app;
import static source.Outer.*;
import static source.Iface.*;
class SourceUse {
    /*@source_nested_use*/Nested nested;
    /*@source_kind_use*/Kind kind;
    /*@source_point_use*/Point point;
    /*@source_tag_use*/Tag tag;
}
//- /app/BinaryUse.java
package app;
import static binary.Outer.*;
import static binary.Iface.*;
class BinaryUse {
    /*@binary_nested_use*/Nested nested;
    /*@binary_kind_use*/Kind kind;
    /*@binary_point_use*/Point point;
    /*@binary_tag_use*/Tag tag;
}
//? def source_nested_use -> source_nested
//? def source_kind_use -> source_kind
//? def source_point_use -> source_point
//? def source_tag_use -> source_tag
//? def binary_nested_use -> lib binary.Iface.Nested
//? def binary_kind_use -> lib binary.Outer.Kind
//? def binary_point_use -> lib binary.Outer.Point
//? def binary_tag_use -> lib binary.Outer.Tag
//? diag none
