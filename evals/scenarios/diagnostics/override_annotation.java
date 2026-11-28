//- /p/Base.java
package p;
public class Base {
    void packageOnly() {}
    private void hidden() {}
    public static void staticMethod() {}
    public void accept(int n) {}
}
//- /q/Main.java
package q;
import p.Base;
import java.util.Comparator;
import java.util.List;

interface Parent<T> {
    default void accept(T value) {}
    <U> void generic(U value);
    <U> U identity(U value);
}
interface Child extends Parent<String> {
    @Override void accept(String value);
    @Override boolean equals(Object other);
    @Override int hashCode();
    @Override String toString();
    @/*@interfaceTypo*/Override void typo();
}
interface CloneAttempt {
    @/*@clone*/Override Object clone();
}
abstract class Main extends Base implements Child {
    @/*@typo*/Override
    public String toSting() { return ""; }
    @/*@overload*/java.lang.Override public void accept(long n) {}
    @/*@hidden*/Override public void hidden() {}
    @/*@packageOnly*/Override public void packageOnly() {}
    @/*@staticMethod*/Override public static void staticMethod() {}
    @Override public void accept(String value) {}
    @Override public <V> void generic(V value) {}
    public <V> @Override V identity(V value) { return value; }
    public <V> @/*@genericTypo*/Override V identit(V value) { return value; }
    @Override public String toString() { return ""; }

    Object anonymous = new Comparator<String>() {
        @Override public int compare(String a, String b) { return 0; }
        @/*@anonTypo*/Override public int compar(String a, String b) { return 0; }
    };
    Comparator<String> diamond = new Comparator<>() {
        @Override public int compare(String a, String b) { return 0; }
    };
    void local() {
        class Local {
            @Override public String toString() { return ""; }
            @/*@localTypo*/Override public void typo() {}
        }
    }
}
abstract class Raw implements Parent {
    @Override public void accept(Object value) {}
    @Override public void generic(Object value) {}
    @Override public Object identity(Object value) { return value; }
}
class Outer<T> {
    class Inner {
        void set(T value) {}
    }
}
class Specialized extends Outer<String> {
    class Nested extends Inner {
        @Override void set(String value) {}
    }
}
interface Wild<T> {
    void consume(List<? extends T> values);
}
class WildObject implements Wild<Object> {
    @Override public void consume(List<?> values) {}
}
abstract class WildMismatch implements Wild<Object> {
    @/*@wildMismatch*/Override public void consume(List<? extends String> values) {}
}
record Value(int n) {
    @Override public int n() { return n; }
    @/*@recordTypo*/Override public int nn() { return n; }
}
enum Choice {
    FIRST {
        @Override public void run() {}
        @/*@constantTypo*/Override public void runn() {}
    };
    abstract void run();
    @Override public String toString() { return ""; }
    @/*@enumTypo*/Override public void typo() {}
}
class Custom {
    @interface Override {}
    @Override void notAnOverride() {}
}
abstract class Unknown extends Missing {
    @Override public void maybe() {}
}
//? diag invalid-override interfaceTypo
//? diag invalid-override clone
//? diag invalid-override typo
//? diag invalid-override overload
//? diag invalid-override hidden
//? diag invalid-override packageOnly
//? diag invalid-override staticMethod
//? diag invalid-override genericTypo
//? diag invalid-override anonTypo
//? diag invalid-override localTypo
//? diag invalid-override wildMismatch
//? diag invalid-override recordTypo
//? diag invalid-override constantTypo
//? diag invalid-override enumTypo
//? diag exact
