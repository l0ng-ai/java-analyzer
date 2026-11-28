//- /lombok/Getter.java
package lombok;
public @interface Getter {}
//- /lombok/Singular.java
package lombok;
public @interface Singular { String value() default ""; }
//- /lombok/Builder.java
package lombok;
public @interface Builder { @interface Default {} }
//- /lombok/experimental/SuperBuilder.java
package lombok.experimental;
public @interface SuperBuilder { String builderMethodName() default "builder"; String buildMethodName() default "build"; boolean toBuilder() default false; String setterPrefix() default ""; }
//- /lombok/extern/jackson/Jacksonized.java
package lombok.extern.jackson;
public @interface Jacksonized {}
//- /app/Entity.java
package app;

import lombok.Builder;
import lombok.Getter;
import lombok.experimental.SuperBuilder;

// 抽象的泛型根类
@Getter
@SuperBuilder(toBuilder = true)
public abstract class Entity<ID> {
    private ID /*@id*/id;
    @Builder.Default
    private long version = 1;
}
//- /app/Animal.java
package app;

import java.util.List;
import lombok.Getter;
import lombok.Singular;
import lombok.experimental.SuperBuilder;

@Getter
@SuperBuilder(toBuilder = true)
public class Animal extends Entity<Long> {
    private String /*@name*/name;
    @Singular
    private List<String> tags;
}
//- /app/Dog.java
package app;

import lombok.experimental.SuperBuilder;
import lombok.extern.jackson.Jacksonized;

@Jacksonized
@SuperBuilder(toBuilder = true)
public class Dog extends Animal {
    private int /*@bark*/bark;
}
//- /app/Holder.java
package app;

import lombok.experimental.SuperBuilder;

// 非抽象的泛型根类
@SuperBuilder(toBuilder = true)
public class Holder<V> {
    private V payload;
}
//- /app/Named.java
package app;

import lombok.experimental.SuperBuilder;

@SuperBuilder(toBuilder = true)
public class Named extends Holder<String> {
    private String label;
}
//- /app/Main.java
package app;

import java.util.List;

class Main {
    Dog run() {
        Dog dog = Dog.builder().id(7L).version(2).name("rex").tag("a").bark(3).build();
        var /*@built*/built = Dog.builder().name("x").bark(1)./*@after_chain*/build();
        var /*@b*/b = Dog.builder();
        Dog copy = dog.toBuilder().bark(4).build();
        Animal animal = Animal.builder().name("cat").tags(List.of("a")).clearTags().build();
        Animal again = animal.toBuilder().id(1L).build();
        Long id = again.getId();
        String name = copy.getName() + built.getTags().size() + id;
        Dog.builder()./*@parent_setter*/name(name)./*@chain*/bark(1);
        b.version(3);
        // 父类的设置方法返回子类的构建器
        var /*@parent_first*/parentFirst = Dog.builder().name("x");
        parentFirst.bark(2);
        // 抽象类没有 builder()
        Entity./*@no_builder*/class.getName();
        var /*@holder*/holder = Holder.<Integer>builder().payload(1).build();
        Named named = Named.builder().payload("p").label("l").build();
        var /*@named_copy*/namedCopy = named.toBuilder().payload("q").label(holder.toString()).build();
        namedCopy.toBuilder();
        return Dog.builder()./*@members*/build();
    }
}
//? hover built ~ "Dog built"
//? hover b ~ "DogBuilder<?, ?> b"
//? def parent_setter -> name
//? def chain -> bark
//? hover chain ~ "public Dog.DogBuilder<?, ?> bark(int bark)"
//? hover parent_setter ~ "public Dog.DogBuilder<?, ?> name(String name)"
//? complete after_chain has build bark
//? complete members has id version name tag tags clearTags bark build
//? hover parent_first ~ "DogBuilder<?, ?> parentFirst"
//? complete no_builder lacks builder toBuilder
//? hover holder ~ "Holder<Integer> holder"
//? hover named_copy ~ "Named namedCopy"
//? diag exact
