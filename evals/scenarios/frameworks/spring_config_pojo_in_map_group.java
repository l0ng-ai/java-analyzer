//- /src/main/java/app/App.java
package app;

class App {
}

//- /META-INF/spring-configuration-metadata.json lib:catalog
{
  "groups": [
    { "name": "catalog", "type": "org.example.catalog.Catalog" },
    { "name": "catalog.entries", "type": "java.util.Map<java.lang.String,org.example.catalog.Pojo>" },
    { "name": "catalog.entries.fixed", "type": "org.example.catalog.Pojo" }
  ],
  "properties": [
    {
      "name": "catalog.entries.fixed.title",
      "type": "java.lang.String",
      "sourceType": "org.example.catalog.Pojo"
    }
  ]
}

//- /org/example/catalog/Pojo.java lib:catalog
package org.example.catalog;

public class Pojo {
    private String title;

    public void setTitle(String title) {
        this.title = title;
    }
}

//- /src/main/resources/application.properties
catalog.entries.fixed.title=ok
catalog.entries.fixed.ti/*@typo*/tel=x
catalog.entries.dynamic.anything=1

//? diag unknown-config-property typo
//? diag only unknown-config-property
