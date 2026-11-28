//- /src/main/java/app/App.java
package app;

class App {
}

//- /META-INF/spring-configuration-metadata.json lib:road
{
  "groups": [
    {
      "name": "road",
      "type": "org.example.road.RoadMap",
      "sourceType": "org.example.road.RoadMap"
    }
  ],
  "properties": [
    {
      "name": "road.title",
      "type": "java.lang.String",
      "sourceType": "org.example.road.RoadMap"
    }
  ]
}

//- /org/example/road/RoadMap.java lib:road
package org.example.road;

public class RoadMap {
    private String title;

    public void setTitle(String title) {
        this.title = title;
    }
}

//- /src/main/resources/application.properties
road.title=x
road.title-ty/*@typo*/po=x

//? diag unknown-config-property typo
//? diag only unknown-config-property
