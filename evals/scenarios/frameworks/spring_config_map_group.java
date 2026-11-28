//- /src/main/java/app/App.java
package app;

class App {
}

//- /META-INF/spring-configuration-metadata.json lib:sms
{
  "groups": [
    {
      "name": "sms",
      "type": "org.example.sms.SmsProperties",
      "sourceType": "org.example.sms.SmsProperties"
    },
    {
      "name": "sms.blends",
      "type": "java.util.Map",
      "sourceType": "org.example.sms.SmsConfiguration",
      "sourceMethod": "blends()"
    }
  ],
  "properties": [
    {
      "name": "sms.config-type",
      "type": "java.lang.String",
      "sourceType": "org.example.sms.SmsProperties"
    }
  ]
}

//- /org/example/sms/SmsProperties.java lib:sms
package org.example.sms;

public class SmsProperties {
    private String configType;

    public void setConfigType(String configType) {
        this.configType = configType;
    }
}

//- /src/main/resources/application.properties
sms.config-type=a
sms.blends.config1.supplier=alibaba
sms.blends.config2.access-key-id=x
sms.blends.config2.templates[0].id=1
sms.typ/*@typo*/o=1

//? diag unknown-config-property typo
//? diag only unknown-config-property
