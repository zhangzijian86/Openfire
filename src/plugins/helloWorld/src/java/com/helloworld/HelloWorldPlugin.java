package com.helloworld;

import java.io.File;  

import org.jivesoftware.openfire.XMPPServer;  
import org.jivesoftware.openfire.container.Plugin;  
import org.jivesoftware.openfire.container.PluginManager;  
  
public class HelloWorldPlugin implements Plugin {  
    private XMPPServer server;  
  
    public HelloWorldPlugin() {  
  
    }  
  
    @Override  
    public void initializePlugin(PluginManager manager, File pluginDirectory) {  
        server = XMPPServer.getInstance();  
        System.out.println("HelloWorldPlugin----start");  
        System.out.println(server.getServerInfo());  
    }  
  
    @Override  
    public void destroyPlugin() {  
        System.out.println("HelloWorldPlugin----destroy");  
    }  
  
}  