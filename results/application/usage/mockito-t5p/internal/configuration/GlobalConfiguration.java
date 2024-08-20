/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.configuration;

import java.io.Serializable;

import org.mockito.configuration.DefaultMockitoConfiguration;
import org.mockito.configuration.IMockitoConfiguration;
import org.mockito.internal.configuration.plugins.Plugins;
import org.mockito.stubbing.Answer;

/**
 * Thread-safe wrapper on user-defined org.mockito.configuration.MockitoConfiguration implementation
 */
public class GlobalConfiguration implements IMockitoConfiguration, Serializable {
    private static final long serialVersionUID = -2860353062105505938L;

    private static final ThreadLocal<IMockitoConfiguration> GLOBAL_CONFIGURATION =
            new ThreadLocal<>();

    // back door for testing
//@ ensures \result == GLOBAL_CONFIGURATION.get();
    IMockitoConfiguration getIt() {
        return GLOBAL_CONFIGURATION.get();
    }

    public GlobalConfiguration() {
        // Configuration should be loaded only once but I cannot really test it
        if (GLOBAL_CONFIGURATION.get() == null) {
            GLOBAL_CONFIGURATION.set(createConfig());
        }
    }

//@ ensures \result!= null;
    private IMockitoConfiguration createConfig() {
        IMockitoConfiguration defaultConfiguration = new DefaultMockitoConfiguration();
        IMockitoConfiguration config = new ClassPathLoader().loadConfiguration();
        if (config != null) {
            return config;
        } else {
            return defaultConfiguration;
        }
    }

//@ ensures true;
    public static void validate() {
        GlobalConfiguration unused = new GlobalConfiguration();
    }

//@ ensures \result!= null;
    public org.mockito.plugins.AnnotationEngine tryGetPluginAnnotationEngine() {
        return Plugins.getAnnotationEngine();
    }

//@ ensures \result == false;
    @Override
    public boolean cleansStackTrace() {
        return GLOBAL_CONFIGURATION.get().cleansStackTrace();
    }

//@ ensures \result == GLOBAL_CONFIGURATION.get().enableClassCache();
    @Override
    public boolean enableClassCache() {
        return GLOBAL_CONFIGURATION.get().enableClassCache();
    }

//@ requires isOpen;
//@ ensures isOpen;
    @Override
    public Answer<Object> getDefaultAnswer() {
        return GLOBAL_CONFIGURATION.get().getDefaultAnswer();
    }
}
