/*
 * Copyright (c) 2016 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.configuration.plugins;

import org.mockito.plugins.PluginSwitch;

class DefaultPluginSwitch implements PluginSwitch {
//@ ensures \result == true;
    @Override
    public boolean isEnabled(String pluginClassName) {
        return true;
    }
}
