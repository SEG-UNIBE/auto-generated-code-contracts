/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.util.collections;

import java.util.LinkedList;

@SuppressWarnings("unchecked")
public class IdentitySet {

    private final LinkedList list = new LinkedList();

//@ requires (list!= null) && (list.length > 0);
    public boolean contains(Object o) {
        for (Object existing : list) {
            if (existing == o) {
                return true;
            }
        }
        return false;
    }

//@ ensures getList().size() == 0;
//@ ensures getList().contains(o);
//@ ensures \old(getList().size()) + 1 == getList().size()  ; 
    public void add(Object o) {
        list.add(o);
    }
}
