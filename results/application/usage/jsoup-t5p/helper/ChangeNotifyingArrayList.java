package org.jsoup.helper;

import java.util.ArrayList;
import java.util.Collection;

/**
 * Implementation of ArrayList that watches out for changes to the contents.
 */
public abstract class ChangeNotifyingArrayList<E> extends ArrayList<E> {
    public ChangeNotifyingArrayList(int initialCapacity) {
        super(initialCapacity);
    }

    public abstract void onContentsChanged();

//@ ensures contents == null;
//@ ensures this.contents == null;
//@ requires 0 <= index && index < size();
    @Override
    public E set(int index, E element) {
        onContentsChanged();
        return super.set(index, element);
    }

//@ ensures this.contents == e.getContents();
    @Override
    public boolean add(E e) {
        onContentsChanged();
        return super.add(e);
    }

//@ requires 0 <= index && index < size();
    @Override
    public void add(int index, E element) {
        onContentsChanged();
        super.add(index, element);
    }

//@ requires 0 <= index && index < size();
    @Override
    public E remove(int index) {
        onContentsChanged();
        return super.remove(index);
    }

//@ requires contents!= null;
//@ ensures  super.remove(o);
    @Override
    public boolean remove(Object o) {
        onContentsChanged();
        return super.remove(o);
    }

//@ requires initialSize > 0 && sizeIncrease >= 0 && sizeMultiple >= 1;
//@ requires!(sizeIncrease == 0 && sizeMultiple == 1)
    @Override
    public void clear() {
        onContentsChanged();
        super.clear();
    }

//@ requires c!= null;
//@ ensures \result == (e == this);
    @Override
    public boolean addAll(Collection<? extends E> c) {
        onContentsChanged();
        return super.addAll(c);
    }

//@ requires 0 <= index && index < size();
    @Override
    public boolean addAll(int index, Collection<? extends E> c) {
        onContentsChanged();
        return super.addAll(index, c);
    }

//@ requires 0 <= fromIndex && fromIndex < size();
//@ requires 0 <= toIndex && toIndex < size();
    @Override
    protected void removeRange(int fromIndex, int toIndex) {
        onContentsChanged();
        super.removeRange(fromIndex, toIndex);
    }

//@ requires c!= null;
//@ requires (a == c || a == m_c);
    @Override
    public boolean removeAll(Collection<?> c) {
        onContentsChanged();
        return super.removeAll(c);
    }

//@ requires c!= null;
//@ ensures \result == this.c;
    @Override
    public boolean retainAll(Collection<?> c) {
        onContentsChanged();
        return super.retainAll(c);
    }

}
