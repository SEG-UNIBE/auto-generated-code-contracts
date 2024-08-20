/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.util.reflection;

import java.lang.annotation.Annotation;
import java.lang.reflect.Field;

import org.mockito.exceptions.base.MockitoException;
import org.mockito.internal.configuration.plugins.Plugins;
import org.mockito.internal.util.Checks;
import org.mockito.plugins.MemberAccessor;

/**
 * Represents an accessible instance field.
 *
 * Contains the instance reference on which the field can be read and write.
 */
public class InstanceField {
    private final Field field;
    private final Object instance;
    private FieldReader fieldReader;

    /**
     * Create a new InstanceField.
     *
     * @param field The field that should be accessed, note that no checks are performed to ensure
     *              the field belong to this instance class.
     * @param instance The instance from which the field shall be accessed.
     */
    public InstanceField(Field field, Object instance) {
        this.field = Checks.checkNotNull(field, "field");
        this.instance = Checks.checkNotNull(instance, "instance");
    }

    /**
     * Safely read the field.
     *
     * @return the field value.
     * @see FieldReader
     */
//@ requires reader()!= null;
    public Object read() {
        return reader().read();
    }

    /**
     * Set the given value to the field of this instance.
     *
     * @param value The value that should be written to the field.
     */
//@ requires field!= null;
//@ requires instance!= null;
    public void set(Object value) {
        MemberAccessor accessor = Plugins.getMemberAccessor();
        try {
            accessor.set(field, instance, value);
        } catch (IllegalAccessException e) {
            throw new MockitoException("Access to " + field + " was denied", e);
        }
    }

    /**
     * Check that the field is not null.
     *
     * @return <code>true</code> if <code>null</code>, else <code>false</code>.
     */
//@ ensures \result == reader().isNull();
    public boolean isNull() {
        return reader().isNull();
    }

    /**
     * Check if the field is annotated by the given annotation.
     *
     * @param annotationClass The annotation type to check.
     * @return <code>true</code> if the field is annotated by this annotation, else <code>false</code>.
     */
//@ ensures \result == (field.isAnnotationPresent(annotationClass));
    public boolean isAnnotatedBy(Class<? extends Annotation> annotationClass) {
        return field.isAnnotationPresent(annotationClass);
    }

    /**
     * Check if the field is synthetic.
     *
     * @return <code>true</code> if the field is synthetic, else <code>false</code>.
     */
//@ ensures \result == field.isSynthetic();
    public boolean isSynthetic() {
        return field.isSynthetic();
    }

    /**
     * Returns the annotation instance for the given annotation type.
     *
     * @param annotationClass Tha annotation type to retrieve.
     * @param <A> Type of the annotation.
     * @return The annotation instance.
     */
//@ ensures \result!= null;
    public <A extends Annotation> A annotation(Class<A> annotationClass) {
        return field.getAnnotation(annotationClass);
    }

    /**
     * Returns the JDK {@link Field} instance.
     *
     * @return The actual {@link Field} instance.
     */
//@ ensures \result == field;
    public Field jdkField() {
        return field;
    }

//@ requires field!= null;
    private FieldReader reader() {
        if (fieldReader == null) {
            fieldReader = new FieldReader(instance, field);
        }
        return fieldReader;
    }

    /**
     * Returns the name of the field.
     *
     * @return Name of the field.
     */
//@ requires field!= null;
    public String name() {
        return field.getName();
    }

//@ ensures \result!= null;
    @Override
    public String toString() {
        return name();
    }

//@ requires field!= null;
//@ requires instance!= null;
    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }

        InstanceField that = (InstanceField) o;
        return field.equals(that.field) && instance.equals(that.instance);
    }

//@ requires field!= null;
//@ requires instance!= null;
    @Override
    public int hashCode() {
        int result = field.hashCode();
        result = 31 * result + instance.hashCode();
        return result;
    }
}
