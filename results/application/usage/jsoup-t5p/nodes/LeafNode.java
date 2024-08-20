package org.jsoup.nodes;

import java.util.List;

abstract class LeafNode extends Node {
    Object value; // either a string value, or an attribute map (in the rare case multiple attributes are set)

//@ ensures \result == (value instanceof Attributes);
    protected final boolean hasAttributes() {
        return value instanceof Attributes;
    }

//@ requires value!= null;
//@ ensures this.value == value;
//@ requires value!= null;
//@ ensures \result == this.value;
    @Override
    public final Attributes attributes() {
        ensureAttributes();
        return (Attributes) value;
    }

//@ requires attributeName!= null;
//@ requires index >= 0;
//@ ensures  attributeName == attributeName;
//@ ensures  index == index;
//@ requires attributeName!= null;
//@ requires index >= 0;
//@ ensures  attributeName == attributeName;
//@ ensures  index == index;
//@ requires attributeName!= null;
//@ requires index >= 0;
//@ ensures  attributeName == attributeName;
//@ ensures  index == index;
    private void ensureAttributes() {
        if (!hasAttributes()) {
            Object coreValue = value;
            Attributes attributes = new Attributes();
            value = attributes;
            if (coreValue != null)
                attributes.put(nodeName(), (String) coreValue);
        }
    }

//@ requires nodeName()!= null;
    String coreValue() {
        return attr(nodeName());
    }

//@ requires attrName(nodeName());
//@ ensures  attr(nodeName(), value);
    void coreValue(String value) {
        attr(nodeName(), value);
    }

//@ requires nodeName()!= null;
    @Override
    public String attr(String key) {
        if (!hasAttributes()) {
            return nodeName().equals(key) ? (String) value : EmptyString;
        }
        return super.attr(key);
    }

//@ requires isOpen;
//@ ensures isOpen;
    @Override
    public Node attr(String key, String value) {
        if (!hasAttributes() && key.equals(nodeName())) {
            this.value = value;
        } else {
            ensureAttributes();
            super.attr(key, value);
        }
        return this;
    }

//@ requires isOpen;
//@ ensures isOpen;
    @Override
    public boolean hasAttr(String key) {
        ensureAttributes();
        return super.hasAttr(key);
    }

//@ requires isOpen;
//@ ensures isOpen;
    @Override
    public Node removeAttr(String key) {
        ensureAttributes();
        return super.removeAttr(key);
    }

//@ requires isOpen;
//@ ensures isOpen;
    @Override
    public String absUrl(String key) {
        ensureAttributes();
        return super.absUrl(key);
    }

//@ requires parent()!= null;
    @Override
    public String baseUri() {
        return hasParent() ? parent().baseUri() : "";
    }

//@ requires baseUri!= null;
    @Override
    protected void doSetBaseUri(String baseUri) {
        // noop
    }

//@ requires 0 <= first;
//@ requires 0 <= toCopy;
//@ requires first + toCopy <= source.numChildren();
    @Override
    public int childNodeSize() {
        return 0;
    }

//@ ensures \result == this;
    @Override
    public Node empty() {
        return this;
    }

//@ ensures \result == EmptyNodes;
    @Override
    protected List<Node> ensureChildNodes() {
        return EmptyNodes;
    }

//@ requires parent!= null;
    @Override
    protected LeafNode doClone(Node parent) {
        LeafNode clone = (LeafNode) super.doClone(parent);

        // Object value could be plain string or attributes - need to clone
        if (hasAttributes())
            clone.value = ((Attributes) value).clone();

        return clone;
    }
}
