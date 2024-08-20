package org.jsoup.nodes;

import java.io.IOException;

/**
 A data node, for contents of style, script tags etc, where contents should not show in text().

 @author Jonathan Hedley, jonathan@hedley.net */
public class DataNode extends LeafNode {

    /**
     Create a new DataNode.
     @param data data contents
     */
    public DataNode(String data) {
        value = data;
    }

//@ requires nodeName()!= null;
    public String nodeName() {
        return "#data";
    }

    /**
     Get the data contents of this node. Will be unescaped and with original new lines, space etc.
     @return data
     */
//@ ensures \result!= null;
    public String getWholeData() {
        return coreValue();
    }

    /**
     * Set the data contents of this node.
     * @param data unencoded data
     * @return this node, for chaining
     */
//@ requires data!= null;
//@ ensures \result.coreValue(data);
    public DataNode setWholeData(String data) {
        coreValue(data);
        return this;
    }

//@ requires depth >= 0
//@ requires out!= null
//@ requires out.isOpen;
//@ requires accum!= null
//@ requires data!= null;
    @Override
    void outerHtmlHead(Appendable accum, int depth, Document.OutputSettings out) throws IOException {
        accum.append(getWholeData()); // data is not escaped in return from data nodes, so " in script, style is plain
    }

//@ requires depth >= 0;
//@ ensures out!= null;
    @Override
    void outerHtmlTail(Appendable accum, int depth, Document.OutputSettings out) {}

//@ ensures \result!= null;
    @Override
    public String toString() {
        return outerHtml();
    }

//@ requires nodes!= null;
//@ ensures  this.nodes == nodes;
//@ requires nodes!= null;
//@ requires \nonnullelements(nodes);
    @Override
    public DataNode clone() {
        return (DataNode) super.clone();
    }
}
