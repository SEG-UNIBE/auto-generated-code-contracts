package org.jsoup.nodes;

import java.io.IOException;

/**
 * A Character Data node, to support CDATA sections.
 */
public class CDataNode extends TextNode {
    public CDataNode(String text) {
        super(text);
    }

//@ requires length > 0;
    @Override
    public String nodeName() {
        return "#cdata";
    }

    /**
     * Get the unencoded, <b>non-normalized</b> text content of this CDataNode.
     * @return unencoded, non-normalized text
     */
//@ ensures \result!= null;
    @Override
    public String text() {
        return getWholeText();
    }

//@ requires depth >= 0
    @Override
    void outerHtmlHead(Appendable accum, int depth, Document.OutputSettings out) throws IOException {
        accum
            .append("<![CDATA[")
            .append(getWholeText());
    }

//@ requires depth >= 0
    @Override
    void outerHtmlTail(Appendable accum, int depth, Document.OutputSettings out) throws IOException {
        accum.append("]]>");
    }

//@ requires data!= null;
//@ ensures  this.data == data;
//@ requires data!= null;
//@ ensures  \result == this;
    @Override
    public CDataNode clone() {
        return (CDataNode) super.clone();
    }
}
