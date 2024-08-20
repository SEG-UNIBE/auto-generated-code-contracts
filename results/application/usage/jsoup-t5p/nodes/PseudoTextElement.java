package org.jsoup.nodes;

import org.jsoup.parser.Tag;

/**
 * Represents a {@link TextNode} as an {@link Element}, to enable text nodes to be selected with
 * the {@link org.jsoup.select.Selector} {@code :matchText} syntax.
 */
public class PseudoTextElement extends Element {

    public PseudoTextElement(Tag tag, String baseUri, Attributes attributes) {
        super(tag, baseUri, attributes);
    }

//@ requires depth >= 0;
//@ ensures outerHtmlHead(accum, depth, out);
    @Override
    void outerHtmlHead(Appendable accum, int depth, Document.OutputSettings out) {
    }

//@ requires depth >= 0
    @Override
    void outerHtmlTail(Appendable accum, int depth, Document.OutputSettings out) {
    }
}
