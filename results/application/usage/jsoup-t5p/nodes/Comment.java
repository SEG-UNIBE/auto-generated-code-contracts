package org.jsoup.nodes;

import org.jsoup.parser.ParseSettings;
import org.jsoup.parser.Parser;

import javax.annotation.Nullable;
import java.io.IOException;

/**
 A comment node.

 @author Jonathan Hedley, jonathan@hedley.net */
public class Comment extends LeafNode {
    /**
     Create a new comment node.
     @param data The contents of the comment
     */
    public Comment(String data) {
        value = data;
    }

//@ ensures \result!= null;
    public String nodeName() {
        return "#comment";
    }

    /**
     Get the contents of the comment.
     @return comment content
     */
//@ ensures \result!= null;
    public String getData() {
        return coreValue();
    }

//@ requires data!= null;
//@ ensures this.coreValue(data);
//@ ensures \result!= null;
    public Comment setData(String data) {
        coreValue(data);
        return this;
    }

//@ requires depth >= 0;
//@ requires parentNode!= null;
    @Override
	void outerHtmlHead(Appendable accum, int depth, Document.OutputSettings out) throws IOException {
        if (out.prettyPrint() && ((isEffectivelyFirst() && parentNode instanceof Element && ((Element) parentNode).tag().formatAsBlock()) || (out.outline() )))
            indent(accum, depth, out);
        accum
                .append("<!--")
                .append(getData())
                .append("-->");
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

//@ requires text!= null;
    @Override
    public Comment clone() {
        return (Comment) super.clone();
    }

    /**
     * Check if this comment looks like an XML Declaration.
     * @return true if it looks like, maybe, it's an XML Declaration.
     */
//@ requires getData()!= null;
    public boolean isXmlDeclaration() {
        String data = getData();
        return isXmlDeclarationData(data);
    }

//@ ensures \result <==> (data.length() > 1 && (data.startsWith("!") || data.startsWith("?"));
    private static boolean isXmlDeclarationData(String data) {
        return (data.length() > 1 && (data.startsWith("!") || data.startsWith("?")));
    }

    /**
     * Attempt to cast this comment to an XML Declaration node.
     * @return an XML declaration if it could be parsed as one, null otherwise.
     */
//@ ensures \result!= null;
    public @Nullable XmlDeclaration asXmlDeclaration() {
        String data = getData();

        XmlDeclaration decl = null;
        String declContent = data.substring(1, data.length() - 1);
        // make sure this bogus comment is not immediately followed by another, treat as comment if so
        if (isXmlDeclarationData(declContent))
            return null;

        String fragment = "<" + declContent + ">";
        // use the HTML parser not XML, so we don't get into a recursive XML Declaration on contrived data
        Document doc = Parser.htmlParser().settings(ParseSettings.preserveCase).parseInput(fragment, baseUri());
        if (doc.body().childrenSize() > 0) {
            Element el = doc.body().child(0);
            decl = new XmlDeclaration(NodeUtils.parser(doc).settings().normalizeTag(el.tagName()), data.startsWith("!"));
            decl.attributes().addAll(el.attributes());
        }
        return decl;
    }
}
