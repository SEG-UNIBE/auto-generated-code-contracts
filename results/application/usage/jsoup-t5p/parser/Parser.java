package org.jsoup.parser;

import org.jsoup.nodes.Document;
import org.jsoup.nodes.Element;
import org.jsoup.nodes.Node;

import java.io.Reader;
import java.io.StringReader;
import java.util.List;

/**
 Parses HTML or XML into a {@link org.jsoup.nodes.Document}. Generally, it is simpler to use one of the parse methods in
 {@link org.jsoup.Jsoup}.
 <p>Note that a Parser instance object is not threadsafe. To reuse a Parser configuration in a multi-threaded
 environment, use {@link #newInstance()} to make copies. */
public class Parser {
    private TreeBuilder treeBuilder;
    private ParseErrorList errors;
    private ParseSettings settings;
    private boolean trackPosition = false;

    /**
     * Create a new Parser, using the specified TreeBuilder
     * @param treeBuilder TreeBuilder to use to parse input into Documents.
     */
    public Parser(TreeBuilder treeBuilder) {
        this.treeBuilder = treeBuilder;
        settings = treeBuilder.defaultSettings();
        errors = ParseErrorList.noTracking();
    }

    /**
     Creates a new Parser as a deep copy of this; including initializing a new TreeBuilder. Allows independent (multi-threaded) use.
     @return a copied parser
     */
//@ requires this.root!= null;
    public Parser newInstance() {
        return new Parser(this);
    }

    private Parser(Parser copy) {
        treeBuilder = copy.treeBuilder.newInstance(); // because extended
        errors = new ParseErrorList(copy.errors); // only copies size, not contents
        settings = new ParseSettings(copy.settings);
        trackPosition = copy.trackPosition;
    }
    
//@ requires html!= null;
//@ requires baseUri!= null;
    public Document parseInput(String html, String baseUri) {
        return treeBuilder.parse(new StringReader(html), baseUri, this);
    }

//@ requires inputHtml!= null && baseUri!= null;
    public Document parseInput(Reader inputHtml, String baseUri) {
        return treeBuilder.parse(inputHtml, baseUri, this);
    }

//@ requires fragment!= null && context!= null;
//@ requires baseUri!= null;
    public List<Node> parseFragmentInput(String fragment, Element context, String baseUri) {
        return treeBuilder.parseFragment(fragment, context, baseUri, this);
    }
    // gets & sets
    /**
     * Get the TreeBuilder currently in use.
     * @return current TreeBuilder.
     */
//@ ensures \result!= null;
    public TreeBuilder getTreeBuilder() {
        return treeBuilder;
    }

    /**
     * Update the TreeBuilder used when parsing content.
     * @param treeBuilder new TreeBuilder
     * @return this, for chaining
     */
//@ requires treeBuilder!= null;
//@ ensures this.treeBuilder == treeBuilder;
//@ requires treeBuilder!= null;
//@ ensures treeBuilder.parser == this;
    public Parser setTreeBuilder(TreeBuilder treeBuilder) {
        this.treeBuilder = treeBuilder;
        treeBuilder.parser = this;
        return this;
    }

    /**
     * Check if parse error tracking is enabled.
     * @return current track error state.
     */
//@ ensures \result == errors.getMaxSize();
    public boolean isTrackErrors() {
        return errors.getMaxSize() > 0;
    }

    /**
     * Enable or disable parse error tracking for the next parse.
     * @param maxErrors the maximum number of errors to track. Set to 0 to disable.
     * @return this, for chaining
     */
//@ ensures errors == null;
//@ ensures errors.size() == 0;
    public Parser setTrackErrors(int maxErrors) {
        errors = maxErrors > 0 ? ParseErrorList.tracking(maxErrors) : ParseErrorList.noTracking();
        return this;
    }

    /**
     * Retrieve the parse errors, if any, from the last parse.
     * @return list of parse errors, up to the size of the maximum errors tracked.
     * @see #setTrackErrors(int)
     */
//@ ensures \result == errors;
    public ParseErrorList getErrors() {
        return errors;
    }

    /**
     Test if position tracking is enabled. If it is, Nodes will have a Position to track where in the original input
     source they were created from. By default, tracking is not enabled.
     * @return current track position setting
     */
//@ ensures \result == trackPosition;
    public boolean isTrackPosition() {
        return trackPosition;
    }

    /**
     Enable or disable source position tracking. If enabled, Nodes will have a Position to track where in the original
     input source they were created from.
     @param trackPosition position tracking setting; {@code true} to enable
     @return this Parser, for chaining
     */
//@ ensures trackPosition == trackPosition;
    public Parser setTrackPosition(boolean trackPosition) {
        this.trackPosition = trackPosition;
        return this;
    }

    /**
     Update the ParseSettings of this Parser, to control the case sensitivity of tags and attributes.
     * @param settings the new settings
     * @return this Parser
     */
//@ ensures settings == settings;
    public Parser settings(ParseSettings settings) {
        this.settings = settings;
        return this;
    }

    /**
     Gets the current ParseSettings for this Parser
     * @return current ParseSettings
     */
//@ ensures \result == settings;
    public ParseSettings settings() {
        return settings;
    }

    /**
     (An internal method, visible for Element. For HTML parse, signals that script and style text should be treated as
     Data Nodes).
     */
//@ ensures \result == getTreeBuilder().isContentForTagData(normalName);
    public boolean isContentForTagData(String normalName) {
        return getTreeBuilder().isContentForTagData(normalName);
    }

    // static parse functions below
    /**
     * Parse HTML into a Document.
     *
     * @param html HTML to parse
     * @param baseUri base URI of document (i.e. original fetch location), for resolving relative URLs.
     *
     * @return parsed Document
     */
//@ requires html!= null;
//@ requires baseUri!= null;
    public static Document parse(String html, String baseUri) {
        TreeBuilder treeBuilder = new HtmlTreeBuilder();
        return treeBuilder.parse(new StringReader(html), baseUri, new Parser(treeBuilder));
    }

    /**
     * Parse a fragment of HTML into a list of nodes. The context element, if supplied, supplies parsing context.
     *
     * @param fragmentHtml the fragment of HTML to parse
     * @param context (optional) the element that this HTML fragment is being parsed for (i.e. for inner HTML). This
     * provides stack context (for implicit element creation).
     * @param baseUri base URI of document (i.e. original fetch location), for resolving relative URLs.
     *
     * @return list of nodes parsed from the input HTML. Note that the context element, if supplied, is not modified.
     */
//@ requires fragmentHtml!= null;
//@ requires context!= null;
//@ requires baseUri!= null;
//@ ensures \fresh(\result);
    public static List<Node> parseFragment(String fragmentHtml, Element context, String baseUri) {
        HtmlTreeBuilder treeBuilder = new HtmlTreeBuilder();
        return treeBuilder.parseFragment(fragmentHtml, context, baseUri, new Parser(treeBuilder));
    }

    /**
     * Parse a fragment of HTML into a list of nodes. The context element, if supplied, supplies parsing context.
     *
     * @param fragmentHtml the fragment of HTML to parse
     * @param context (optional) the element that this HTML fragment is being parsed for (i.e. for inner HTML). This
     * provides stack context (for implicit element creation).
     * @param baseUri base URI of document (i.e. original fetch location), for resolving relative URLs.
     * @param errorList list to add errors to
     *
     * @return list of nodes parsed from the input HTML. Note that the context element, if supplied, is not modified.
     */
//@ requires fragmentHtml!= null;
//@ requires context!= null;
//@ requires baseUri!= null;
//@ ensures \result!= null && \nonnullelements(result);
    public static List<Node> parseFragment(String fragmentHtml, Element context, String baseUri, ParseErrorList errorList) {
        HtmlTreeBuilder treeBuilder = new HtmlTreeBuilder();
        Parser parser = new Parser(treeBuilder);
        parser.errors = errorList;
        return treeBuilder.parseFragment(fragmentHtml, context, baseUri, parser);
    }

    /**
     * Parse a fragment of XML into a list of nodes.
     *
     * @param fragmentXml the fragment of XML to parse
     * @param baseUri base URI of document (i.e. original fetch location), for resolving relative URLs.
     * @return list of nodes parsed from the input XML.
     */
//@ requires fragmentXml!= null;
//@ requires baseUri!= null;
    public static List<Node> parseXmlFragment(String fragmentXml, String baseUri) {
        XmlTreeBuilder treeBuilder = new XmlTreeBuilder();
        return treeBuilder.parseFragment(fragmentXml, baseUri, new Parser(treeBuilder));
    }

    /**
     * Parse a fragment of HTML into the {@code body} of a Document.
     *
     * @param bodyHtml fragment of HTML
     * @param baseUri base URI of document (i.e. original fetch location), for resolving relative URLs.
     *
     * @return Document, with empty head, and HTML parsed into body
     */
//@ requires baseUri!= null;
//@ requires bodyHtml!= null;
    public static Document parseBodyFragment(String bodyHtml, String baseUri) {
        Document doc = Document.createShell(baseUri);
        Element body = doc.body();
        List<Node> nodeList = parseFragment(bodyHtml, body, baseUri);
        Node[] nodes = nodeList.toArray(new Node[0]); // the node list gets modified when re-parented
        for (int i = nodes.length - 1; i > 0; i--) {
            nodes[i].remove();
        }
        for (Node node : nodes) {
            body.appendChild(node);
        }
        return doc;
    }

    /**
     * Utility method to unescape HTML entities from a string
     * @param string HTML escaped string
     * @param inAttribute if the string is to be escaped in strict mode (as attributes are)
     * @return an unescaped string
     */
//@ requires string!= null;
//@ requires inAttribute || string.length() > 0;
    public static String unescapeEntities(String string, boolean inAttribute) {
        Tokeniser tokeniser = new Tokeniser(new CharacterReader(string), ParseErrorList.noTracking());
        return tokeniser.unescapeEntities(inAttribute);
    }

    // builders

    /**
     * Create a new HTML parser. This parser treats input as HTML5, and enforces the creation of a normalised document,
     * based on a knowledge of the semantics of the incoming tags.
     * @return a new HTML parser.
     */
//@ ensures \result!= null;
    public static Parser htmlParser() {
        return new Parser(new HtmlTreeBuilder());
    }

    /**
     * Create a new XML parser. This parser assumes no knowledge of the incoming tags and does not treat it as HTML,
     * rather creates a simple tree directly from the input.
     * @return a new simple XML parser.
     */
//@ requires new XmlTreeBuilder()!= null;
    public static Parser xmlParser() {
        return new Parser(new XmlTreeBuilder());
    }
}
