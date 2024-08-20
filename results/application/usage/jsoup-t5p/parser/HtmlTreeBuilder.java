package org.jsoup.parser;

import org.jsoup.helper.Validate;
import org.jsoup.internal.StringUtil;
import org.jsoup.nodes.CDataNode;
import org.jsoup.nodes.Comment;
import org.jsoup.nodes.DataNode;
import org.jsoup.nodes.Document;
import org.jsoup.nodes.Element;
import org.jsoup.nodes.FormElement;
import org.jsoup.nodes.Node;
import org.jsoup.nodes.TextNode;
import org.jsoup.parser.Token.StartTag;

import javax.annotation.Nullable;
import javax.annotation.ParametersAreNonnullByDefault;
import java.io.Reader;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.List;

import static org.jsoup.internal.StringUtil.inSorted;
import static org.jsoup.parser.HtmlTreeBuilderState.Constants.InTableFoster;

/**
 * HTML Tree Builder; creates a DOM from Tokens.
 */
public class HtmlTreeBuilder extends TreeBuilder {
    // tag searches. must be sorted, used in inSorted. HtmlTreeBuilderTest validates they're sorted.
    static final String[] TagsSearchInScope = new String[]{"applet", "caption", "html", "marquee", "object", "table", "td", "th"};
    static final String[] TagSearchList = new String[]{"ol", "ul"};
    static final String[] TagSearchButton = new String[]{"button"};
    static final String[] TagSearchTableScope = new String[]{"html", "table"};
    static final String[] TagSearchSelectScope = new String[]{"optgroup", "option"};
    static final String[] TagSearchEndTags = new String[]{"dd", "dt", "li", "optgroup", "option", "p", "rb", "rp", "rt", "rtc"};
    static final String[] TagThoroughSearchEndTags = new String[]{"caption", "colgroup", "dd", "dt", "li", "optgroup", "option", "p", "rb", "rp", "rt", "rtc", "tbody", "td", "tfoot", "th", "thead", "tr"};
    static final String[] TagSearchSpecial = new String[]{"address", "applet", "area", "article", "aside", "base", "basefont", "bgsound",
        "blockquote", "body", "br", "button", "caption", "center", "col", "colgroup", "command", "dd",
        "details", "dir", "div", "dl", "dt", "embed", "fieldset", "figcaption", "figure", "footer", "form",
        "frame", "frameset", "h1", "h2", "h3", "h4", "h5", "h6", "head", "header", "hgroup", "hr", "html",
        "iframe", "img", "input", "isindex", "li", "link", "listing", "marquee", "menu", "meta", "nav",
        "noembed", "noframes", "noscript", "object", "ol", "p", "param", "plaintext", "pre", "script",
        "section", "select", "style", "summary", "table", "tbody", "td", "textarea", "tfoot", "th", "thead",
        "title", "tr", "ul", "wbr", "xmp"};

    public static final int MaxScopeSearchDepth = 100; // prevents the parser bogging down in exceptionally broken pages

    private HtmlTreeBuilderState state; // the current state
    private HtmlTreeBuilderState originalState; // original / marked state

    private boolean baseUriSetFromDoc;
    private @Nullable Element headElement; // the current head element
    private @Nullable FormElement formElement; // the current form element
    private @Nullable Element contextElement; // fragment parse context -- could be null even if fragment parsing
    private ArrayList<Element> formattingElements; // active (open) formatting elements
    private ArrayList<HtmlTreeBuilderState> tmplInsertMode; // stack of Template Insertion modes
    private List<Token.Character> pendingTableCharacters; // chars in table to be shifted out
    private Token.EndTag emptyEnd; // reused empty end tag

    private boolean framesetOk; // if ok to go into frameset
    private boolean fosterInserts; // if next inserts should be fostered
    private boolean fragmentParsing; // if parsing a fragment of html

//@ ensures \result == ParseSettings.htmlDefault;
    ParseSettings defaultSettings() {
        return ParseSettings.htmlDefault;
    }

//@ ensures \result!= null;
    @Override
    HtmlTreeBuilder newInstance() {
        return new HtmlTreeBuilder();
    }

//@ requires baseUri!= null;
//@ ensures state == HtmlTreeBuilderState.Initial;
//@ requires originalState!= null;
    @Override @ParametersAreNonnullByDefault
    protected void initialiseParse(Reader input, String baseUri, Parser parser) {
        super.initialiseParse(input, baseUri, parser);

        // this is a bit mucky. todo - probably just create new parser objects to ensure all reset.
        state = HtmlTreeBuilderState.Initial;
        originalState = null;
        baseUriSetFromDoc = false;
        headElement = null;
        formElement = null;
        contextElement = null;
        formattingElements = new ArrayList<>();
        tmplInsertMode = new ArrayList<>();
        pendingTableCharacters = new ArrayList<>();
        emptyEnd = new Token.EndTag();
        framesetOk = true;
        fosterInserts = false;
        fragmentParsing = false;
    }

//@ requires context!= null;
//@ requires baseUri!= null;
    List<Node> parseFragment(String inputFragment, @Nullable Element context, String baseUri, Parser parser) {
        // context may be null
        state = HtmlTreeBuilderState.Initial;
        initialiseParse(new StringReader(inputFragment), baseUri, parser);
        contextElement = context;
        fragmentParsing = true;
        Element root = null;

        if (context != null) {
            if (context.ownerDocument() != null) // quirks setup:
                doc.quirksMode(context.ownerDocument().quirksMode());

            // initialise the tokeniser state:
            String contextTag = context.normalName();
            switch (contextTag) {
                case "title":
                case "textarea":
                    tokeniser.transition(TokeniserState.Rcdata);
                    break;
                case "iframe":
                case "noembed":
                case "noframes":
                case "style":
                case "xml":
                    tokeniser.transition(TokeniserState.Rawtext);
                    break;
                case "script":
                    tokeniser.transition(TokeniserState.ScriptData);
                    break;
                case "noscript":
                    tokeniser.transition(TokeniserState.Data); // if scripting enabled, rawtext
                    break;
                case "plaintext":
                    tokeniser.transition(TokeniserState.PLAINTEXT);
                    break;
                case "template":
                    tokeniser.transition(TokeniserState.Data);
                    pushTemplateMode(HtmlTreeBuilderState.InTemplate);
                    break;
                default:
                    tokeniser.transition(TokeniserState.Data);
            }
            root = new Element(tagFor(contextTag, settings), baseUri);
            doc.appendChild(root);
            stack.add(root);
            resetInsertionMode();

            // setup form element to nearest form on context (up ancestor chain). ensures form controls are associated
            // with form correctly
            Element formSearch = context;
            while (formSearch != null) {
                if (formSearch instanceof FormElement) {
                    formElement = (FormElement) formSearch;
                    break;
                }
                formSearch = formSearch.parent();
            }
        }

        runParser();
        if (context != null) {
            // depending on context and the input html, content may have been added outside of the root el
            // e.g. context=p, input=div, the div will have been pushed out.
            List<Node> nodes = root.siblingNodes();
            if (!nodes.isEmpty())
                root.insertChildren(-1, nodes);
            return root.childNodes();
        }
        else
            return doc.childNodes();
    }

//@ requires token!= null;
//@ ensures currentToken == token && \result == (token == current_token);
    @Override
    protected boolean process(Token token) {
        currentToken = token;
        return this.state.process(token, this);
    }

//@ requires state!= null;
//@ ensures currentToken == token;
//@ requires state.valid(token, this);
    boolean process(Token token, HtmlTreeBuilderState state) {
        currentToken = token;
        return state.process(token, this);
    }

//@ ensures this.state == state;
    void transition(HtmlTreeBuilderState state) {
        this.state = state;
    }

//@ ensures \result == state;
    HtmlTreeBuilderState state() {
        return state;
    }

//@ ensures originalState == state;
    void markInsertionMode() {
        originalState = state;
    }

//@ ensures \result == originalState;
    HtmlTreeBuilderState originalState() {
        return originalState;
    }

//@ ensures framesetOk == framesetOk;
    void framesetOk(boolean framesetOk) {
        this.framesetOk = framesetOk;
    }

//@ ensures \result == framesetOk;
    boolean framesetOk() {
        return framesetOk;
    }

//@ ensures \result == doc;
    Document getDocument() {
        return doc;
    }

//@ ensures \result == baseUri;
    String getBaseUri() {
        return baseUri;
    }

//@ requires base!= null;
//@ ensures baseUriSetFromDoc == true;
    void maybeSetBaseUri(Element base) {
        if (baseUriSetFromDoc) // only listen to the first <base href> in parse
            return;

        String href = base.absUrl("href");
        if (href.length() != 0) { // ignore <base target> etc
            baseUri = href;
            baseUriSetFromDoc = true;
            doc.setBaseUri(href); // set on the doc so doc.createElement(Tag) will get updated base, and to update all descendants
        }
    }

//@ ensures \result == fragmentParsing;
    boolean isFragmentParsing() {
        return fragmentParsing;
    }

//@ requires state!= null;
    void error(HtmlTreeBuilderState state) {
        if (parser.getErrors().canAddError())
            parser.getErrors().add(new ParseError(reader, "Unexpected %s token [%s] when in state [%s]",
                currentToken.tokenType(), currentToken, state));
    }

//@ requires startTag!= null;
    Element insert(final Token.StartTag startTag) {
        dedupeAttributes(startTag);

        // handle empty unknown tags
        // when the spec expects an empty tag, will directly hit insertEmpty, so won't generate this fake end tag.
        if (startTag.isSelfClosing()) {
            Element el = insertEmpty(startTag);
            stack.add(el);
            tokeniser.transition(TokeniserState.Data); // handles <script />, otherwise needs breakout steps from script data
            tokeniser.emit(emptyEnd.reset().name(el.tagName()));  // ensure we get out of whatever state we are in. emitted for yielded processing
            return el;
        }

        Element el = new Element(tagFor(startTag.name(), settings), null, settings.normalizeAttributes(startTag.attributes));
        insert(el, startTag);
        return el;
    }

//@ requires startTagName!= null;
//@ ensures \result.getText().equals(startTagName);
	Element insertStartTag(String startTagName) {
        Element el = new Element(tagFor(startTagName, settings), null);
        insert(el);
        return el;
    }

//@ requires el!= null;
//@ ensures stack.size() == el.stack.size() + 1;
    void insert(Element el) {
        insertNode(el, null);
        stack.add(el);
    }

//@ requires el!= null;
//@ requires token!= null;
    private void insert(Element el, @Nullable Token token) {
        insertNode(el, token);
        stack.add(el);
    }

//@ requires startTag!= null;
    Element insertEmpty(Token.StartTag startTag) {
        dedupeAttributes(startTag);

        Tag tag = tagFor(startTag.name(), settings);
        Element el = new Element(tag, null, settings.normalizeAttributes(startTag.attributes));
        insertNode(el, startTag);
        if (startTag.isSelfClosing()) {
            if (tag.isKnownTag()) {
                if (!tag.isEmpty())
                    tokeniser.error("Tag [%s] cannot be self closing; not a void tag", tag.normalName());
            }
            else // unknown tag, remember this is self closing for output
                tag.setSelfClosing();
        }
        return el;
    }

//@ requires startTag!= null;
//@ requires onStack!= null;
//@ ensures \result!= null;
    FormElement insertForm(Token.StartTag startTag, boolean onStack, boolean checkTemplateStack) {
        dedupeAttributes(startTag);

        Tag tag = tagFor(startTag.name(), settings);
        FormElement el = new FormElement(tag, null, settings.normalizeAttributes(startTag.attributes));
        if (checkTemplateStack) {
            if(!onStack("template"))
                setFormElement(el);
        } else
            setFormElement(el);

        insertNode(el, startTag);
        if (onStack)
            stack.add(el);
        return el;
    }

//@ requires commentToken!= null;
    void insert(Token.Comment commentToken) {
        Comment comment = new Comment(commentToken.getData());
        insertNode(comment, commentToken);
    }

    /** Inserts the provided character token into the current element. */
//@ requires currentElement()!= null;
    void insert(Token.Character characterToken) {
        final Element el = currentElement(); // will be doc if no current element; allows for whitespace to be inserted into the doc root object (not on the stack)
        insert(characterToken, el);
    }

//@ requires el!= null;
    void insert(Token.Character characterToken, Element el) {
        final Node node;
        final String tagName = el.normalName();
        final String data = characterToken.getData();

        if (characterToken.isCData())
            node = new CDataNode(data);
        else if (isContentForTagData(tagName))
            node = new DataNode(data);
        else
            node = new TextNode(data);
        el.appendChild(node); // doesn't use insertNode, because we don't foster these; and will always have a stack.
        onNodeInserted(node, characterToken);
    }

    /** Inserts the provided character token into the provided element. Use when not going onto stack element */
//@ requires doc!= null;
//@ requires stack.isEmpty() ||!(stack.isEmpty() && token!= null);
//@ ensures currentElement() == null;
//@ ensures doc.appendChild(node);
    private void insertNode(Node node, @Nullable Token token) {
        // if the stack hasn't been set up yet, elements (doctype, comments) go into the doc
        if (stack.isEmpty())
            doc.appendChild(node);
        else if (isFosterInserts() && StringUtil.inSorted(currentElement().normalName(), InTableFoster))
            insertInFosterParent(node);
        else
            currentElement().appendChild(node);

        // connect form controls to their form element
        if (node instanceof Element && ((Element) node).tag().isFormListed()) {
            if (formElement != null)
                formElement.addElement((Element) node);
        }
        onNodeInserted(node, token);
    }

    /** Cleanup duplicate attributes. **/
//@ requires startTag!= null;
    private void dedupeAttributes(StartTag startTag) {
        if (startTag.hasAttributes() && !startTag.attributes.isEmpty()) {
            int dupes = startTag.attributes.deduplicate(settings);
            if (dupes > 0) {
                error("Dropped duplicate attribute(s) in tag [%s]", startTag.normalName);
            }
        }
    }

//@ ensures \result!= null;
    Element pop() {
        int size = stack.size();
        return stack.remove(size-1);
    }

//@ ensures stack.size() == 0;
//@ ensures stack.contains(element);
    void push(Element element) {
        stack.add(element);
    }

//@ ensures \result!= null;
//@ ensures stack.size() == \old(stack.size()) + 1;
    ArrayList<Element> getStack() {
        return stack;
    }

//@ requires el!= null;
    boolean onStack(Element el) {
        return onStack(stack, el);
    }

//@ ensures \result == (elName!= null);
    boolean onStack(String elName) {
        return getFromStack(elName) != null;
    }

    private static final int maxQueueDepth = 256; // an arbitrary tension point between real HTML and crafted pain
//@ requires queue.size() > 0;
    private static boolean onStack(ArrayList<Element> queue, Element element) {
        final int bottom = queue.size() - 1;
        final int upper = bottom >= maxQueueDepth ? bottom - maxQueueDepth : 0;
        for (int pos = bottom; pos >= upper; pos--) {
            Element next = queue.get(pos);
            if (next == element) {
                return true;
            }
        }
        return false;
    }

//@ requires elName!= null;
//@ requires stack.size() > 0;
    @Nullable
    Element getFromStack(String elName) {
        final int bottom = stack.size() - 1;
        final int upper = bottom >= maxQueueDepth ? bottom - maxQueueDepth : 0;
        for (int pos = bottom; pos >= upper; pos--) {
            Element next = stack.get(pos);
            if (next.normalName().equals(elName)) {
                return next;
            }
        }
        return null;
    }

//@ requires el!= null;
    boolean removeFromStack(Element el) {
        for (int pos = stack.size() -1; pos >= 0; pos--) {
            Element next = stack.get(pos);
            if (next == el) {
                stack.remove(pos);
                return true;
            }
        }
        return false;
    }

//@ requires elName!= null;
//@ requires stack.size() > 0;
    @Nullable
    Element popStackToClose(String elName) {
        for (int pos = stack.size() -1; pos >= 0; pos--) {
            Element el = stack.get(pos);
            stack.remove(pos);
            if (el.normalName().equals(elName)) {
                if (currentToken instanceof Token.EndTag)
                    onNodeClosed(el, currentToken);
                return el;
            }
        }
        return null;
    }

    // elnames is sorted, comes from Constants
//@ requires elNames!= null;
    void popStackToClose(String... elNames) {
        for (int pos = stack.size() -1; pos >= 0; pos--) {
            Element next = stack.get(pos);
            stack.remove(pos);
            if (inSorted(next.normalName(), elNames))
                break;
        }
    }

//@ requires elName!= null;
    void popStackToBefore(String elName) {
        for (int pos = stack.size() -1; pos >= 0; pos--) {
            Element next = stack.get(pos);
            if (next.normalName().equals(elName)) {
                break;
            } else {
                stack.remove(pos);
            }
        }
    }

//@ requires isTableOpen(this.table) && isTemplateOpen(this.template);
//@ ensures true;
    void clearStackToTableContext() {
        clearStackToContext("table", "template");
    }

//@ requires isOpen;
//@ ensures isOpen;
    void clearStackToTableBodyContext() {
        clearStackToContext("tbody", "tfoot", "thead", "template");
    }

//@ requires isOpen;
//@ ensures isOpen;
    void clearStackToTableRowContext() {
        clearStackToContext("tr", "template");
    }

//@ requires nodeNames!= null;
    private void clearStackToContext(String... nodeNames) {
        for (int pos = stack.size() -1; pos >= 0; pos--) {
            Element next = stack.get(pos);
            if (StringUtil.in(next.normalName(), nodeNames) || next.normalName().equals("html"))
                break;
            else
                stack.remove(pos);
        }
    }

//@ requires el!= null;
    @Nullable Element aboveOnStack(Element el) {
        assert onStack(el);
        for (int pos = stack.size() -1; pos >= 0; pos--) {
            Element next = stack.get(pos);
            if (next == el) {
                return stack.get(pos-1);
            }
        }
        return null;
    }

//@ requires after!= null;
//@ requires in!= null;
    void insertOnStackAfter(Element after, Element in) {
        int i = stack.lastIndexOf(after);
        Validate.isTrue(i != -1);
        stack.add(i+1, in);
    }

//@ requires out!= null && in!= null;
//@ ensures queue.contains(out) && queue.contains(in);
    void replaceOnStack(Element out, Element in) {
        replaceInQueue(stack, out, in);
    }

//@ requires queue.size() > 0;
//@ requires out!= null;
//@ requires in!= null;
    private void replaceInQueue(ArrayList<Element> queue, Element out, Element in) {
        int i = queue.lastIndexOf(out);
        Validate.isTrue(i != -1);
        queue.set(i, in);
    }

    /**
     * Reset the insertion mode, by searching up the stack for an appropriate insertion mode. The stack search depth
     * is limited to {@link #maxQueueDepth}.
     * @return true if the insertion mode was actually changed.
     */
//@ ensures \result == state;
    boolean resetInsertionMode() {
        // https://html.spec.whatwg.org/multipage/parsing.html#the-insertion-mode
        boolean last = false;
        final int bottom = stack.size() - 1;
        final int upper = bottom >= maxQueueDepth ? bottom - maxQueueDepth : 0;
        final HtmlTreeBuilderState origState = this.state;

        if (stack.size() == 0) { // nothing left of stack, just get to body
            transition(HtmlTreeBuilderState.InBody);
        }

        LOOP: for (int pos = bottom; pos >= upper; pos--) {
            Element node = stack.get(pos);
            if (pos == upper) {
                last = true;
                if (fragmentParsing)
                    node = contextElement;
            }
            String name = node != null ? node.normalName() : "";
            switch (name) {
                case "select":
                    transition(HtmlTreeBuilderState.InSelect);
                    // todo - should loop up (with some limit) and check for table or template hits
                    break LOOP;
                case "td":
                case "th":
                    if (!last) {
                        transition(HtmlTreeBuilderState.InCell);
                        break LOOP;
                    }
                    break;
                case "tr":
                    transition(HtmlTreeBuilderState.InRow);
                    break LOOP;
                case "tbody":
                case "thead":
                case "tfoot":
                    transition(HtmlTreeBuilderState.InTableBody);
                    break LOOP;
                case "caption":
                    transition(HtmlTreeBuilderState.InCaption);
                    break LOOP;
                case "colgroup":
                    transition(HtmlTreeBuilderState.InColumnGroup);
                    break LOOP;
                case "table":
                    transition(HtmlTreeBuilderState.InTable);
                    break LOOP;
                case "template":
                    HtmlTreeBuilderState tmplState = currentTemplateMode();
                    Validate.notNull(tmplState, "Bug: no template insertion mode on stack!");
                    transition(tmplState);
                    break LOOP;
                case "head":
                    if (!last) {
                        transition(HtmlTreeBuilderState.InHead);
                        break LOOP;
                    }
                    break;
                case "body":
                    transition(HtmlTreeBuilderState.InBody);
                    break LOOP;
                case "frameset":
                    transition(HtmlTreeBuilderState.InFrameset);
                    break LOOP;
                case "html":
                    transition(headElement == null ? HtmlTreeBuilderState.BeforeHead : HtmlTreeBuilderState.AfterHead);
                    break LOOP;
            }
            if (last) {
                transition(HtmlTreeBuilderState.InBody);
                break;
            }
        }
        return state != origState;
    }

    /** Places the body back onto the stack and moves to InBody, for cases in AfterBody / AfterAfterBody when more content comes */
//@ requires doc!= null;
    void resetBody() {
        if (!onStack("body")) {
            stack.add(doc.body());
        }
        transition(HtmlTreeBuilderState.InBody);
    }

    // todo: tidy up in specific scope methods
    private String[] specificScopeTarget = {null};

//@ requires targetName!= null;
//@ requires (\forall String typeName; typeName!= null; typeName!= extraTypes);
//@ ensures \result == inSpecificScope(specificScopeTarget, baseTypes, extraTypes);
    private boolean inSpecificScope(String targetName, String[] baseTypes, String[] extraTypes) {
        specificScopeTarget[0] = targetName;
        return inSpecificScope(specificScopeTarget, baseTypes, extraTypes);
    }

//@ requires targetNames!= null && \nonnullelements(targetNames);
//@ requires baseTypes!= null && \nonnullelements(baseTypes);
//@ requires extraTypes!= null && \nonnullelements(extraTypes);
    private boolean inSpecificScope(String[] targetNames, String[] baseTypes, @Nullable String[] extraTypes) {
        // https://html.spec.whatwg.org/multipage/parsing.html#has-an-element-in-the-specific-scope
        final int bottom = stack.size() -1;
        final int top = bottom > MaxScopeSearchDepth ? bottom - MaxScopeSearchDepth : 0;
        // don't walk too far up the tree

        for (int pos = bottom; pos >= top; pos--) {
            final String elName = stack.get(pos).normalName();
            if (inSorted(elName, targetNames))
                return true;
            if (inSorted(elName, baseTypes))
                return false;
            if (extraTypes != null && inSorted(elName, extraTypes))
                return false;
        }
        //Validate.fail("Should not be reachable"); // would end up false because hitting 'html' at root (basetypes)
        return false;
    }

//@ requires targetNames!= null;
    boolean inScope(String[] targetNames) {
        return inSpecificScope(targetNames, TagsSearchInScope, null);
    }

//@ ensures \result == inScope(targetName, null);
    boolean inScope(String targetName) {
        return inScope(targetName, null);
    }

//@ requires extras!= null && \nonnullelements(extras);
    boolean inScope(String targetName, String[] extras) {
        return inSpecificScope(targetName, TagsSearchInScope, extras);
        // todo: in mathml namespace: mi, mo, mn, ms, mtext annotation-xml
        // todo: in svg namespace: forignOjbect, desc, title
    }

//@ requires targetName!= null;
//@ requires inScope(targetName, TagSearchList);
    boolean inListItemScope(String targetName) {
        return inScope(targetName, TagSearchList);
    }

//@ ensures \result == inScope(targetName, TagSearchButton);
    boolean inButtonScope(String targetName) {
        return inScope(targetName, TagSearchButton);
    }

//@ ensures \result == inSpecificScope(targetName, TagSearchTableScope, null);
    boolean inTableScope(String targetName) {
        return inSpecificScope(targetName, TagSearchTableScope, null);
    }

//@ requires targetName!= null;
//@ ensures \result == inSorted(targetName, TagSearchSelectScope);
    boolean inSelectScope(String targetName) {
        for (int pos = stack.size() -1; pos >= 0; pos--) {
            Element el = stack.get(pos);
            String elName = el.normalName();
            if (elName.equals(targetName))
                return true;
            if (!inSorted(elName, TagSearchSelectScope)) // all elements except
                return false;
        }
        Validate.fail("Should not be reachable");
        return false;
    }

    /** Tests if there is some element on the stack that is not in the provided set. */
//@ ensures \result == (stack.size() > 0);
    boolean onStackNot(String[] allowedTags) {
        final int bottom = stack.size() -1;
        final int top = bottom > MaxScopeSearchDepth ? bottom - MaxScopeSearchDepth : 0;
        // don't walk too far up the tree

        for (int pos = bottom; pos >= top; pos--) {
            final String elName = stack.get(pos).normalName();
            if (!inSorted(elName, allowedTags))
                return true;
        }
        return false;
    }

//@ ensures headElement == null;
//@ ensures this.headElement == headElement;
    void setHeadElement(Element headElement) {
        this.headElement = headElement;
    }

//@ ensures \result == headElement;
    Element getHeadElement() {
        return headElement;
    }

//@ ensures \result == fosterInserts;
    boolean isFosterInserts() {
        return fosterInserts;
    }

//@ ensures fosterInserts == true;
    void setFosterInserts(boolean fosterInserts) {
        this.fosterInserts = fosterInserts;
    }

//@ ensures \result == formElement;
    @Nullable FormElement getFormElement() {
        return formElement;
    }

//@ ensures this.formElement == formElement;
    void setFormElement(FormElement formElement) {
        this.formElement = formElement;
    }

//@ ensures pendingTableCharacters == null;
//@ ensures pendingTableCharacters == new ArrayList<>();
    void resetPendingTableCharacters() {
        pendingTableCharacters = new ArrayList<>();
    }

//@ ensures \result == pendingTableCharacters;
    List<Token.Character> getPendingTableCharacters() {
        return pendingTableCharacters;
    }

//@ requires state!= null;
//@ ensures state == pendingTableCharacters;
    void addPendingTableCharacters(Token.Character c) {
        // make a clone of the token to maintain its state (as Tokens are otherwise reset)
        Token.Character clone = c.clone();
        pendingTableCharacters.add(clone);
    }

    /**
     13.2.6.3 Closing elements that have implied end tags
     When the steps below require the UA to generate implied end tags, then, while the current node is a dd element, a dt element, an li element, an optgroup element, an option element, a p element, an rb element, an rp element, an rt element, or an rtc element, the UA must pop the current node off the stack of open elements.

     If a step requires the UA to generate implied end tags but lists an element to exclude from the process, then the UA must perform the above steps as if that element was not in the above list.

     When the steps below require the UA to generate all implied end tags thoroughly, then, while the current node is a caption element, a colgroup element, a dd element, a dt element, an li element, an optgroup element, an option element, a p element, an rb element, an rp element, an rt element, an rtc element, a tbody element, a td element, a tfoot element, a th element, a thead element, or a tr element, the UA must pop the current node off the stack of open elements.

     @param excludeTag If a step requires the UA to generate implied end tags but lists an element to exclude from the
     process, then the UA must perform the above steps as if that element was not in the above list.
     */
//@ requires excludeTag!= null;
    void generateImpliedEndTags(String excludeTag) {
        while (inSorted(currentElement().normalName(), TagSearchEndTags)) {
            if (excludeTag != null && currentElementIs(excludeTag))
                break;
            pop();
        }
    }

//@ requires isImpliedEndTags(false);
    void generateImpliedEndTags() {
        generateImpliedEndTags(false);
    }

    /**
     Pops elements off the stack according to the implied end tag rules
     @param thorough if we are thorough (includes table elements etc) or not
     */
//@ requires thorough!= null;
    void generateImpliedEndTags(boolean thorough) {
        final String[] search = thorough ? TagThoroughSearchEndTags : TagSearchEndTags;
        while (inSorted(currentElement().normalName(), search)) {
            pop();
        }
    }

//@ requires isOpen;
//@ ensures!isOpen;
    void closeElement(String name) {
        generateImpliedEndTags(name);
        if (!name.equals(currentElement().normalName())) error(state());
        popStackToClose(name);
    }

//@ requires el!= null;
    boolean isSpecial(Element el) {
        // todo: mathml's mi, mo, mn
        // todo: svg's foreigObject, desc, title
        String name = el.normalName();
        return inSorted(name, TagSearchSpecial);
    }

//@ requires formattingElements.size() > 0;
    Element lastFormattingElement() {
        return formattingElements.size() > 0 ? formattingElements.get(formattingElements.size()-1) : null;
    }

//@ requires el!= null;
//@ ensures \result!= -1 ==> formattingElements.size() == \old(formattingElements.size()) + 1;
//@ ensures \result == -1 ==> formattingElements.size() == \old(formattingElements.size()) + 1;
    int positionOfElement(Element el){
        for (int i = 0; i < formattingElements.size(); i++){
            if (el == formattingElements.get(i))
                return i;
        }
        return -1;
    }

//@ requires formattingElements.size() > 0;
    Element removeLastFormattingElement() {
        int size = formattingElements.size();
        if (size > 0)
            return formattingElements.remove(size-1);
        else
            return null;
    }

    // active formatting elements
//@ requires in!= null;
//@ ensures formattingElements.contains(in);
    void pushActiveFormattingElements(Element in) {
        checkActiveFormattingElements(in);
        formattingElements.add(in);
    }

//@ requires in!= null;
//@ requires bookmark >= 0;
    void pushWithBookmark(Element in, int bookmark){
        checkActiveFormattingElements(in);
        // catch any range errors and assume bookmark is incorrect - saves a redundant range check.
        try {
            formattingElements.add(bookmark, in);
        } catch (IndexOutOfBoundsException e) {
            formattingElements.add(in);
        }
    }

//@ requires in!= null;
    void checkActiveFormattingElements(Element in){
        int numSeen = 0;
        final int size = formattingElements.size() -1;
        int ceil = size - maxUsedFormattingElements; if (ceil <0) ceil = 0;

        for (int pos = size; pos >= ceil; pos--) {
            Element el = formattingElements.get(pos);
            if (el == null) // marker
                break;

            if (isSameFormattingElement(in, el))
                numSeen++;

            if (numSeen == 3) {
                formattingElements.remove(pos);
                break;
            }
        }
    }

//@ requires a.namespace() == b.namespace();
//@ requires a.normalName() == b.normalName();
//@ requires a.tag() == b.tag();
    private boolean isSameFormattingElement(Element a, Element b) {
        // same if: same namespace, tag, and attributes. Element.equals only checks tag, might in future check children
        return a.normalName().equals(b.normalName()) &&
                // a.namespace().equals(b.namespace()) &&
                a.attributes().equals(b.attributes());
        // todo: namespaces
    }

//@ requires maxQueueDepth > 0;
    void reconstructFormattingElements() {
        if (stack.size() > maxQueueDepth)
            return;
        Element last = lastFormattingElement();
        if (last == null || onStack(last))
            return;

        Element entry = last;
        int size = formattingElements.size();
        int ceil = size - maxUsedFormattingElements; if (ceil <0) ceil = 0;
        int pos = size - 1;
        boolean skip = false;
        while (true) {
            if (pos == ceil) { // step 4. if none before, skip to 8
                skip = true;
                break;
            }
            entry = formattingElements.get(--pos); // step 5. one earlier than entry
            if (entry == null || onStack(entry)) // step 6 - neither marker nor on stack
                break; // jump to 8, else continue back to 4
        }
        while(true) {
            if (!skip) // step 7: on later than entry
                entry = formattingElements.get(++pos);
            Validate.notNull(entry); // should not occur, as we break at last element

            // 8. create new element from element, 9 insert into current node, onto stack
            skip = false; // can only skip increment from 4.
            Element newEl = new Element(tagFor(entry.normalName(), settings), null, entry.attributes().clone());
            insert(newEl);

            // 10. replace entry with new entry
            formattingElements.set(pos, newEl);

            // 11
            if (pos == size-1) // if not last entry in list, jump to 7
                break;
        }
    }
    private static final int maxUsedFormattingElements = 12; // limit how many elements get recreated

//@ requires!formattingElements.isEmpty();
    void clearFormattingElementsToLastMarker() {
        while (!formattingElements.isEmpty()) {
            Element el = removeLastFormattingElement();
            if (el == null)
                break;
        }
    }

//@ requires el!= null;
    void removeFromActiveFormattingElements(Element el) {
        for (int pos = formattingElements.size() -1; pos >= 0; pos--) {
            Element next = formattingElements.get(pos);
            if (next == el) {
                formattingElements.remove(pos);
                break;
            }
        }
    }

//@ requires openStack(formattingElements, el);
    boolean isInActiveFormattingElements(Element el) {
        return onStack(formattingElements, el);
    }

//@ requires nodeName!= null;
//@ ensures \result!= null;
    @Nullable
    Element getActiveFormattingElement(String nodeName) {
        for (int pos = formattingElements.size() -1; pos >= 0; pos--) {
            Element next = formattingElements.get(pos);
            if (next == null) // scope marker
                break;
            else if (next.normalName().equals(nodeName))
                return next;
        }
        return null;
    }

//@ requires out!= null && in!= null;
//@ requires formattingElements!= null;
    void replaceActiveFormattingElement(Element out, Element in) {
        replaceInQueue(formattingElements, out, in);
    }

//@ requires formattingElements.size() > 0;
    void insertMarkerToFormattingElements() {
        formattingElements.add(null);
    }

//@ requires in!= null;
//@ requires stack.size() > 0;
    void insertInFosterParent(Node in) {
        Element fosterParent;
        Element lastTable = getFromStack("table");
        boolean isLastTableParent = false;
        if (lastTable != null) {
            if (lastTable.parent() != null) {
                fosterParent = lastTable.parent();
                isLastTableParent = true;
            } else
                fosterParent = aboveOnStack(lastTable);
        } else { // no table == frag
            fosterParent = stack.get(0);
        }

        if (isLastTableParent) {
            Validate.notNull(lastTable); // last table cannot be null by this point.
            lastTable.before(in);
        }
        else
            fosterParent.appendChild(in);
    }

    // Template Insertion Mode stack
//@ ensures tmplInsertMode.contains(state);
    void pushTemplateMode(HtmlTreeBuilderState state) {
        tmplInsertMode.add(state);
    }

//@ ensures \result == tmplInsertMode.remove(tmplInsertMode.size() -1);
    @Nullable HtmlTreeBuilderState popTemplateMode() {
        if (tmplInsertMode.size() > 0) {
            return tmplInsertMode.remove(tmplInsertMode.size() -1);
        } else {
            return null;
        }
    }

//@ ensures \result == tmplInsertMode.size();
    int templateModeSize() {
        return tmplInsertMode.size();
    }

//@ requires tmplInsertMode.size() > 0;
    @Nullable HtmlTreeBuilderState currentTemplateMode() {
        return (tmplInsertMode.size() > 0) ? tmplInsertMode.get(tmplInsertMode.size() -1)  : null;
    }

//@ requires currentToken!= null;
//@ requires state!= null;
//@ ensures this.currentToken == currentToken;
//@ ensures state == state;
//@ ensures currentElement == null;
    @Override
    public String toString() {
        return "TreeBuilder{" +
                "currentToken=" + currentToken +
                ", state=" + state +
                ", currentElement=" + currentElement() +
                '}';
    }

//@ ensures \result == (normalName.equals("script") || normalName.equals("style"));
    protected boolean isContentForTagData(final String normalName) {
        return (normalName.equals("script") || normalName.equals("style"));
    }
}
