package org.jsoup.parser;

import org.jsoup.helper.Validate;
import org.jsoup.internal.StringUtil;
import org.jsoup.nodes.Entities;

import javax.annotation.Nullable;
import java.util.Arrays;

/**
 * Readers the input stream into tokens.
 */
final class Tokeniser {
    static final char replacementChar = '\uFFFD'; // replaces null character
    private static final char[] notCharRefCharsSorted = new char[]{'\t', '\n', '\r', '\f', ' ', '<', '&'};

    // Some illegal character escapes are parsed by browsers as windows-1252 instead. See issue #1034
    // https://html.spec.whatwg.org/multipage/parsing.html#numeric-character-reference-end-state
    static final int win1252ExtensionsStart = 0x80;
    static final int[] win1252Extensions = new int[] {
            // we could build this manually, but Windows-1252 is not a standard java charset so that could break on
            // some platforms - this table is verified with a test
            0x20AC, 0x0081, 0x201A, 0x0192, 0x201E, 0x2026, 0x2020, 0x2021,
            0x02C6, 0x2030, 0x0160, 0x2039, 0x0152, 0x008D, 0x017D, 0x008F,
            0x0090, 0x2018, 0x2019, 0x201C, 0x201D, 0x2022, 0x2013, 0x2014,
            0x02DC, 0x2122, 0x0161, 0x203A, 0x0153, 0x009D, 0x017E, 0x0178,
    };

    static {
        Arrays.sort(notCharRefCharsSorted);
    }

    private final CharacterReader reader; // html input
    private final ParseErrorList errors; // errors found while tokenising

    private TokeniserState state = TokeniserState.Data; // current tokenisation state
    @Nullable private Token emitPending = null; // the token we are about to emit on next read
    private boolean isEmitPending = false;
    @Nullable private String charsString = null; // characters pending an emit. Will fall to charsBuilder if more than one
    private final StringBuilder charsBuilder = new StringBuilder(1024); // buffers characters to output as one token, if more than one emit per read
    StringBuilder dataBuffer = new StringBuilder(1024); // buffers data looking for </script>

    Token.StartTag startPending = new Token.StartTag();
    Token.EndTag endPending = new Token.EndTag();
    Token.Tag tagPending = startPending; // tag we are building up: start or end pending
    Token.Character charPending = new Token.Character();
    Token.Doctype doctypePending = new Token.Doctype(); // doctype building up
    Token.Comment commentPending = new Token.Comment(); // comment building up
    @Nullable private String lastStartTag; // the last start tag emitted, to test appropriate end tag
    @Nullable private String lastStartCloseSeq; // "</" + lastStartTag, so we can quickly check for that in RCData

    private static final int Unset = -1;
    private int markupStartPos, charStartPos = Unset; // reader pos at the start of markup / characters. updated on state transition

    Tokeniser(CharacterReader reader, ParseErrorList errors) {
        this.reader = reader;
        this.errors = errors;
    }

//@ requires state!= null;
//@ requires reader!= null;
    Token read() {
        while (!isEmitPending) {
            state.read(this, reader);
        }

        // if emit is pending, a non-character token was found: return any chars in buffer, and leave token for next read:
        final StringBuilder cb = this.charsBuilder;
        if (cb.length() != 0) {
            String str = cb.toString();
            cb.delete(0, cb.length());
            Token token = charPending.data(str);
            charsString = null;
            return token;
        } else if (charsString != null) {
            Token token = charPending.data(charsString);
            charsString = null;
            return token;
        } else {
            isEmitPending = false;
            assert emitPending != null;
            return emitPending;
        }
    }

//@ requires token!= null;
//@ ensures isEmitPending == \old(isEmitPending) && token.startPos() == markupStartPos;
//@ ensures token.endPos() == \old(reader.pos());
    void emit(Token token) {
        Validate.isFalse(isEmitPending);

        emitPending = token;
        isEmitPending = true;
        token.startPos(markupStartPos);
        token.endPos(reader.pos());
        charStartPos = Unset;

        if (token.type == Token.TokenType.StartTag) {
            Token.StartTag startTag = (Token.StartTag) token;
            lastStartTag = startTag.tagName;
            lastStartCloseSeq = null; // only lazy inits
        } else if (token.type == Token.TokenType.EndTag) {
            Token.EndTag endTag = (Token.EndTag) token;
            if (endTag.hasAttributes())
                error("Attributes incorrectly present on end tag [/%s]", endTag.normalName());
        }
    }

//@ ensures isEmitPending == \old(isEmitPending) && \old(reader.pos()) == 0;
    void emit(final String str) {
        // buffer strings up until last string token found, to emit only one token for a run of character refs etc.
        // does not set isEmitPending; read checks that
        if (charsString == null) {
            charsString = str;
        } else {
            if (charsBuilder.length() == 0) { // switching to string builder as more than one emit before read
                charsBuilder.append(charsString);
            }
            charsBuilder.append(str);
        }
        charPending.startPos(charStartPos);
        charPending.endPos(reader.pos());
    }

    // variations to limit need to create temp strings
//@ ensures charsString!= null ==> str.toString().equals(charsString);
//@ ensures charStartPos == 0 ==> charPending.startPos(reader.pos());
//@ ensures charPending.endPos(reader.pos());
    void emit(final StringBuilder str) {
        if (charsString == null) {
            charsString = str.toString();
        } else {
            if (charsBuilder.length() == 0) {
                charsBuilder.append(charsString);
            }
            charsBuilder.append(str);
        }
        charPending.startPos(charStartPos);
        charPending.endPos(reader.pos());
    }

//@ requires reader!= null;
    void emit(char c) {
        if (charsString == null) {
            charsString = String.valueOf(c);
        } else {
            if (charsBuilder.length() == 0) {
                charsBuilder.append(charsString);
            }
            charsBuilder.append(c);
        }
        charPending.startPos(charStartPos);
        charPending.endPos(reader.pos());
    }

//@ requires chars!= null;
//@ ensures \result!= null;
    void emit(char[] chars) {
        emit(String.valueOf(chars));
    }

//@ requires codepoints!= null && codepoints.length > 0;
    void emit(int[] codepoints) {
        emit(new String(codepoints, 0, codepoints.length));
    }

//@ ensures \result == state;
    TokeniserState getState() {
        return state;
    }

//@ requires newState!= null;
//@ ensures this.state == newState;
    void transition(TokeniserState newState) {
        // track markup / data position on state transitions
        switch (newState) {
            case TagOpen:
                markupStartPos = reader.pos();
                break;
            case Data:
                if (charStartPos == Unset) // don't reset when we are jumping between e.g data -> char ref -> data
                    charStartPos = reader.pos();
        }

        this.state = newState;
    }

//@ requires newState!= null;
//@ ensures reader.state() == newState;
    void advanceTransition(TokeniserState newState) {
        transition(newState);
        reader.advance();
    }

    final private int[] codepointHolder = new int[1]; // holder to not have to keep creating arrays
    final private int[] multipointHolder = new int[2];
//@ requires reader!= null;
    @Nullable int[] consumeCharacterReference(@Nullable Character additionalAllowedCharacter, boolean inAttribute) {
        if (reader.isEmpty())
            return null;
        if (additionalAllowedCharacter != null && additionalAllowedCharacter == reader.current())
            return null;
        if (reader.matchesAnySorted(notCharRefCharsSorted))
            return null;

        final int[] codeRef = codepointHolder;
        reader.mark();
        if (reader.matchConsume("#")) { // numbered
            boolean isHexMode = reader.matchConsumeIgnoreCase("X");
            String numRef = isHexMode ? reader.consumeHexSequence() : reader.consumeDigitSequence();
            if (numRef.length() == 0) { // didn't match anything
                characterReferenceError("numeric reference with no numerals");
                reader.rewindToMark();
                return null;
            }

            reader.unmark();
            if (!reader.matchConsume(";"))
                characterReferenceError("missing semicolon on [&#%s]", numRef); // missing semi
            int charval = -1;
            try {
                int base = isHexMode ? 16 : 10;
                charval = Integer.valueOf(numRef, base);
            } catch (NumberFormatException ignored) {
            } // skip
            if (charval == -1 || (charval >= 0xD800 && charval <= 0xDFFF) || charval > 0x10FFFF) {
                characterReferenceError("character [%s] outside of valid range", charval);
                codeRef[0] = replacementChar;
            } else {
                // fix illegal unicode characters to match browser behavior
                if (charval >= win1252ExtensionsStart && charval < win1252ExtensionsStart + win1252Extensions.length) {
                    characterReferenceError("character [%s] is not a valid unicode code point", charval);
                    charval = win1252Extensions[charval - win1252ExtensionsStart];
                }

                // todo: implement number replacement table
                // todo: check for extra illegal unicode points as parse errors
                codeRef[0] = charval;
            }
            return codeRef;
        } else { // named
            // get as many letters as possible, and look for matching entities.
            String nameRef = reader.consumeLetterThenDigitSequence();
            boolean looksLegit = reader.matches(';');
            // found if a base named entity without a ;, or an extended entity with the ;.
            boolean found = (Entities.isBaseNamedEntity(nameRef) || (Entities.isNamedEntity(nameRef) && looksLegit));

            if (!found) {
                reader.rewindToMark();
                if (looksLegit) // named with semicolon
                    characterReferenceError("invalid named reference [%s]", nameRef);
                return null;
            }
            if (inAttribute && (reader.matchesLetter() || reader.matchesDigit() || reader.matchesAny('=', '-', '_'))) {
                // don't want that to match
                reader.rewindToMark();
                return null;
            }

            reader.unmark();
            if (!reader.matchConsume(";"))
                characterReferenceError("missing semicolon on [&%s]", nameRef); // missing semi
            int numChars = Entities.codepointsForName(nameRef, multipointHolder);
            if (numChars == 1) {
                codeRef[0] = multipointHolder[0];
                return codeRef;
            } else if (numChars ==2) {
                return multipointHolder;
            } else {
                Validate.fail("Unexpected characters returned for " + nameRef);
                return multipointHolder;
            }
        }
    }

//@ ensures \result!= null;
//@ ensures startPending.value() == \old(startPending.value()) && endPending.value() == \old(endPending.value());
    Token.Tag createTagPending(boolean start) {
        tagPending = start ? startPending.reset() : endPending.reset();
        return tagPending;
    }

//@ requires tagPending!= null;
    void emitTagPending() {
        tagPending.finaliseTag();
        emit(tagPending);
    }

//@ ensures commentPending.valid();
    void createCommentPending() {
        commentPending.reset();
    }

//@ requires commentPending!= null;
    void emitCommentPending() {
        emit(commentPending);
    }

//@ ensures commentPending.bogus == true;
    void createBogusCommentPending() {
        commentPending.reset();
        commentPending.bogus = true;
    }

//@ ensures \new_elems_fresh(doctypePending);
    void createDoctypePending() {
        doctypePending.reset();
    }

//@ requires!doctypePending.isEmpty();
    void emitDoctypePending() {
        emit(doctypePending);
    }

//@ requires dataBuffer!= null;
    void createTempBuffer() {
        Token.reset(dataBuffer);
    }

//@ requires lastStartTag!= null;
    boolean isAppropriateEndTagToken() {
        return lastStartTag != null && tagPending.name().equalsIgnoreCase(lastStartTag);
    }

//@ ensures \result == lastStartTag;
    @Nullable String appropriateEndTagName() {
        return lastStartTag; // could be null
    }

    /** Returns the closer sequence {@code </lastStart} */
//@ requires lastStartTag!= null;
    String appropriateEndTagSeq() {
        if (lastStartCloseSeq == null) // reset on start tag emit
            lastStartCloseSeq = "</" + lastStartTag;
        return lastStartCloseSeq;
    }

//@ requires state!= null;
    void error(TokeniserState state) {
        if (errors.canAddError())
            errors.add(new ParseError(reader, "Unexpected character '%s' in input state [%s]", reader.current(), state));
    }

//@ requires state.token().equals(EOF);
    void eofError(TokeniserState state) {
        if (errors.canAddError())
            errors.add(new ParseError(reader, "Unexpectedly reached end of file (EOF) in input state [%s]", state));
    }

//@ requires message!= null;
//@ requires args!= null && \nonnullelements(args);
    private void characterReferenceError(String message, Object... args) {
        if (errors.canAddError())
            errors.add(new ParseError(reader, String.format("Invalid character reference: " + message, args)));
    }

//@ requires errorMsg!= null;
    void error(String errorMsg) {
        if (errors.canAddError())
            errors.add(new ParseError(reader, errorMsg));
    }

//@ requires args!= null && \nonnullelements(args);
    void error(String errorMsg, Object... args) {
        if (errors.canAddError())
            errors.add(new ParseError(reader, errorMsg, args));
    }

//@ ensures \result == (currentNode()!= null);
    boolean currentNodeInHtmlNS() {
        // todo: implement namespaces correctly
        return true;
        // Element currentNode = currentNode();
        // return currentNode != null && currentNode.namespace().equals("HTML");
    }

    /**
     * Utility method to consume reader and unescape entities found within.
     * @param inAttribute if the text to be unescaped is in an attribute
     * @return unescaped string from reader
     */
//@ requires reader!= null;
    String unescapeEntities(boolean inAttribute) {
        StringBuilder builder = StringUtil.borrowBuilder();
        while (!reader.isEmpty()) {
            builder.append(reader.consumeTo('&'));
            if (reader.matches('&')) {
                reader.consume();
                int[] c = consumeCharacterReference(null, inAttribute);
                if (c == null || c.length==0)
                    builder.append('&');
                else {
                    builder.appendCodePoint(c[0]);
                    if (c.length == 2)
                        builder.appendCodePoint(c[1]);
                }

            }
        }
        return StringUtil.releaseBuilder(builder);
    }
}
