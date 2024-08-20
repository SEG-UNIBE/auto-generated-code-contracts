package org.jsoup.parser;

import org.jsoup.helper.Validate;
import org.jsoup.nodes.Attributes;

import javax.annotation.Nullable;

/**
 * Parse tokens for the Tokeniser.
 */
abstract class Token {
    TokenType type;
    static final int Unset = -1;
    private int startPos, endPos = Unset; // position in CharacterReader this token was read from

    private Token() {
    }
    
//@ ensures \result!= null;
    String tokenType() {
        return this.getClass().getSimpleName();
    }

    /**
     * Reset the data represent by this token, for reuse. Prevents the need to create transfer objects for every
     * piece of data, which immediately get GCed.
     */
//@ ensures startPos == Unset;
//@ ensures endPos == Unset;
//@ ensures \result == this;
    Token reset() {
        startPos = Unset;
        endPos = Unset;
        return this;
    }

//@ ensures \result == startPos;
    int startPos() {
        return startPos;
    }

//@ requires pos >= 0;
//@ ensures startPos == pos;
    void startPos(int pos) {
        startPos = pos;
    }

//@ ensures \result == endPos;
    int endPos() {
        return endPos;
    }

//@ ensures endPos == pos;
//@ ensures endPos == pos;
    void endPos(int pos) {
        endPos = pos;
    }

//@ ensures sb!= null;
    static void reset(StringBuilder sb) {
        if (sb != null) {
            sb.delete(0, sb.length());
        }
    }

    static final class Doctype extends Token {
        final StringBuilder name = new StringBuilder();
        String pubSysKey = null;
        final StringBuilder publicIdentifier = new StringBuilder();
        final StringBuilder systemIdentifier = new StringBuilder();
        boolean forceQuirks = false;

        Doctype() {
            type = TokenType.Doctype;
        }

//@ requires name!= null;
//@ requires pubSysKey!= null;
//@ requires publicIdentifier!= null;
//@ requires systemIdentifier!= null;
        @Override
        Token reset() {
            super.reset();
            reset(name);
            pubSysKey = null;
            reset(publicIdentifier);
            reset(systemIdentifier);
            forceQuirks = false;
            return this;
        }

//@ ensures \result!= null;
        String getName() {
            return name.toString();
        }

//@ ensures \result == pubSysKey;
        String getPubSysKey() {
            return pubSysKey;
        }

//@ ensures \result!= null;
        String getPublicIdentifier() {
            return publicIdentifier.toString();
        }

//@ ensures \result!= null;
        public String getSystemIdentifier() {
            return systemIdentifier.toString();
        }

//@ ensures forceQuirks == true;
        public boolean isForceQuirks() {
            return forceQuirks;
        }

//@ ensures \result!= null;
        @Override
        public String toString() {
            return "<!doctype " + getName() + ">";
        }
    }

    static abstract class Tag extends Token {
        @Nullable protected String tagName;
        @Nullable protected String normalName; // lc version of tag name, for case insensitive tree build

        private final StringBuilder attrName = new StringBuilder(); // try to get attr names and vals in one shot, vs Builder
        @Nullable private String attrNameS;
        private boolean hasAttrName = false;

        private final StringBuilder attrValue = new StringBuilder();
        @Nullable private String attrValueS;
        private boolean hasAttrValue = false;
        private boolean hasEmptyAttrValue = false; // distinguish boolean attribute from empty string value

        boolean selfClosing = false;
        @Nullable Attributes attributes; // start tags get attributes on construction. End tags get attributes on first new attribute (but only for parser convenience, not used).

//@ requires tagName!= null;
//@ requires normalName!= null;
//@ requires attrName!= null;
//@ requires attrValue!= null;
//@ ensures this.tagName == tagName;
//@ ensures this.normalName == normalName;
//@ ensures attrNameS == attrName;
//@ ensures this.hasAttrName == true;
//@ ensures this.attrValue == attrValue;
        @Override
        Tag reset() {
            super.reset();
            tagName = null;
            normalName = null;
            reset(attrName);
            attrNameS = null;
            hasAttrName = false;
            reset(attrValue);
            attrValueS = null;
            hasEmptyAttrValue = false;
            hasAttrValue = false;
            selfClosing = false;
            attributes = null;
            return this;
        }

        /* Limits runaway crafted HTML from spewing attributes and getting a little sluggish in ensureCapacity.
        Real-world HTML will P99 around 8 attributes, so plenty of headroom. Implemented here and not in the Attributes
        object so that API users can add more if ever required. */
        private static final int MaxAttributes = 512;

//@ requires attrName!= null;
//@ requires attrValue!= null;
//@ ensures  hasAttrName == \old(hasAttrName) && \old(attrNameS) == null;
//@ ensures  hasEmptyAttrValue == \old(hasEmptyAttrValue) && \old(attrValueS) == null;
        final void newAttribute() {
            if (attributes == null)
                attributes = new Attributes();

            if (hasAttrName && attributes.size() < MaxAttributes) {
                // the tokeniser has skipped whitespace control chars, but trimming could collapse to empty for other control codes, so verify here
                String name = attrName.length() > 0 ? attrName.toString() : attrNameS;
                name = name.trim();
                if (name.length() > 0) {
                    String value;
                    if (hasAttrValue)
                        value = attrValue.length() > 0 ? attrValue.toString() : attrValueS;
                    else if (hasEmptyAttrValue)
                        value = "";
                    else
                        value = null;
                    // note that we add, not put. So that the first is kept, and rest are deduped, once in a context where case sensitivity is known (the appropriate tree builder).
                    attributes.add(name, value);
                }
            }
            reset(attrName);
            attrNameS = null;
            hasAttrName = false;

            reset(attrValue);
            attrValueS = null;
            hasAttrValue = false;
            hasEmptyAttrValue = false;
        }

//@ ensures \result == attributes!= null;
        final boolean hasAttributes() {
            return attributes != null;
        }

//@ ensures \result == (attributes!= null);
        final boolean hasAttribute(String key) {
            return attributes != null && attributes.hasKey(key);
        }

//@ requires hasAttrName!= null;
        final void finaliseTag() {
            // finalises for emit
            if (hasAttrName) {
                newAttribute();
            }
        }

        /** Preserves case */
//@ ensures \result!= null;
        final String name() { // preserves case, for input into Tag.valueOf (which may drop case)
            Validate.isFalse(tagName == null || tagName.length() == 0);
            return tagName;
        }

        /** Lower case */
//@ ensures \result!= null;
        final String normalName() { // lower case, used in tree building for working out where in tree it should go
            return normalName;
        }

//@ ensures \result!= null;
        final String toStringName() {
            return tagName != null ? tagName : "[unset]";
        }

//@ requires name!= null;
//@ ensures this.tagName == name;
//@ ensures this.normalName == name;
        final Tag name(String name) {
            tagName = name;
            normalName = ParseSettings.normalName(tagName);
            return this;
        }

//@ ensures \result == selfClosing;
        final boolean isSelfClosing() {
            return selfClosing;
        }

        // these appenders are rarely hit in not null state-- caused by null chars.
//@ requires append!= null;
//@ ensures normalName == ParseSettings.normalName(tagName);
        final void appendTagName(String append) {
            // might have null chars - need to replace with null replacement character
            append = append.replace(TokeniserState.nullChar, Tokeniser.replacementChar);
            tagName = tagName == null ? append : tagName.concat(append);
            normalName = ParseSettings.normalName(tagName);
        }

//@ requires append!= 0;
//@ ensures this.tagName == append;
//@ requires this.parent!= null;
//@ ensures this.parent.appendTagName(append);
        final void appendTagName(char append) {
            appendTagName(String.valueOf(append));
        }

//@ requires append!= null;
//@ ensures attrNameS == append;
//@ ensures attrName!= null;
//@ requires append.length() > 0;
//@ ensures attrNameS == append;
//@ ensures attrName!= null;
        final void appendAttributeName(String append) {
            // might have null chars because we eat in one pass - need to replace with null replacement character
            append = append.replace(TokeniserState.nullChar, Tokeniser.replacementChar);

            ensureAttrName();
            if (attrName.length() == 0) {
                attrNameS = append;
            } else {
                attrName.append(append);
            }
        }

//@ requires attrName.length() > 0;
//@ ensures attrName.append(append);
        final void appendAttributeName(char append) {
            ensureAttrName();
            attrName.append(append);
        }

//@ requires attrValue!= null;
//@ ensures attrValueS == append;
        final void appendAttributeValue(String append) {
            ensureAttrValue();
            if (attrValue.length() == 0) {
                attrValueS = append;
            } else {
                attrValue.append(append);
            }
        }

//@ requires attrValue.length() > 0;
        final void appendAttributeValue(char append) {
            ensureAttrValue();
            attrValue.append(append);
        }

//@ requires attrValue!= null;
        final void appendAttributeValue(char[] append) {
            ensureAttrValue();
            attrValue.append(append);
        }

//@ requires attrValue!= null;
//@ requires appendCodepoints!= null;
        final void appendAttributeValue(int[] appendCodepoints) {
            ensureAttrValue();
            for (int codepoint : appendCodepoints) {
                attrValue.appendCodePoint(codepoint);
            }
        }
        
//@ ensures hasEmptyAttrValue == true;
        final void setEmptyAttributeValue() {
            hasEmptyAttrValue = true;
        }

//@ requires attrName!= null;
//@ ensures hasAttrName == true;
//@ requires attrNameS!= null;
//@ ensures attrName.length() == attrNameS.length();
//@ requires attrNameS!= null;
//@ requires attrName!= null;
//@ ensures hasAttrName == true;
//@ requires attrNameS!= null;
//@ requires attrName!= null;
//@ ensures hasAttrName == true;
//@ requires attrNameS!= null;
        private void ensureAttrName() {
            hasAttrName = true;
            // if on second hit, we'll need to move to the builder
            if (attrNameS != null) {
                attrName.append(attrNameS);
                attrNameS = null;
            }
        }

//@ requires attrValue!= null;
//@ ensures hasAttrValue == true;
//@ requires attrValueS!= null;
//@ ensures attrValue.append(attrValueS);
//@ requires attrValueS!= null;
        private void ensureAttrValue() {
            hasAttrValue = true;
            // if on second hit, we'll need to move to the builder
            if (attrValueS != null) {
                attrValue.append(attrValueS);
                attrValueS = null;
            }
        }

        @Override
        abstract public String toString();
    }

    final static class StartTag extends Tag {
        StartTag() {
            super();
            type = TokenType.StartTag;
        }

//@ requires attributes!= null;
        @Override
        Tag reset() {
            super.reset();
            attributes = null;
            return this;
        }

//@ requires name!= null;
//@ requires attributes!= null;
        StartTag nameAttr(String name, Attributes attributes) {
            this.tagName = name;
            this.attributes = attributes;
            normalName = ParseSettings.normalName(tagName);
            return this;
        }

//@ requires attributes!= null;
        @Override
        public String toString() {
            if (hasAttributes() && attributes.size() > 0)
                return "<" + toStringName() + " " + attributes.toString() + ">";
            else
                return "<" + toStringName() + ">";
        }
    }

    final static class EndTag extends Tag{
        EndTag() {
            super();
            type = TokenType.EndTag;
        }

//@ requires isOpen;
//@ ensures isOpen;
        @Override
        public String toString() {
            return "</" + toStringName() + ">";
        }
    }

    final static class Comment extends Token {
        private final StringBuilder data = new StringBuilder();
        private String dataS; // try to get in one shot
        boolean bogus = false;

//@ requires data!= null;
//@ ensures this.data == data;
//@ ensures this.dataS == null;
//@ requires data!= null;
//@ ensures \result.data == data;
//@ ensures \result.dataS == null;
        @Override
        Token reset() {
            super.reset();
            reset(data);
            dataS = null;
            bogus = false;
            return this;
        }

        Comment() {
            type = TokenType.Comment;
        }

//@ ensures \result == dataS;
        String getData() {
            return dataS != null ? dataS : data.toString();
        }

//@ requires data!= null;
//@ ensures data.length() == 0;
//@ ensures dataS == append;
        final Comment append(String append) {
            ensureData();
            if (data.length() == 0) {
                dataS = append;
            } else {
                data.append(append);
            }
            return this;
        }

//@ requires data!= null;
        final Comment append(char append) {
            ensureData();
            data.append(append);
            return this;
        }

//@ requires data!= null;
//@ requires dataS!= null;
        private void ensureData() {
            // if on second hit, we'll need to move to the builder
            if (dataS != null) {
                data.append(dataS);
                dataS = null;
            }
        }

//@ ensures getData() == data;
        @Override
        public String toString() {
            return "<!--" + getData() + "-->";
        }
    }

    static class Character extends Token implements Cloneable {
        private String data;

        Character() {
            super();
            type = TokenType.Character;
        }

//@ ensures data == null;
//@ ensures \result == this;
        @Override
        Token reset() {
            super.reset();
            data = null;
            return this;
        }

//@ ensures data!= null;
        Character data(String data) {
            this.data = data;
            return this;
        }

//@ ensures \result!= null;
        String getData() {
            return data;
        }

//@ ensures \result!= null;
        @Override
        public String toString() {
            return getData();
        }

//@ requires true;
//@ ensures \result!= null;
        @Override protected Token.Character clone() {
            try {
                return (Token.Character) super.clone();
            } catch (CloneNotSupportedException e) {
                throw new RuntimeException(e);
            }
        }
    }

    final static class CData extends Character {
        CData(String data) {
            super();
            this.data(data);
        }

//@ ensures \result!= null;
        @Override
        public String toString() {
            return "<![CDATA[" + getData() + "]]>";
        }

    }

    final static class EOF extends Token {
        EOF() {
            type = Token.TokenType.EOF;
        }

//@ ensures \result == this;
        @Override
        Token reset() {
            super.reset();
            return this;
        }

//@ ensures \result!= null;
        @Override
        public String toString() {
            return "";
        }
    }

//@ ensures \result <==> type == TokenType.Doctype;
    final boolean isDoctype() {
        return type == TokenType.Doctype;
    }

//@ ensures \result!= null;
    final Doctype asDoctype() {
        return (Doctype) this;
    }

//@ ensures \result <==> type == TokenType.StartTag;
    final boolean isStartTag() {
        return type == TokenType.StartTag;
    }

//@ ensures \result!= null;
    final StartTag asStartTag() {
        return (StartTag) this;
    }

//@ ensures \result <==> type == TokenType.EndTag;
    final boolean isEndTag() {
        return type == TokenType.EndTag;
    }

//@ ensures \result!= null;
    final EndTag asEndTag() {
        return (EndTag) this;
    }

//@ ensures \result == type;
    final boolean isComment() {
        return type == TokenType.Comment;
    }

//@ ensures \return == this;
    final Comment asComment() {
        return (Comment) this;
    }

//@ ensures \result <==> type == TokenType.Character;
    final boolean isCharacter() {
        return type == TokenType.Character;
    }

//@ ensures \result <==> this instanceof CData;
    final boolean isCData() {
        return this instanceof CData;
    }

//@ ensures \result!= null;
    final Character asCharacter() {
        return (Character) this;
    }

//@ ensures \result <==> type == TokenType.EOF;
    final boolean isEOF() {
        return type == TokenType.EOF;
    }

    public enum TokenType {
        Doctype,
        StartTag,
        EndTag,
        Comment,
        Character, // note no CData - treated in builder as an extension of Character
        EOF
    }
}
