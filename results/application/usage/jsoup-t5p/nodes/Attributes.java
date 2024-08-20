package org.jsoup.nodes;

import org.jsoup.SerializationException;
import org.jsoup.helper.Validate;
import org.jsoup.internal.StringUtil;
import org.jsoup.parser.ParseSettings;

import javax.annotation.Nullable;
import java.io.IOException;
import java.util.AbstractMap;
import java.util.AbstractSet;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.jsoup.internal.Normalizer.lowerCase;

/**
 * The attributes of an Element.
 * <p>
 * Attributes are treated as a map: there can be only one value associated with an attribute key/name.
 * </p>
 * <p>
 * Attribute name and value comparisons are generally <b>case sensitive</b>. By default for HTML, attribute names are
 * normalized to lower-case on parsing. That means you should use lower-case strings when referring to attributes by
 * name.
 * </p>
 *
 * @author Jonathan Hedley, jonathan@hedley.net
 */
public class Attributes implements Iterable<Attribute>, Cloneable {
    // The Attributes object is only created on the first use of an attribute; the Element will just have a null
    // Attribute slot otherwise
    protected static final String dataPrefix = "data-";
    // Indicates a jsoup internal key. Can't be set via HTML. (It could be set via accessor, but not too worried about
    // that. Suppressed from list, iter.
    static final char InternalPrefix = '/';
    private static final int InitialCapacity = 3; // sampling found mean count when attrs present = 1.49; 1.08 overall. 2.6:1 don't have any attrs.

    // manages the key/val arrays
    private static final int GrowthFactor = 2;
    static final int NotFound = -1;
    private static final String EmptyString = "";

    // the number of instance fields is kept as low as possible giving an object size of 24 bytes
    private int size = 0; // number of slots used (not total capacity, which is keys.length)
    String[] keys = new String[InitialCapacity];
    Object[] vals = new Object[InitialCapacity]; // Genericish: all non-internal attribute values must be Strings and are cast on access.

    // check there's room for more
//@ requires capacity >= 0;
    private void checkCapacity(int minNewSize) {
        Validate.isTrue(minNewSize >= size);
        int curCap = keys.length;
        if (curCap >= minNewSize)
            return;
        int newCap = curCap >= InitialCapacity ? size * GrowthFactor : InitialCapacity;
        if (minNewSize > newCap)
            newCap = minNewSize;

        keys = Arrays.copyOf(keys, newCap);
        vals = Arrays.copyOf(vals, newCap);
    }

//@ requires key!= null;
//@ ensures \result >= 0;
    int indexOfKey(String key) {
        Validate.notNull(key);
        for (int i = 0; i < size; i++) {
            if (key.equals(keys[i]))
                return i;
        }
        return NotFound;
    }

//@ requires key!= null;
//@ ensures \result >= 0;
    private int indexOfKeyIgnoreCase(String key) {
        Validate.notNull(key);
        for (int i = 0; i < size; i++) {
            if (key.equalsIgnoreCase(keys[i]))
                return i;
        }
        return NotFound;
    }

    // we track boolean attributes as null in values - they're just keys. so returns empty for consumers
    // casts to String, so only for non-internal attributes
//@ ensures \result == null? EmptyString : (String) val;
    static String checkNotNull(@Nullable Object val) {
        return val == null ? EmptyString : (String) val;
    }

    /**
     Get an attribute value by key.
     @param key the (case-sensitive) attribute key
     @return the attribute value if set; or empty string if not set (or a boolean attribute).
     @see #hasKey(String)
     */
//@ requires!(key!= null);
//@ requires indexOfKey(key) >= 0;
    public String get(String key) {
        int i = indexOfKey(key);
        return i == NotFound ? EmptyString : checkNotNull(vals[i]);
    }

    /**
     * Get an attribute's value by case-insensitive key
     * @param key the attribute name
     * @return the first matching attribute value if set; or empty string if not set (ora boolean attribute).
     */
//@ requires key!= null;
//@ requires vals!= null;
//@ ensures \result!= null;
    public String getIgnoreCase(String key) {
        int i = indexOfKeyIgnoreCase(key);
        return i == NotFound ? EmptyString : checkNotNull(vals[i]);
    }

    /**
     Get an arbitrary user data object by key.
     * @param key case sensitive key to the object.
     * @return the object associated to this key, or {@code null} if not found.
     */
//@ requires isOpen;
//@ ensures isOpen;
    @Nullable
    Object getUserData(String key) {
        Validate.notNull(key);
        if (!isInternalKey(key)) key = internalKey(key);
        int i = indexOfKeyIgnoreCase(key);
        return i == NotFound ? null : vals[i];
    }

    /**
     * Adds a new attribute. Will produce duplicates if the key already exists.
     * @see Attributes#put(String, String)
     */
//@ requires ((this.root == null) || this.root.consistency()) && (this.size == this.realSize());
//@ ensures true;
    public Attributes add(String key, @Nullable String value) {
        addObject(key, value);
        return this;
    }

//@ requires capacity >= 0;
    private void addObject(String key, @Nullable Object value) {
        checkCapacity(size + 1);
        keys[size] = key;
        vals[size] = value;
        size++;
    }

    /**
     * Set a new attribute, or replace an existing one by key.
     * @param key case sensitive attribute key (not null)
     * @param value attribute value (may be null, to set a boolean attribute)
     * @return these attributes, for chaining
     */
//@ requires key!= null;
//@ ensures \result.containsKey(key);
    public Attributes put(String key, @Nullable String value) {
        Validate.notNull(key);
        int i = indexOfKey(key);
        if (i != NotFound)
            vals[i] = value;
        else
            add(key, value);
        return this;
    }

    /**
     Put an arbitrary user-data object by key. Will be treated as an internal attribute, so will not be emitted in HTML.
     * @param key case sensitive key
     * @param value object value
     * @return these attributes
     * @see #getUserData(String)
     */
//@ requires isOpen;
//@ ensures isOpen;
    Attributes putUserData(String key, Object value) {
        Validate.notNull(key);
        if (!isInternalKey(key)) key = internalKey(key);
        Validate.notNull(value);
        int i = indexOfKey(key);
        if (i != NotFound)
            vals[i] = value;
        else
            addObject(key, value);
        return this;
    }

//@ requires (keys!= null && vals!= null) || (keys.length == 1);
//@ ensures (keys!= null && vals.length == 1) || (keys.length == 0);
    void putIgnoreCase(String key, @Nullable String value) {
        int i = indexOfKeyIgnoreCase(key);
        if (i != NotFound) {
            vals[i] = value;
            if (!keys[i].equals(key)) // case changed, update
                keys[i] = key;
        }
        else
            add(key, value);
    }

    /**
     * Set a new boolean attribute, remove attribute if value is false.
     * @param key case <b>insensitive</b> attribute key
     * @param value attribute value
     * @return these attributes, for chaining
     */
//@ requires ((this.root == null) || this.root.consistency()) && (this.size == this.realSize());
//@ ensures true;
    public Attributes put(String key, boolean value) {
        if (value)
            putIgnoreCase(key, null);
        else
            remove(key);
        return this;
    }

    /**
     Set a new attribute, or replace an existing one by key.
     @param attribute attribute with case sensitive key
     @return these attributes, for chaining
     */
//@ requires attributeName!= null;
//@ ensures  this.attributeName == attributeName;
//@ requires attributeName!= null;
//@ requires value!= null;
//@ ensures  this.attributeName == attributeName;
//@ requires attributeName!= null;
//@ requires value!= null;
//@ ensures  this.attributeName == attributeName;
//@ requires attributeName!= null;
//@ ensures  this.attributeName == attributeName;
//@ requires attributeName!= null;
//@ requires value!= null;
//@ ensures  this.attributeName == attributeName;
//@ requires attributeName!= null;
//@ ensures  this.attributeName == attributeName;
    public Attributes put(Attribute attribute) {
        Validate.notNull(attribute);
        put(attribute.getKey(), attribute.getValue());
        attribute.parent = this;
        return this;
    }

    // removes and shifts up
//@ requires 0 <= index && index < size;
    @SuppressWarnings("AssignmentToNull")
    private void remove(int index) {
        Validate.isFalse(index >= size);
        int shifted = size - index - 1;
        if (shifted > 0) {
            System.arraycopy(keys, index + 1, keys, index, shifted);
            System.arraycopy(vals, index + 1, vals, index, shifted);
        }
        size--;
        keys[size] = null; // release hold
        vals[size] = null;
    }

    /**
     Remove an attribute by key. <b>Case sensitive.</b>
     @param key attribute key to remove
     */
//@ requires key!= null;
//@ requires indexOfKey(key) >= 0;
    public void remove(String key) {
        int i = indexOfKey(key);
        if (i != NotFound)
            remove(i);
    }

    /**
     Remove an attribute by key. <b>Case insensitive.</b>
     @param key attribute key to remove
     */
//@ requires key!= null;
//@ requires (forall int i; 0 <= i && i < size(); 0 <= key.length() && key.length() < numAttributes());
    public void removeIgnoreCase(String key) {
        int i = indexOfKeyIgnoreCase(key);
        if (i != NotFound)
            remove(i);
    }

    /**
     Tests if these attributes contain an attribute with this key.
     @param key case-sensitive key to check for
     @return true if key exists, false otherwise
     */
//@ ensures \result == (\exists int i; 0 <= i && i < keys.length; key == keys[i]);
    public boolean hasKey(String key) {
        return indexOfKey(key) != NotFound;
    }

    /**
     Tests if these attributes contain an attribute with this key.
     @param key key to check for
     @return true if key exists, false otherwise
     */
//@ ensures \result == (indexOfKeyIgnoreCase(key)!= NotFound);
    public boolean hasKeyIgnoreCase(String key) {
        return indexOfKeyIgnoreCase(key) != NotFound;
    }

    /**
     * Check if these attributes contain an attribute with a value for this key.
     * @param key key to check for
     * @return true if key exists, and it has a value
     */
//@ requires key!= null;
//@ requires indexOfKey(key) >= 0;
    public boolean hasDeclaredValueForKey(String key) {
        int i = indexOfKey(key);
        return i != NotFound && vals[i] != null;
    }

    /**
     * Check if these attributes contain an attribute with a value for this key.
     * @param key case-insensitive key to check for
     * @return true if key exists, and it has a value
     */
//@ requires false;
    public boolean hasDeclaredValueForKeyIgnoreCase(String key) {
        int i = indexOfKeyIgnoreCase(key);
        return i != NotFound && vals[i] != null;
    }

    /**
     Get the number of attributes in this set, including any jsoup internal-only attributes. Internal attributes are
     excluded from the {@link #html()}, {@link #asList()}, and {@link #iterator()} methods.
     @return size
     */
//@ ensures \result == size;
    public int size() {
        return size;
    }

    /**
     * Test if this Attributes list is empty (size==0).
     */
//@ ensures \result <==> size == 0;
    public boolean isEmpty() {
        return size == 0;
    }

    /**
     Add all the attributes from the incoming set to this set.
     @param incoming attributes to add to these attributes.
     */
//@ requires incoming!= null;
//@ ensures size == \old(size) + incoming.size;
    public void addAll(Attributes incoming) {
        if (incoming.size() == 0)
            return;
        checkCapacity(size + incoming.size);

        boolean needsPut = size != 0; // if this set is empty, no need to check existing set, so can add() vs put()
        // (and save bashing on the indexOfKey()
        for (Attribute attr : incoming) {
            if (needsPut)
                put(attr);
            else
                add(attr.getKey(), attr.getValue());
        }
    }

//@ requires keys!= null;
//@ requires vals!= null;
    public Iterator<Attribute> iterator() {
        return new Iterator<Attribute>() {
            int i = 0;

//@ requires 0 <= first;
//@ requires 0 <= toCopy;
//@ requires first + toCopy <= source.numInstances();
            @Override
            public boolean hasNext() {
                while (i < size) {
                    if (isInternalKey(keys[i])) // skip over internal keys
                        i++;
                    else
                        break;
                }

                return i < size;
            }

//@ requires i < keys.length;
//@ ensures i < vals.length;
            @Override
            public Attribute next() {
                final Attribute attr = new Attribute(keys[i], (String) vals[i], Attributes.this);
                i++;
                return attr;
            }

//@ requires i >= 0;
            @Override
            public void remove() {
                Attributes.this.remove(--i); // next() advanced, so rewind
            }
        };
    }

    /**
     Get the attributes as a List, for iteration.
     @return a view of the attributes as an unmodifiable List.
     */
//@ requires size > 0;
    public List<Attribute> asList() {
        ArrayList<Attribute> list = new ArrayList<>(size);
        for (int i = 0; i < size; i++) {
            if (isInternalKey(keys[i]))
                continue; // skip internal keys
            Attribute attr = new Attribute(keys[i], (String) vals[i], Attributes.this);
            list.add(attr);
        }
        return Collections.unmodifiableList(list);
    }

    /**
     * Retrieves a filtered view of attributes that are HTML5 custom data attributes; that is, attributes with keys
     * starting with {@code data-}.
     * @return map of custom data attributes.
     */
//@ ensures \result!= null;
    public Map<String, String> dataset() {
        return new Dataset(this);
    }

    /**
     Get the HTML representation of these attributes.
     @return HTML
     */
//@ ensures \result!= null;
    public String html() {
        StringBuilder sb = StringUtil.borrowBuilder();
        try {
            html(sb, (new Document("")).outputSettings()); // output settings a bit funky, but this html() seldom used
        } catch (IOException e) { // ought never happen
            throw new SerializationException(e);
        }
        return StringUtil.releaseBuilder(sb);
    }

//@ requires accum!= null && out!= null;
//@ requires size > 0;
    final void html(final Appendable accum, final Document.OutputSettings out) throws IOException {
        final int sz = size;
        for (int i = 0; i < sz; i++) {
            if (isInternalKey(keys[i]))
                continue;
            final String key = Attribute.getValidKey(keys[i], out.syntax());
            if (key != null)
                Attribute.htmlNoValidate(key, (String) vals[i], accum.append(' '), out);
        }
    }

//@ ensures \result!= null;
    @Override
    public String toString() {
        return html();
    }

    /**
     * Checks if these attributes are equal to another set of attributes, by comparing the two sets. Note that the order
     * of the attributes does not impact this equality (as per the Map interface equals()).
     * @param o attributes to compare with
     * @return if both sets of attributes have the same content
     */
//@ requires 0 <= first;
//@ requires 0 <= toCopy;
//@ requires first + toCopy <= source.numAttributes();
    @Override
    public boolean equals(@Nullable Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        Attributes that = (Attributes) o;
        if (size != that.size) return false;
        for (int i = 0; i < size; i++) {
            String key = keys[i];
            int thatI = that.indexOfKey(key);
            if (thatI == NotFound)
                return false;
            Object val = vals[i];
            Object thatVal = that.vals[thatI];
            if (val == null) {
                if (thatVal != null)
                    return false;
            } else if (!val.equals(thatVal))
                return false;
        }
        return true;
    }

    /**
     * Calculates the hashcode of these attributes, by iterating all attributes and summing their hashcodes.
     * @return calculated hashcode
     */
//@ requires 0 <= first;
//@ requires 0 <= toCopy;
//@ requires first + toCopy <= source.numInstances();
    @Override
    public int hashCode() {
        int result = size;
        result = 31 * result + Arrays.hashCode(keys);
        result = 31 * result + Arrays.hashCode(vals);
        return result;
    }

//@ requires size!= 0;
//@ ensures size == \old(size) + 1;
    @Override
    public Attributes clone() {
        Attributes clone;
        try {
            clone = (Attributes) super.clone();
        } catch (CloneNotSupportedException e) {
            throw new RuntimeException(e);
        }
        clone.size = size;
        clone.keys = Arrays.copyOf(keys, size);
        clone.vals = Arrays.copyOf(vals, size);
        return clone;
    }

    /**
     * Internal method. Lowercases all keys.
     */
//@ requires 0 <= first && first <= size && size < keys.length;
    public void normalize() {
        for (int i = 0; i < size; i++) {
            keys[i] = lowerCase(keys[i]);
        }
    }

    /**
     * Internal method. Removes duplicate attribute by name. Settings for case sensitivity of key names.
     * @param settings case sensitivity
     * @return number of removed dupes
     */
//@ ensures \result == 0;
    public int deduplicate(ParseSettings settings) {
        if (isEmpty())
            return 0;
        boolean preserve = settings.preserveAttributeCase();
        int dupes = 0;
        OUTER: for (int i = 0; i < keys.length; i++) {
            for (int j = i + 1; j < keys.length; j++) {
                if (keys[j] == null)
                    continue OUTER; // keys.length doesn't shrink when removing, so re-test
                if ((preserve && keys[i].equals(keys[j])) || (!preserve && keys[i].equalsIgnoreCase(keys[j]))) {
                    dupes++;
                    remove(j);
                    j--;
                }
            }
        }
        return dupes;
    }

    private static class Dataset extends AbstractMap<String, String> {
        private final Attributes attributes;

        private Dataset(Attributes attributes) {
            this.attributes = attributes;
        }

//@ requires (e.getKey()!= null && e.getValue()!= null);
//@ ensures (e.getKey()!= null && e.getValue()!= null) && \fresh(\result);
        @Override
        public Set<Entry<String, String>> entrySet() {
            return new EntrySet();
        }

//@ requires 0 <= key && key < size();
        @Override
        public String put(String key, String value) {
            String dataKey = dataKey(key);
            String oldValue = attributes.hasKey(dataKey) ? attributes.get(dataKey) : null;
            attributes.put(dataKey, value);
            return oldValue;
        }

        private class EntrySet extends AbstractSet<Map.Entry<String, String>> {

//@ requires numAttributes > 0;    // Or maybe == 0 is okay too?
//@ ensures this.numAttributes == numAttributes;
//@ ensures this.data!= null;
//@ ensures \fresh(this.data);
            @Override
            public Iterator<Map.Entry<String, String>> iterator() {
                return new DatasetIterator();
            }

//@ requires iter.hasNext();
            @Override
            public int size() {
                int count = 0;
                Iterator iter = new DatasetIterator();
                while (iter.hasNext())
                    count++;
                return count;
            }
        }

        private class DatasetIterator implements Iterator<Map.Entry<String, String>> {
            private Iterator<Attribute> attrIter = attributes.iterator();
            private Attribute attr;
//@ requires attrIter!= null;
            public boolean hasNext() {
                while (attrIter.hasNext()) {
                    attr = attrIter.next();
                    if (attr.isDataAttribute()) return true;
                }
                return false;
            }

//@ requires attr!= null && dataPrefix!= null;
            public Entry<String, String> next() {
                return new Attribute(attr.getKey().substring(dataPrefix.length()), attr.getValue());
            }

//@ requires attr!= null;
            public void remove() {
                attributes.remove(attr.getKey());
            }
        }
    }

//@ ensures \result!= null;
    private static String dataKey(String key) {
        return dataPrefix + key;
    }

//@ ensures \result.equals(InternalPrefix + key);
    static String internalKey(String key) {
        return InternalPrefix + key;
    }

//@ ensures \result == (key!= null && key.length() > 1 && key.charAt(0) == InternalPrefix);
    private boolean isInternalKey(String key) {
        return key != null && key.length() > 1 && key.charAt(0) == InternalPrefix;
    }
}
