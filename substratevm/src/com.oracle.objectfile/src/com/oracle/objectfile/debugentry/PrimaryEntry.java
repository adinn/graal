/*
 * Copyright (c) 2020, 2020, Oracle and/or its affiliates. All rights reserved.
 * Copyright (c) 2020, 2020, Red Hat Inc. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */

package com.oracle.objectfile.debugentry;

import com.oracle.objectfile.debuginfo.DebugInfoProvider.DebugFrameSizeChange;

import java.util.Iterator;
import java.util.List;
import java.util.Stack;

/**
 * Tracks debug info associated with a primary method. i.e. a top level compiled method
 */
public class PrimaryEntry {
    /**
     * The primary range detailed by this object.
     */
    private Range primary;
    /**
     * Details of the class owning this range.
     */
    private ClassEntry classEntry;
    /**
     * Details of of compiled method frame size changes.
     */
    private List<DebugFrameSizeChange> frameSizeInfos;
    /**
     * Size of compiled method frame.
     */
    private int frameSize;

    public PrimaryEntry(Range primary, List<DebugFrameSizeChange> frameSizeInfos, int frameSize, ClassEntry classEntry) {
        this.primary = primary;
        this.classEntry = classEntry;
        this.frameSizeInfos = frameSizeInfos;
        this.frameSize = frameSize;
    }

    public Range getPrimary() {
        return primary;
    }

    public ClassEntry getClassEntry() {
        return classEntry;
    }

    public Iterator<Range> topDownIterator() {
        return new Iterator<Range>() {
            final Stack<Range> workList = new Stack<>();
            Range current = primary.getFirstCallee();

            @Override
            public boolean hasNext() {
                return current != null;
            }

            @Override
            public Range next() {
                assert hasNext();
                Range result = current;
                forward();
                return result;
            }

            private void forward() {
                Range sibling = current.getNextCallee();
                if (!current.isLeaf()) {
                    // save next sibling while we process the children
                    if (sibling != null) {
                        workList.push(sibling);
                    }
                    current = current.getFirstCallee();
                } else if (sibling != null) {
                    current = sibling;
                } else {
                    // return back up to parents' siblings
                    current = workList.isEmpty() ? null : workList.pop();
                }
            }
        };
    }

    public Iterator<Range> leafIterator() {
        final Iterator<Range> t = topDownIterator();
        return new Iterator<Range>() {
            Range current = forwardLeaf(t);

            @Override
            public boolean hasNext() {
                return current != null;
            }

            @Override
            public Range next() {
                assert hasNext();
                Range result = current;
                current = forwardLeaf(t);
                return result;
            }

            private Range forwardLeaf(Iterator<Range> t) {
                if (t.hasNext()) {
                    Range next = t.next();
                    while (next != null && !next.isLeaf()) {
                        next = t.next();
                    }
                    return next;
                }
                return null;
            }
        };
    }

    public List<DebugFrameSizeChange> getFrameSizeInfos() {
        return frameSizeInfos;
    }

    public int getFrameSize() {
        return frameSize;
    }
}
