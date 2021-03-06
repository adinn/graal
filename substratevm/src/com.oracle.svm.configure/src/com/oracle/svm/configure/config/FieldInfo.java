/*
 * Copyright (c) 2019, 2019, Oracle and/or its affiliates. All rights reserved.
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
package com.oracle.svm.configure.config;

final class FieldInfo {
    private static final FieldInfo[] FINAL_NOT_WRITABLE_CACHE;
    static {
        ConfigurationMemberKind[] values = ConfigurationMemberKind.values();
        FINAL_NOT_WRITABLE_CACHE = new FieldInfo[values.length];
        for (ConfigurationMemberKind value : values) {
            FINAL_NOT_WRITABLE_CACHE[value.ordinal()] = new FieldInfo(value, false);
        }
    }

    static FieldInfo get(ConfigurationMemberKind kind, boolean finalButWritable) {
        if (finalButWritable) { // assumed to be rare
            return new FieldInfo(kind, finalButWritable);
        }
        return FINAL_NOT_WRITABLE_CACHE[kind.ordinal()];
    }

    private final ConfigurationMemberKind kind;
    private final boolean finalButWritable;

    private FieldInfo(ConfigurationMemberKind kind, boolean finalButWritable) {
        this.kind = kind;
        this.finalButWritable = finalButWritable;
    }

    public ConfigurationMemberKind getKind() {
        return kind;
    }

    public boolean isFinalButWritable() {
        return finalButWritable;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj != this && obj instanceof FieldInfo) {
            FieldInfo other = (FieldInfo) obj;
            return kind.equals(other.kind) && finalButWritable == other.finalButWritable;
        }
        return (obj == this);
    }

    @Override
    public int hashCode() {
        return Boolean.hashCode(finalButWritable) * 31 + kind.hashCode();
    }
}
