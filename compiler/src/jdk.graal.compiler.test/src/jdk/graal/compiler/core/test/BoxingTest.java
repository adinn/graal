/*
 * Copyright (c) 2015, 2018, Oracle and/or its affiliates. All rights reserved.
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
package jdk.graal.compiler.core.test;

import org.junit.Test;

public class BoxingTest extends GraalCompilerTest {

    public static Object boxSnippet(int arg) {
        return arg;
    }

    @Test
    public void test0() {
        test("boxSnippet", 0);
    }

    @Test
    public void test5() {
        test("boxSnippet", 5);
    }

    @Test
    public void testMinus5() {
        test("boxSnippet", -5);
    }

    @Test
    public void test300() {
        test("boxSnippet", 300);
    }

    @Test
    public void testMinus300() {
        test("boxSnippet", -300);
    }

    public static Object boxInt(int arg) {
        return arg;
    }

    public static Object boxLong(long arg) {
        return arg;
    }

    public static Object boxByte(byte arg) {
        return arg;
    }

    public static Object boxChar(char arg) {
        return arg;
    }

    public static Object boxBoolean(boolean arg) {
        return arg;
    }

    public static Object boxShort(short arg) {
        return arg;
    }

    @Test
    public void boxInt0() {
        test("boxInt", 0);
    }

    @Test
    public void boxByte0() {
        test("boxByte", (byte) 0);
    }

    @Test
    public void boxLong0() {
        test("boxLong", (long) 0);
    }

    @Test
    public void boxChar0() {
        test("boxChar", (char) 0);
    }

    @Test
    public void boxBoolean0() {
        test("boxBoolean", false);
    }

    @Test
    public void boxShort0() {
        test("boxShort", (short) 0);
    }
}
