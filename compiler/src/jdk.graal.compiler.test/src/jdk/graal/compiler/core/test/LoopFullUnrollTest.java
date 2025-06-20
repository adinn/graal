/*
 * Copyright (c) 2017, 2025, Oracle and/or its affiliates. All rights reserved.
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

import jdk.graal.compiler.api.directives.GraalDirectives;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.debug.DebugDumpScope;
import jdk.graal.compiler.loop.phases.LoopFullUnrollPhase;
import jdk.graal.compiler.nodes.LoopBeginNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.StructuredGraph.AllowAssumptions;
import jdk.graal.compiler.nodes.loop.DefaultLoopPolicies;
import jdk.graal.compiler.nodes.spi.CoreProviders;
import jdk.graal.compiler.phases.common.DisableOverflownCountedLoopsPhase;

import org.junit.Test;

public class LoopFullUnrollTest extends GraalCompilerTest {

    public static int testMinToMax(int input) {
        int ret = 2;
        int current = input;
        for (long i = Long.MIN_VALUE; i < Long.MAX_VALUE; i++) {
            ret *= 2 + current;
            current /= 50;
        }
        return ret;
    }

    @Test
    public void runMinToMax() throws Throwable {
        test("testMinToMax", 1);
    }

    public static int testMinTo0(int input) {
        int ret = 2;
        int current = input;
        for (long i = Long.MIN_VALUE; i <= 0; i++) {
            ret *= 2 + current;
            current /= 50;
        }
        return ret;
    }

    @Test
    public void runMinTo0() throws Throwable {
        test("testMinTo0", 1);
    }

    public static int testNegativeTripCount(int input) {
        int ret = 2;
        int current = input;
        for (long i = 0; i <= -20; i++) {
            ret *= 2 + current;
            current /= 50;
        }
        return ret;
    }

    @Test
    public void runNegativeTripCount() throws Throwable {
        test("testNegativeTripCount", 0);
    }

    private void test(String snippet, int loopCount) {
        DebugContext debug = getDebugContext();
        try (DebugContext.Scope _ = debug.scope(getClass().getSimpleName(), new DebugDumpScope(snippet))) {
            final StructuredGraph graph = parseEager(snippet, AllowAssumptions.NO, debug);

            new DisableOverflownCountedLoopsPhase().apply(graph);

            CoreProviders context = getProviders();
            new LoopFullUnrollPhase(createCanonicalizerPhase(), new DefaultLoopPolicies()).apply(graph, context);

            assertTrue(graph.getNodes().filter(LoopBeginNode.class).count() == loopCount);
        } catch (Throwable e) {
            throw debug.handle(e);
        }
    }

    public static int snippetFlows() {
        int init = Integer.MIN_VALUE;
        int step = -1;
        int limit = 1;
        int phi = init;
        while (Integer.MIN_VALUE - phi < limit) {
            GraalDirectives.sideEffect();
            phi = phi + step;
        }
        return phi;
    }

    @Test
    public void testFlows() {
        test("snippetFlows");
    }

    public static int snippetFlows2() {
        int init = Integer.MAX_VALUE;
        int step = -8;
        int limit = 8184;
        int phi = init;
        while (Integer.MIN_VALUE - phi < limit) {
            GraalDirectives.sideEffect();
            phi = phi + step;
        }
        return phi;
    }

    @Test
    public void testFlows2() {
        test("snippetFlows2");
    }
}
