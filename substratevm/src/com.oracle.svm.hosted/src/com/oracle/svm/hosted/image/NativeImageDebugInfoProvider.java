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
package com.oracle.svm.hosted.image;

import static com.oracle.objectfile.debuginfo.DebugInfoProvider.DebugFrameSizeChange.Type.CONTRACT;
import static com.oracle.objectfile.debuginfo.DebugInfoProvider.DebugFrameSizeChange.Type.EXTEND;

import java.lang.reflect.Modifier;
import java.nio.file.NotDirectoryException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.function.Consumer;
import java.util.stream.Stream;

import com.oracle.svm.core.heap.ReferenceMapEncoder;
import com.oracle.svm.core.heap.SubstrateReferenceMap;
import com.oracle.svm.core.meta.DirectSubstrateObjectConstant;
import com.oracle.svm.core.meta.SubstrateObjectConstant;
import jdk.vm.ci.code.BytecodeFrame;
import jdk.vm.ci.code.BytecodePosition;
import jdk.vm.ci.code.DebugInfo;
import jdk.vm.ci.code.ReferenceMap;
import jdk.vm.ci.code.site.Call;
import jdk.vm.ci.code.site.ImplicitExceptionDispatch;
import jdk.vm.ci.code.site.Infopoint;
import jdk.vm.ci.code.site.InfopointReason;
import jdk.vm.ci.meta.JavaConstant;
import jdk.vm.ci.meta.JavaType;
import jdk.vm.ci.meta.JavaValue;
import jdk.vm.ci.meta.Local;
import jdk.vm.ci.meta.LocalVariableTable;
import jdk.vm.ci.meta.Value;
import org.graalvm.compiler.code.CompilationResult;
import org.graalvm.compiler.code.SourceMapping;
import org.graalvm.compiler.core.common.CompressEncoding;
import org.graalvm.compiler.debug.DebugContext;
import org.graalvm.compiler.graph.NodeSourcePosition;
import org.graalvm.nativeimage.ImageSingletons;

import com.oracle.graal.pointsto.infrastructure.OriginalClassProvider;
import com.oracle.graal.pointsto.infrastructure.WrappedJavaMethod;
import com.oracle.objectfile.debuginfo.DebugInfoProvider;
import com.oracle.svm.core.StaticFieldsSupport;
import com.oracle.svm.core.SubstrateOptions;
import com.oracle.svm.core.config.ConfigurationValues;
import com.oracle.svm.core.config.ObjectLayout;
import com.oracle.svm.core.graal.code.SubstrateBackend;
import com.oracle.svm.core.heap.Heap;
import com.oracle.svm.core.heap.ObjectHeader;
import com.oracle.svm.core.image.ImageHeapPartition;
import com.oracle.svm.hosted.annotation.CustomSubstitutionMethod;
import com.oracle.svm.hosted.annotation.CustomSubstitutionType;
import com.oracle.svm.hosted.image.NativeImageHeap.ObjectInfo;
import com.oracle.svm.hosted.image.sources.SourceManager;
import com.oracle.svm.hosted.lambda.LambdaSubstitutionType;
import com.oracle.svm.hosted.meta.HostedArrayClass;
import com.oracle.svm.hosted.meta.HostedClass;
import com.oracle.svm.hosted.meta.HostedField;
import com.oracle.svm.hosted.meta.HostedInstanceClass;
import com.oracle.svm.hosted.meta.HostedInterface;
import com.oracle.svm.hosted.meta.HostedMethod;
import com.oracle.svm.hosted.meta.HostedPrimitiveType;
import com.oracle.svm.hosted.meta.HostedType;
import com.oracle.svm.hosted.substitute.InjectedFieldsType;
import com.oracle.svm.hosted.substitute.SubstitutionMethod;
import com.oracle.svm.hosted.substitute.SubstitutionType;

import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.LineNumberTable;
import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;
import jdk.vm.ci.meta.Signature;
import sun.jvm.hotspot.interpreter.Bytecode;

/**
 * Implementation of the DebugInfoProvider API interface that allows type, code and heap data info
 * to be passed to an ObjectFile when generation of debug info is enabled.
 */
class NativeImageDebugInfoProvider implements DebugInfoProvider {
    private final DebugContext debugContext;
    private final NativeImageCodeCache codeCache;
    @SuppressWarnings("unused") private final NativeImageHeap heap;
    boolean useHeapBase;
    int compressShift;
    int tagsMask;
    int referenceSize;
    int pointerSize;
    int referenceAlignment;
    int primitiveStartOffset;
    int referenceStartOffset;

    NativeImageDebugInfoProvider(DebugContext debugContext, NativeImageCodeCache codeCache, NativeImageHeap heap) {
        super();
        this.debugContext = debugContext;
        this.codeCache = codeCache;
        this.heap = heap;
        ObjectHeader objectHeader = Heap.getHeap().getObjectHeader();
        ObjectInfo primitiveFields = heap.getObjectInfo(StaticFieldsSupport.getStaticPrimitiveFields());
        ObjectInfo objectFields = heap.getObjectInfo(StaticFieldsSupport.getStaticObjectFields());
        this.tagsMask = objectHeader.getReservedBitsMask();
        if (SubstrateOptions.SpawnIsolates.getValue()) {
            CompressEncoding compressEncoding = ImageSingletons.lookup(CompressEncoding.class);
            this.useHeapBase = compressEncoding.hasBase();
            this.compressShift = (compressEncoding.hasShift() ? compressEncoding.getShift() : 0);
        } else {
            this.useHeapBase = false;
            this.compressShift = 0;
        }
        this.referenceSize = getObjectLayout().getReferenceSize();
        this.pointerSize = ConfigurationValues.getTarget().wordSize;
        this.referenceAlignment = getObjectLayout().getAlignment();
        /* Offsets need to be adjusted relative to the heap base plus partition-specific offset. */
        primitiveStartOffset = (int) primitiveFields.getOffset();
        referenceStartOffset = (int) objectFields.getOffset();
    }

    @Override
    public boolean useHeapBase() {
        return useHeapBase;
    }

    @Override
    public int oopCompressShift() {
        return compressShift;
    }

    @Override
    public int oopReferenceSize() {
        return referenceSize;
    }

    @Override
    public int pointerSize() {
        return pointerSize;
    }

    @Override
    public int oopAlignment() {
        return referenceAlignment;
    }

    @Override
    public int oopTagsMask() {
        return tagsMask;
    }

    @Override
    public Stream<DebugTypeInfo> typeInfoProvider() {
        Stream<DebugTypeInfo> headerTypeInfo = computeHeaderTypeInfo();
        Stream<DebugTypeInfo> heapTypeInfo = heap.getUniverse().getTypes().stream().map(this::createDebugTypeInfo);
        return Stream.concat(headerTypeInfo, heapTypeInfo);
    }

    @Override
    public Stream<DebugCodeInfo> codeInfoProvider() {
        return codeCache.compilations.entrySet().stream().map(entry -> new NativeImageDebugCodeInfo(entry.getKey(), entry.getValue()));
    }

    @Override
    public Stream<DebugDataInfo> dataInfoProvider() {
        return heap.getObjects().stream().filter(this::acceptObjectInfo).map(this::createDebugDataInfo);
    }

    static ObjectLayout getObjectLayout() {
        return ConfigurationValues.getObjectLayout();
    }

    /*
     * HostedType wraps an AnalysisType and both HostedType and AnalysisType punt calls to
     * getSourceFilename to the wrapped class so for consistency we need to do type names and path
     * lookup relative to the doubly unwrapped HostedType.
     *
     * However, note that the result of the unwrap on the AnalysisType may be a SubstitutionType
     * which wraps both an original type and the annotated type that substitutes it. Unwrapping
     * normally returns the AnnotatedType which we need to use to resolve the file name. However, we
     * need to use the original to name the owning type to ensure that names found in method param
     * and return types resolve correctly.
     */
    protected static ResolvedJavaType getDeclaringClass(HostedType hostedType, boolean wantOriginal) {
        // unwrap to the underlying class eihter the original or target class
        if (wantOriginal) {
            return getOriginal(hostedType);
        }
        // we want any substituted target if there is one. directly unwrapping will
        // do what we want.
        return hostedType.getWrapped().getWrapped();
    }

    protected static ResolvedJavaType getDeclaringClass(HostedMethod hostedMethod, boolean wantOriginal) {
        if (wantOriginal) {
            return getOriginal(hostedMethod.getDeclaringClass());
        }
        // we want a substituted target if there is one. if there is a substitution at the end of
        // the method chain fetch the annotated target class
        ResolvedJavaMethod javaMethod = hostedMethod.getWrapped().getWrapped();
        if (javaMethod instanceof SubstitutionMethod) {
            SubstitutionMethod substitutionMethod = (SubstitutionMethod) javaMethod;
            return substitutionMethod.getAnnotated().getDeclaringClass();
        }
        return javaMethod.getDeclaringClass();
    }

    @SuppressWarnings("unused")
    protected static ResolvedJavaType getDeclaringClass(HostedField hostedField, boolean wantOriginal) {
        /* for now fields are always reported as belonging to the original class */
        return getOriginal(hostedField.getDeclaringClass());
    }

    private static ResolvedJavaType getOriginal(HostedType hostedType) {
        /* partially unwrap then traverse through substitutions to the original */
        ResolvedJavaType javaType = hostedType.getWrapped().getWrappedWithoutResolve();
        if (javaType instanceof SubstitutionType) {
            return ((SubstitutionType) javaType).getOriginal();
        } else if (javaType instanceof CustomSubstitutionType<?, ?>) {
            return ((CustomSubstitutionType<?, ?>) javaType).getOriginal();
        } else if (javaType instanceof LambdaSubstitutionType) {
            return ((LambdaSubstitutionType) javaType).getOriginal();
        } else if (javaType instanceof InjectedFieldsType) {
            return ((InjectedFieldsType) javaType).getOriginal();
        }
        return javaType;
    }

    private static String toJavaName(JavaType javaType) {
        if (javaType instanceof HostedType) {
            return getDeclaringClass((HostedType) javaType, true).toJavaName();
        }
        return javaType.toJavaName();
    }

    public List<String> getParamTypes(ResolvedJavaMethod method) {
        Signature signature = method.getSignature();
        int parameterCount = signature.getParameterCount(false);
        List<String> paramTypes = new ArrayList<>(parameterCount);
        for (int i = 0; i < parameterCount; i++) {
            JavaType parameterType = signature.getParameterType(i, null);
            paramTypes.add(toJavaName(parameterType));
        }
        return paramTypes;
    }

    List<String> getParamNames(ResolvedJavaMethod method) {
        LocalVariableTable localsTable = method.getLocalVariableTable();
        Local[] params = (localsTable != null ? localsTable.getLocalsAt(0) : null);
        /* Can only provide blank names for now. */
        Signature signature = method.getSignature();
        int parameterCount = signature.getParameterCount(false);
        List<String> paramNames = new ArrayList<>(parameterCount);
        /* need to ignore this parameter for instance methods */
        int paramOffset = 1;
        if (method.isStatic()) {
            /* Signature includes no this parameter. */
            paramOffset = 0;
        } else {
            ResolvedJavaType declaringClass = method.getDeclaringClass();
            if (!declaringClass.isStatic() && declaringClass.getEnclosingType() != null) {
                /* Signature includes a special parameter for the outer instance. */
                paramOffset = 0;
            }
        }
        for (int i = 0, idx = paramOffset; i < parameterCount; i++, idx++) {
            String name;
            /* sometimes local vars may not be present */
            if (params != null && idx < params.length) {
                name = params[idx].getName();
            } else {
                // use a synthetic name
                name = "__arg" + i;
            }
            paramNames.add(name);
        }
        return paramNames;
    }

    private final Path cachePath = SubstrateOptions.getDebugInfoSourceCacheRoot();

    private abstract class NativeImageDebugFileInfo implements DebugFileInfo {
        private Path fullFilePath;

        @SuppressWarnings("try")
        NativeImageDebugFileInfo(HostedType hostedType) {
            ResolvedJavaType javaType = getDeclaringClass(hostedType, false);
            Class<?> clazz = hostedType.getJavaClass();
            SourceManager sourceManager = ImageSingletons.lookup(SourceManager.class);
            try (DebugContext.Scope s = debugContext.scope("DebugFileInfo", hostedType)) {
                fullFilePath = sourceManager.findAndCacheSource(javaType, clazz, debugContext);
            } catch (Throwable e) {
                throw debugContext.handle(e);
            }
        }

        @SuppressWarnings("try")
        NativeImageDebugFileInfo(HostedMethod hostedMethod) {
            ResolvedJavaType javaType = getDeclaringClass(hostedMethod, false);
            HostedType hostedType = hostedMethod.getDeclaringClass();
            Class<?> clazz = hostedType.getJavaClass();
            SourceManager sourceManager = ImageSingletons.lookup(SourceManager.class);
            try (DebugContext.Scope s = debugContext.scope("DebugFileInfo", hostedType)) {
                fullFilePath = sourceManager.findAndCacheSource(javaType, clazz, debugContext);
            } catch (Throwable e) {
                throw debugContext.handle(e);
            }
        }

        @SuppressWarnings("try")
        NativeImageDebugFileInfo(HostedField hostedField) {
            ResolvedJavaType javaType = getDeclaringClass(hostedField, false);
            HostedType hostedType = hostedField.getDeclaringClass();
            Class<?> clazz = hostedType.getJavaClass();
            SourceManager sourceManager = ImageSingletons.lookup(SourceManager.class);
            try (DebugContext.Scope s = debugContext.scope("DebugFileInfo", hostedType)) {
                fullFilePath = sourceManager.findAndCacheSource(javaType, clazz, debugContext);
            } catch (Throwable e) {
                throw debugContext.handle(e);
            }
        }

        @Override
        public String fileName() {
            if (fullFilePath != null) {
                Path filename = fullFilePath.getFileName();
                if (filename != null) {
                    return filename.toString();
                }
            }
            return "";
        }

        @Override
        public Path filePath() {
            if (fullFilePath != null) {
                return fullFilePath.getParent();
            }
            return null;
        }

        @Override
        public Path cachePath() {
            return cachePath;
        }
    }

    private abstract class NativeImageDebugTypeInfo extends NativeImageDebugFileInfo implements DebugTypeInfo {
        protected final HostedType hostedType;

        @SuppressWarnings("try")
        protected NativeImageDebugTypeInfo(HostedType hostedType) {
            super(hostedType);
            this.hostedType = hostedType;
        }

        @SuppressWarnings("try")
        @Override
        public void debugContext(Consumer<DebugContext> action) {
            try (DebugContext.Scope s = debugContext.scope("DebugTypeInfo", typeName())) {
                action.accept(debugContext);
            } catch (Throwable e) {
                throw debugContext.handle(e);
            }
        }

        public String toJavaName(@SuppressWarnings("hiding") HostedType hostedType) {
            return getDeclaringClass(hostedType, true).toJavaName();
        }

        @Override
        public String typeName() {
            return toJavaName(hostedType);
        }

        @Override
        public int size() {
            if (hostedType instanceof HostedInstanceClass) {
                /* We know the actual instance size in bytes. */
                return ((HostedInstanceClass) hostedType).getInstanceSize();
            } else if (hostedType instanceof HostedArrayClass) {
                /* Use the size of header common to all arrays of this type. */
                return getObjectLayout().getArrayBaseOffset(hostedType.getComponentType().getStorageKind());
            } else if (hostedType instanceof HostedInterface) {
                /* Use the size of the header common to all implementors. */
                return getObjectLayout().getFirstFieldOffset();
            } else {
                /* Use the number of bytes needed needed to store the value. */
                assert hostedType instanceof HostedPrimitiveType;
                JavaKind javaKind = hostedType.getStorageKind();
                return (javaKind == JavaKind.Void ? 0 : javaKind.getByteCount());
            }
        }
    }

    private class NativeImageHeaderTypeInfo implements DebugHeaderTypeInfo {
        String typeName;
        int size;
        List<DebugFieldInfo> fieldInfos;

        NativeImageHeaderTypeInfo(String typeName, int size) {
            this.typeName = typeName;
            this.size = size;
            this.fieldInfos = new LinkedList<>();
        }

        void addField(String name, String valueType, int offset, @SuppressWarnings("hiding") int size) {
            NativeImageDebugHeaderFieldInfo fieldinfo = new NativeImageDebugHeaderFieldInfo(name, typeName, valueType, offset, size);
            fieldInfos.add(fieldinfo);
        }

        @SuppressWarnings("try")
        @Override
        public void debugContext(Consumer<DebugContext> action) {
            try (DebugContext.Scope s = debugContext.scope("DebugTypeInfo", typeName())) {
                action.accept(debugContext);
            } catch (Throwable e) {
                throw debugContext.handle(e);
            }
        }

        @Override
        public String typeName() {
            return typeName;
        }

        @Override
        public DebugTypeKind typeKind() {
            return DebugTypeKind.HEADER;
        }

        @Override
        public String fileName() {
            return "";
        }

        @Override
        public Path filePath() {
            return null;
        }

        @Override
        public Path cachePath() {
            return null;
        }

        @Override
        public int size() {
            return size;
        }

        @Override
        public Stream<DebugFieldInfo> fieldInfoProvider() {
            return fieldInfos.stream();
        }
    }

    private class NativeImageDebugHeaderFieldInfo implements DebugFieldInfo {
        private final String name;
        private final String ownerType;
        private final String valueType;
        private final int offset;
        private final int size;
        private final int modifiers;

        NativeImageDebugHeaderFieldInfo(String name, String ownerType, String valueType, int offset, int size) {
            this.name = name;
            this.ownerType = ownerType;
            this.valueType = valueType;
            this.offset = offset;
            this.size = size;
            this.modifiers = Modifier.PUBLIC;
        }

        @Override
        public String name() {
            return name;
        }

        @Override
        public String ownerType() {
            return ownerType;
        }

        @Override
        public String valueType() {
            return valueType;
        }

        @Override
        public int offset() {
            return offset;
        }

        @Override
        public int size() {
            return size;
        }

        @Override
        public int modifiers() {
            return modifiers;
        }

        @Override
        public String fileName() {
            return "";
        }

        @Override
        public Path filePath() {
            return null;
        }

        @Override
        public Path cachePath() {
            return null;
        }
    }

    private Stream<DebugTypeInfo> computeHeaderTypeInfo() {
        List<DebugTypeInfo> infos = new LinkedList<>();
        int hubOffset = getObjectLayout().getHubOffset();
        int hubFieldSize = referenceSize;
        String hubTypeName = "java.lang.Class";
        int idHashOffset = getObjectLayout().getIdentityHashCodeOffset();
        int idHashSize = getObjectLayout().sizeInBytes(JavaKind.Int);
        int objHeaderSize = getObjectLayout().getMinimumInstanceObjectSize();

        /* We need array headers for all Java kinds */

        NativeImageHeaderTypeInfo objHeader = new NativeImageHeaderTypeInfo("_objhdr", objHeaderSize);
        objHeader.addField("hub", hubTypeName, hubOffset, hubFieldSize);
        if (idHashOffset > 0) {
            objHeader.addField("idHash", "int", idHashOffset, idHashSize);
        }
        infos.add(objHeader);

        return infos.stream();
    }

    private class NativeImageDebugEnumTypeInfo extends NativeImageDebugInstanceTypeInfo implements DebugEnumTypeInfo {

        NativeImageDebugEnumTypeInfo(HostedInstanceClass enumClass) {
            super(enumClass);
        }

        @Override
        public DebugTypeKind typeKind() {
            return DebugTypeKind.ENUM;
        }
    }

    private class NativeImageDebugInstanceTypeInfo extends NativeImageDebugTypeInfo implements DebugInstanceTypeInfo {
        NativeImageDebugInstanceTypeInfo(HostedType hostedType) {
            super(hostedType);
        }

        @Override
        public DebugTypeKind typeKind() {
            return DebugTypeKind.INSTANCE;
        }

        @Override
        public int headerSize() {
            return getObjectLayout().getFirstFieldOffset();
        }

        @Override
        public Stream<DebugFieldInfo> fieldInfoProvider() {
            Stream<DebugFieldInfo> instanceFieldsStream = Arrays.stream(hostedType.getInstanceFields(false)).map(this::createDebugFieldInfo);
            if (hostedType instanceof HostedInstanceClass && hostedType.getStaticFields().length > 0) {
                Stream<DebugFieldInfo> staticFieldsStream = Arrays.stream(hostedType.getStaticFields()).map(this::createDebugStaticFieldInfo);
                return Stream.concat(instanceFieldsStream, staticFieldsStream);
            } else {
                return instanceFieldsStream;
            }
        }

        @Override
        public Stream<DebugMethodInfo> methodInfoProvider() {
            return Arrays.stream(hostedType.getAllDeclaredMethods()).map(this::createDebugMethodInfo);
        }

        @Override
        public String superName() {
            HostedClass superClass = hostedType.getSuperclass();
            /*
             * HostedType wraps an AnalysisType and both HostedType and AnalysisType punt calls to
             * getSourceFilename to the wrapped class so for consistency we need to do the path
             * lookup relative to the doubly unwrapped HostedType.
             */
            if (superClass != null) {
                return getDeclaringClass(superClass, true).toJavaName();
            }
            return null;
        }

        @Override
        public Stream<String> interfaces() {
            return Arrays.stream(hostedType.getInterfaces()).map(this::toJavaName);
        }

        @Override
        public String enclosingClassName() {
            ResolvedJavaType enclosngType = hostedType.getEnclosingType();
            if (enclosngType != null) {
                return toJavaName(hostedType);
            }
            return null;
        }

        @Override
        public int modifiers() {
            return hostedType.getModifiers();
        }

        protected NativeImageDebugFieldInfo createDebugFieldInfo(HostedField field) {
            return new NativeImageDebugFieldInfo(field);
        }

        protected NativeImageDebugFieldInfo createDebugStaticFieldInfo(ResolvedJavaField field) {
            return new NativeImageDebugFieldInfo((HostedField) field);
        }

        protected NativeImageDebugMethodInfo createDebugMethodInfo(HostedMethod method) {
            return new NativeImageDebugMethodInfo(method);
        }

        protected class NativeImageDebugFieldInfo extends NativeImageDebugFileInfo implements DebugFieldInfo {
            private final HostedField field;

            NativeImageDebugFieldInfo(HostedField field) {
                super(field);
                this.field = field;
            }

            @Override
            public String name() {
                return field.getName();
            }

            @Override
            public String ownerType() {
                return typeName();
            }

            @Override
            public String valueType() {
                HostedType valueType = field.getType();
                return toJavaName(valueType);
            }

            @Override
            public int offset() {
                int offset = field.getLocation();
                /*
                 * For static fields we need to add in the appropriate partition base but only if we
                 * have a real offset
                 */
                if (isStatic() && offset >= 0) {
                    if (isPrimitive()) {
                        offset += primitiveStartOffset;
                    } else {
                        offset += referenceStartOffset;
                    }
                }
                return offset;
            }

            @Override
            public int size() {
                return getObjectLayout().sizeInBytes(field.getType().getStorageKind());
            }

            @Override
            public int modifiers() {
                return field.getModifiers();
            }

            private boolean isStatic() {
                return Modifier.isStatic(modifiers());
            }

            private boolean isPrimitive() {
                return field.getType().getStorageKind().isPrimitive();
            }
        }

        protected class NativeImageDebugMethodInfo extends NativeImageDebugFileInfo implements DebugMethodInfo {
            private final HostedMethod hostedMethod;

            NativeImageDebugMethodInfo(HostedMethod hostedMethod) {
                super(hostedMethod);
                this.hostedMethod = hostedMethod;
            }

            @Override
            public String name() {
                String name = hostedMethod.format("%n");
                if ("<init>".equals(name)) {
                    name = getDeclaringClass(hostedMethod, true).toJavaName();
                    if (name.indexOf('.') >= 0) {
                        name = name.substring(name.lastIndexOf('.') + 1);
                    }
                    if (name.indexOf('$') >= 0) {
                        name = name.substring(name.lastIndexOf('$') + 1);
                    }
                }
                return name;
            }

            @Override
            public String ownerType() {
                return typeName();
            }

            @Override
            public String valueType() {
                return hostedMethod.getSignature().getReturnType(null).toJavaName();
            }

            @Override
            public String paramSignature() {
                return hostedMethod.format("%P");
            }

            @Override
            public List<String> paramTypes() {
                return getParamTypes(hostedMethod);
            }

            @Override
            public List<String> paramNames() {
                return getParamNames(hostedMethod);
            }

            @Override
            public String symbolNameForMethod() {
                return NativeImage.localSymbolNameForMethod(hostedMethod);
            }

            @Override
            public boolean isDeoptTarget() {
                return hostedMethod.isDeoptTarget();
            }

            @Override
            public int modifiers() {
                return hostedMethod.getModifiers();
            }
        }
    }

    private class NativeImageDebugInterfaceTypeInfo extends NativeImageDebugInstanceTypeInfo implements DebugInterfaceTypeInfo {

        NativeImageDebugInterfaceTypeInfo(HostedInterface interfaceClass) {
            super(interfaceClass);
        }

        @Override
        public DebugTypeKind typeKind() {
            return DebugTypeKind.INTERFACE;
        }
    }

    private class NativeImageDebugArrayTypeInfo extends NativeImageDebugTypeInfo implements DebugArrayTypeInfo {
        HostedArrayClass arrayClass;
        List<DebugFieldInfo> fieldInfos;

        NativeImageDebugArrayTypeInfo(HostedArrayClass arrayClass) {
            super(arrayClass);
            this.arrayClass = arrayClass;
            this.fieldInfos = new LinkedList<>();
            JavaKind arrayKind = arrayClass.getBaseType().getJavaKind();
            int headerSize = getObjectLayout().getArrayBaseOffset(arrayKind);
            int arrayLengthOffset = getObjectLayout().getArrayLengthOffset();
            int arrayLengthSize = getObjectLayout().sizeInBytes(JavaKind.Int);
            assert arrayLengthOffset + arrayLengthSize <= headerSize;

            addField("len", "int", arrayLengthOffset, arrayLengthSize);
        }

        void addField(String name, String valueType, int offset, @SuppressWarnings("hiding") int size) {
            NativeImageDebugHeaderFieldInfo fieldinfo = new NativeImageDebugHeaderFieldInfo(name, typeName(), valueType, offset, size);
            fieldInfos.add(fieldinfo);
        }

        @Override
        public DebugTypeKind typeKind() {
            return DebugTypeKind.ARRAY;
        }

        @Override
        public int baseSize() {
            return getObjectLayout().getArrayBaseOffset(arrayClass.getComponentType().getStorageKind());
        }

        @Override
        public int lengthOffset() {
            return getObjectLayout().getArrayLengthOffset();
        }

        @Override
        public String elementType() {
            HostedType elementType = arrayClass.getComponentType();
            return toJavaName(elementType);
        }

        @Override
        public Stream<DebugFieldInfo> fieldInfoProvider() {
            return fieldInfos.stream();
        }
    }

    private class NativeImageDebugPrimitiveTypeInfo extends NativeImageDebugTypeInfo implements DebugPrimitiveTypeInfo {
        private final HostedPrimitiveType primitiveType;

        NativeImageDebugPrimitiveTypeInfo(HostedPrimitiveType primitiveType) {
            super(primitiveType);
            this.primitiveType = primitiveType;
        }

        @Override
        public DebugTypeKind typeKind() {
            return DebugTypeKind.PRIMITIVE;
        }

        @Override
        public int bitCount() {
            JavaKind javaKind = primitiveType.getStorageKind();
            return (javaKind == JavaKind.Void ? 0 : javaKind.getBitCount());
        }

        @Override
        public char typeChar() {
            return primitiveType.getStorageKind().getTypeChar();
        }

        @Override
        public int flags() {
            char typeChar = primitiveType.getStorageKind().getTypeChar();
            switch (typeChar) {
                case 'B':
                case 'S':
                case 'I':
                case 'J': {
                    return FLAG_NUMERIC | FLAG_INTEGRAL | FLAG_SIGNED;
                }
                case 'C': {
                    return FLAG_NUMERIC | FLAG_INTEGRAL;
                }
                case 'F':
                case 'D': {
                    return FLAG_NUMERIC;
                }
                default: {
                    assert typeChar == 'V' || typeChar == 'Z';
                    return 0;
                }
            }
        }
    }

    private NativeImageDebugTypeInfo createDebugTypeInfo(HostedType hostedType) {
        if (hostedType.isEnum()) {
            return new NativeImageDebugEnumTypeInfo((HostedInstanceClass) hostedType);
        } else if (hostedType.isInstanceClass()) {
            return new NativeImageDebugInstanceTypeInfo(hostedType);
        } else if (hostedType.isInterface()) {
            return new NativeImageDebugInterfaceTypeInfo((HostedInterface) hostedType);
        } else if (hostedType.isArray()) {
            return new NativeImageDebugArrayTypeInfo((HostedArrayClass) hostedType);
        } else if (hostedType.isPrimitive()) {
            return new NativeImageDebugPrimitiveTypeInfo((HostedPrimitiveType) hostedType);
        } else {
            throw new RuntimeException("Unknown type kind " + hostedType.getName());
        }
    }

    /**
     * Implementation of the DebugCodeInfo API interface that allows code info to be passed to an
     * ObjectFile when generation of debug info is enabled.
     */
    private class NativeImageDebugCodeInfo extends NativeImageDebugFileInfo implements DebugCodeInfo {
        private final HostedMethod hostedMethod;
        private final CompilationResult compilation;

        NativeImageDebugCodeInfo(HostedMethod method, CompilationResult compilation) {
            super(method);
            this.hostedMethod = method;
            this.compilation = compilation;
        }

        @SuppressWarnings("try")
        @Override
        public void debugContext(Consumer<DebugContext> action) {
            try (DebugContext.Scope s = debugContext.scope("DebugCodeInfo", hostedMethod)) {
                action.accept(debugContext);
            } catch (Throwable e) {
                throw debugContext.handle(e);
            }
        }

        @Override
        public String ownerType() {
            return getDeclaringClass(hostedMethod, true).toJavaName();
        }

        @Override
        public String name() {
            ResolvedJavaMethod targetMethod = hostedMethod.getWrapped().getWrapped();
            if (targetMethod instanceof SubstitutionMethod) {
                targetMethod = ((SubstitutionMethod) targetMethod).getOriginal();
            } else if (targetMethod instanceof CustomSubstitutionMethod) {
                targetMethod = ((CustomSubstitutionMethod) targetMethod).getOriginal();
            }
            String name = targetMethod.getName();
            if (name.equals("<init>")) {
                name = getDeclaringClass(hostedMethod, true).toJavaName();
                if (name.indexOf('.') >= 0) {
                    name = name.substring(name.lastIndexOf('.') + 1);
                }
                if (name.indexOf('$') >= 0) {
                    name = name.substring(name.lastIndexOf('$') + 1);
                }
            }
            return name;
        }

        @Override
        public String symbolNameForMethod() {
            return NativeImage.localSymbolNameForMethod(hostedMethod);
        }

        @Override
        public String paramSignature() {
            return hostedMethod.format("%P");
        }

        @Override
        public String valueType() {
            return hostedMethod.format("%R");
        }

        @Override
        public int addressLo() {
            return hostedMethod.getCodeAddressOffset();
        }

        @Override
        public int addressHi() {
            return hostedMethod.getCodeAddressOffset() + compilation.getTargetCodeSize();
        }

        @Override
        public int line() {
            LineNumberTable lineNumberTable = hostedMethod.getLineNumberTable();
            if (lineNumberTable != null) {
                return lineNumberTable.getLineNumber(0);
            }
            return -1;
        }

        @Override
        public Stream<DebugLineInfo> lineInfoProvider() {
            if (fileName().length() == 0) {
                return Stream.empty();
            }
            return compilation.getSourceMappings().stream()
                            .filter(NativeImageDebugInfoProvider::filterLineInfoSourceMapping)
                            .map(sourceMapping -> new NativeImageDebugLineInfo(sourceMapping));
        }

        @Override
        public int getFrameSize() {
            return compilation.getTotalFrameSize();
        }

        @Override
        public List<DebugFrameSizeChange> getFrameSizeChanges() {
            List<DebugFrameSizeChange> frameSizeChanges = new LinkedList<>();
            for (CompilationResult.CodeMark mark : compilation.getMarks()) {
                /* We only need to observe stack increment or decrement points. */
                if (mark.id.equals(SubstrateBackend.SubstrateMarkId.PROLOGUE_DECD_RSP)) {
                    NativeImageDebugFrameSizeChange sizeChange = new NativeImageDebugFrameSizeChange(mark.pcOffset, EXTEND);
                    frameSizeChanges.add(sizeChange);
                    // } else if (mark.id.equals("PROLOGUE_END")) {
                    // can ignore these
                    // } else if (mark.id.equals("EPILOGUE_START")) {
                    // can ignore these
                } else if (mark.id.equals(SubstrateBackend.SubstrateMarkId.EPILOGUE_INCD_RSP)) {
                    NativeImageDebugFrameSizeChange sizeChange = new NativeImageDebugFrameSizeChange(mark.pcOffset, CONTRACT);
                    frameSizeChanges.add(sizeChange);
                } else if (mark.id.equals(SubstrateBackend.SubstrateMarkId.EPILOGUE_END) && mark.pcOffset < compilation.getTargetCodeSize()) {
                    /* There is code after this return point so notify a stack extend again. */
                    NativeImageDebugFrameSizeChange sizeChange = new NativeImageDebugFrameSizeChange(mark.pcOffset, EXTEND);
                    frameSizeChanges.add(sizeChange);
                }
            }
            return frameSizeChanges;
        }

        @Override
        public boolean isDeoptTarget() {
            return hostedMethod.isDeoptTarget();
        }

        @Override
        public List<String> paramTypes() {
            return getParamTypes(hostedMethod);
        }

        @Override
        public List<String> paramNames() {
            return getParamNames(hostedMethod);
        }

        @Override
        public int modifiers() {
            return hostedMethod.getModifiers();
        }

        public String infoDump() {
            StringBuilder builder = new StringBuilder();
            dumpMethodInfo(builder);
            dumpFrames(builder);
            dumpSourceMappings(builder);
            dumpInfoPoints(builder);
            return builder.toString();
        }

        public void dumpMethodInfo(StringBuilder builder) {
            builder.append("method : ");
            methodName(builder, hostedMethod);
            builder.append("\n");
        }

        public void dumpFrames(StringBuilder builder) {
            builder.append("Frame : size=");
            hex(builder, compilation.getTotalFrameSize());
            builder.append(" {");
            String prefix = "\n";
            int codeSize = compilation.getTargetCodeSize();
            for (CompilationResult.CodeMark mark : compilation.getMarks()) {
                int pc = mark.pcOffset;
                if (mark.id.equals(SubstrateBackend.SubstrateMarkId.PROLOGUE_DECD_RSP)) {
                    builder.append(prefix);
                    builder.append("  pc : ");
                    hex(builder, pc);
                    builder.append(" stack_extend");
                    prefix = ",\n";
                } else if (mark.id.equals(SubstrateBackend.SubstrateMarkId.PROLOGUE_END)) {
                    builder.append(prefix);
                    builder.append("  pc : ");
                    hex(builder, pc);
                    builder.append(" prologue_end");
                    prefix = ",\n";
                } else if (mark.id.equals(SubstrateBackend.SubstrateMarkId.EPILOGUE_START)) {
                    builder.append(prefix);
                    builder.append("  pc : ");
                    hex(builder, pc);
                    builder.append(" epilogue_start");
                    prefix = ",\n";
                } else if (mark.id.equals(SubstrateBackend.SubstrateMarkId.EPILOGUE_INCD_RSP)) {
                    builder.append(prefix);
                    builder.append("  pc : ");
                    hex(builder, pc);
                    builder.append(" stack_contract");
                    prefix = ",\n";
                } else if (mark.id.equals(SubstrateBackend.SubstrateMarkId.EPILOGUE_END)) {
                    if (pc < codeSize) {
                        builder.append(prefix);
                        builder.append("  pc : ");
                        hex(builder, pc);
                        builder.append(" epilogue_end+stack_extend");
                        prefix = ",\n";
                    } else {
                        builder.append(prefix);
                        builder.append("  pc : ");
                        hex(builder, pc);
                        builder.append(" epilogue_end");
                        prefix = ",\n";
                    }
                }
            }
            if (!prefix.equals("\n")) {
                builder.append(prefix);
            } else {
                builder.append(" ");
            }
            builder.append("}\n");
        }

        public void dumpSourceMappings(StringBuilder builder) {
            builder.append("Source Mappings : ");
            builder.append(" {");
            String prefix = "\n";
            for (SourceMapping sourceMapping: compilation.getSourceMappings()) {
                int pc = sourceMapping.getStartOffset();
                int pcend = sourceMapping.getEndOffset();
                builder.append(prefix);
                builder.append("  pc : [");
                hex(builder, pc);
                builder.append(", ");
                hex(builder, pcend);
                builder.append("] {");
                NodeSourcePosition sourcePos = sourceMapping.getSourcePosition();
                callChain(builder, sourcePos);
                builder.append(" }");
                prefix = ",\n";
            }
            if (!prefix.equals("\n")) {
                builder.append(prefix);
            } else {
                builder.append(" ");
            }
            builder.append("}\n");
        }

        public void dumpInfoPoints(StringBuilder builder) {
            builder.append("Info Points : ");
            builder.append(" {");
            String prefix = "\n";
            for (Infopoint infopoint: compilation.getInfopoints()) {
                builder.append(prefix);
                infopoint(builder, infopoint);
                prefix = ",\n";
            }
            if (prefix.equals("\n")) {
                builder.append(" ");
            } else {
                builder.append("\n");
            }
            builder.append("}\n");
        }

        public void callChain(StringBuilder builder, NodeSourcePosition sourcePos) {
            NodeSourcePosition nextPos = sourcePos;
            String prefix = "";
            int i = 0;
            while (nextPos != null) {
                builder.append(prefix);
                builder.append("\n    ");
                builder.append(i++);
                builder.append(": ");
                ResolvedJavaMethod method = nextPos.getMethod();
                methodName(builder, method);
                lineOrBCI(builder, method, nextPos.getBCI());
                marker(builder, nextPos);
                nextPos = nextPos.getCaller();
            }
        }

        public void methodName(StringBuilder builder, ResolvedJavaMethod method) {
            builder.append(method.getDeclaringClass().toJavaName());
            builder.append("::");
            builder.append(method.getName());
            builder.append(method.getSignature().toMethodDescriptor());
        }

        public void lineOrBCI(StringBuilder builder, ResolvedJavaMethod method, int bci) {
            if (bci > 0) {
                int line = -1;
                LineNumberTable lineNumberTable = method.getLineNumberTable();
                if (lineNumberTable != null) {
                    line = lineNumberTable.getLineNumber(bci);
                }
                if (line >= 0) {
                    builder.append(" line ");
                    builder.append(line);
                }
                builder.append(" bci ");
                builder.append(bci);
            }
        }

        public void marker(StringBuilder builder, NodeSourcePosition nodeSourcePosition) {
            if (nodeSourcePosition.isSubstitution()) {
                builder.append(" Substitution ");
            } else if (nodeSourcePosition.isPlaceholder()) {
                builder.append(" Placeholder ");
            }
        }

        public void infopoint(StringBuilder builder, Infopoint infopoint) {
            int pc = infopoint.pcOffset;
            DebugInfo debuginfo = infopoint.debugInfo;
            InfopointReason reason = infopoint.reason;
            builder.append("  pc : ");
            hex(builder, pc);
            infopointReason(builder, reason);
            if (infopoint.reason == InfopointReason.CALL) {
                Call call = (Call)infopoint;
                if (call.target instanceof ResolvedJavaMethod) {
                    methodName(builder, (ResolvedJavaMethod) call.target);
                } else {
                    builder.append(call.target);
                }
            }
            if (debuginfo != null) {
                builder.append("\n  Debuginfo {\n    "  );
                BytecodePosition bytecodePosition = debuginfo.getBytecodePosition();
                ResolvedJavaMethod method = bytecodePosition.getMethod();
                methodName(builder, method);
                lineOrBCI(builder, method, bytecodePosition.getBCI());
                BytecodeFrame frame = debuginfo.frame();
                String prefix = "\n";
                if (frame != null) {
                    builder.append(prefix);
                    frameStack(builder, frame);
                    prefix = ",\n";
                }
                if (prefix == "\n") {
                    builder.append(" }");
                } else {
                    builder.append("\n  }");
                }
            } else {
                builder.append("\n  No Debuginfo");
            }
        }

        public void frameStack(StringBuilder builder,  BytecodeFrame frame) {
            builder.append("    frames {");
            BytecodePosition next = frame;
            String prefix = "\n      ";
            while (next != null) {
                builder.append(prefix);
                bytecodePosition(builder, next);
                next = next.getCaller();
                prefix = ",\n      ";
            }
            if (prefix.equals("\n      ")) {
                builder.append(" }");
            } else {
                builder.append("\n    }");
            }
        }


        public void bytecodePosition(StringBuilder builder,  BytecodePosition pos) {
            builder.append("at ");
            ResolvedJavaMethod method = pos.getMethod();
            methodName(builder, method);
            lineOrBCI(builder, method, pos.getBCI());
            if (pos instanceof BytecodeFrame) {
                bytecodeFrame(builder, (BytecodeFrame) pos);
            }
        }

        public void bytecodeFrame(StringBuilder builder,  BytecodeFrame frame) {
            if (frame.duringCall) {
                builder.append(" during call");
            }
            int numLocals = frame.numLocals;
            ResolvedJavaMethod method = frame.getMethod();
            LocalVariableTable localTable = method.getLocalVariableTable();
            if (numLocals == 0) {
                builder.append("\n      locals: { }");
            } else {
                builder.append("\n      locals: {");
                for (int i = 0; i < numLocals; i++) {
                    builder.append("\n        ");
                    local(builder, localTable, frame.getBCI(), i, frame.getLocalValue(i), frame.getLocalValueKind(i));
                }
                builder.append("\n      }");
            }
        }

        public void local(StringBuilder builder, LocalVariableTable localTable, int bci, int slot, JavaValue value, JavaKind kind) {
            builder.append(slot);
            builder.append(": ");
            Local local = (localTable != null ? localTable.getLocal(slot, bci) : null);
            if (local != null) {
                builder.append(local.getName());
                builder.append(":");
                builder.append(local.getType().toJavaName());
            } else {
                builder.append("__");

            }
            builder.append(" = ");
            if (kind == JavaKind.Illegal) {
                builder.append("<undefined>");
            } else if (value instanceof JavaConstant) {
                builder.append("const ");
                if (value instanceof DirectSubstrateObjectConstant &&
                        ((DirectSubstrateObjectConstant)value).getObject() instanceof String) {
                    builder.append("\"");
                    builder.append(((JavaConstant) value).toValueString());
                    builder.append("\"");
                } else {
                    builder.append(((JavaConstant) value).toValueString());
                }
            } else {
                builder.append(value);
                builder.append(" kind ");
                builder.append(kind);
            }
        }

        public void infopointReason(StringBuilder builder, InfopointReason reason) {
            builder.append(" reason_");
            switch (reason) {
                case SAFEPOINT:
                    builder.append("safepoint ");
                    break;
                case CALL:
                    builder.append("call ");
                    break;
                case IMPLICIT_EXCEPTION:
                    builder.append("implicit_exception ");
                    break;
                case METHOD_START:
                    builder.append("start ");
                    break;
                case METHOD_END:
                    builder.append("end ");
                    break;
                case BYTECODE_POSITION:
                    builder.append("bytecode_pos ");
                    break;
                default:
                    builder.append("none ");
                    break;
            }
        }

        public void hex(StringBuilder builder, int i) {
            builder.append("0x");
            builder.append(Integer.toHexString(i));
        }
    }
    private static boolean filterLineInfoSourceMapping(SourceMapping sourceMapping) {
        if (!SubstrateOptions.OmitInlinedMethodDebugLineInfo.getValue()) {
            return true;
        }
        return sourceMapping.getSourcePosition().getCaller() == null;
    }

    /**
     * Implementation of the DebugLineInfo API interface that allows line number info to be passed
     * to an ObjectFile when generation of debug info is enabled.
     */
    private class NativeImageDebugLineInfo implements DebugLineInfo {
        private final int bci;
        private final ResolvedJavaMethod method;
        private final int lo;
        private final int hi;
        private Path cachePath;
        private Path fullFilePath;

        NativeImageDebugLineInfo(SourceMapping sourceMapping) {
            NodeSourcePosition position = sourceMapping.getSourcePosition();
            int posbci = position.getBCI();
            this.bci = (posbci >= 0 ? posbci : 0);
            this.method = position.getMethod();
            this.lo = sourceMapping.getStartOffset();
            this.hi = sourceMapping.getEndOffset();
            this.cachePath = SubstrateOptions.getDebugInfoSourceCacheRoot();
            computeFullFilePath();
        }

        @Override
        public String fileName() {
            if (fullFilePath != null) {
                Path fileName = fullFilePath.getFileName();
                if (fileName != null) {
                    return fileName.toString();
                }
            }
            return null;
        }

        @Override
        public Path filePath() {
            if (fullFilePath != null) {
                return fullFilePath.getParent();
            }
            return null;
        }

        @Override
        public Path cachePath() {
            return cachePath;
        }

        @Override
        public String ownerType() {
            if (method instanceof HostedMethod) {
                return getDeclaringClass((HostedMethod) method, true).toJavaName();
            } else {
                return method.getDeclaringClass().toJavaName();
            }
        }

        @Override
        public String name() {
            ResolvedJavaMethod targetMethod = method;
            while (targetMethod instanceof WrappedJavaMethod) {
                targetMethod = ((WrappedJavaMethod) targetMethod).getWrapped();
            }
            if (targetMethod instanceof SubstitutionMethod) {
                targetMethod = ((SubstitutionMethod) targetMethod).getOriginal();
            } else if (targetMethod instanceof CustomSubstitutionMethod) {
                targetMethod = ((CustomSubstitutionMethod) targetMethod).getOriginal();
            }
            String name = targetMethod.getName();
            if (name.equals("<init>")) {
                if (method instanceof HostedMethod) {
                    name = getDeclaringClass((HostedMethod) method, true).toJavaName();
                    if (name.indexOf('.') >= 0) {
                        name = name.substring(name.lastIndexOf('.') + 1);
                    }
                    if (name.indexOf('$') >= 0) {
                        name = name.substring(name.lastIndexOf('$') + 1);
                    }
                } else {
                    name = targetMethod.format("%h");
                    if (name.indexOf('$') >= 0) {
                        name = name.substring(name.lastIndexOf('$') + 1);
                    }
                }
            }
            return name;
        }

        @Override
        public String valueType() {
            return method.format("%R");
        }

        @Override
        public String paramSignature() {
            return method.format("%P");
        }

        @Override
        public String symbolNameForMethod() {
            return NativeImage.localSymbolNameForMethod(method);
        }

        @Override
        public boolean isDeoptTarget() {
            if (method instanceof HostedMethod) {
                return ((HostedMethod) method).isDeoptTarget();
            }
            return name().endsWith(HostedMethod.METHOD_NAME_DEOPT_SUFFIX);
        }

        @Override
        public int addressLo() {
            return lo;
        }

        @Override
        public int addressHi() {
            return hi;
        }

        @Override
        public int line() {
            LineNumberTable lineNumberTable = method.getLineNumberTable();
            if (lineNumberTable != null) {
                return lineNumberTable.getLineNumber(bci);
            }
            return -1;
        }

        @Override
        public List<String> paramTypes() {
            Signature signature = method.getSignature();
            int parameterCount = signature.getParameterCount(false);
            List<String> paramTypes = new ArrayList<>(parameterCount);
            for (int i = 0; i < parameterCount; i++) {
                JavaType parameterType = signature.getParameterType(i, null);
                paramTypes.add(toJavaName(parameterType));
            }
            return paramTypes;
        }

        @Override
        public List<String> paramNames() {
            return getParamNames(method);
        }

        @Override
        public int modifiers() {
            return method.getModifiers();
        }

        @SuppressWarnings("try")
        private void computeFullFilePath() {
            ResolvedJavaType declaringClass;
            // if we have a HostedMethod then deal with substitutions
            if (method instanceof HostedMethod) {
                declaringClass = getDeclaringClass((HostedMethod) method, false);
            } else {
                declaringClass = method.getDeclaringClass();
            }
            Class<?> clazz = null;
            if (declaringClass instanceof OriginalClassProvider) {
                clazz = ((OriginalClassProvider) declaringClass).getJavaClass();
            }
            SourceManager sourceManager = ImageSingletons.lookup(SourceManager.class);
            try (DebugContext.Scope s = debugContext.scope("DebugCodeInfo", declaringClass)) {
                fullFilePath = sourceManager.findAndCacheSource(declaringClass, clazz, debugContext);
            } catch (Throwable e) {
                throw debugContext.handle(e);
            }
        }

    }

    /**
     * Implementation of the DebugFrameSizeChange API interface that allows stack frame size change
     * info to be passed to an ObjectFile when generation of debug info is enabled.
     */
    private class NativeImageDebugFrameSizeChange implements DebugFrameSizeChange {
        private int offset;
        private Type type;

        NativeImageDebugFrameSizeChange(int offset, Type type) {
            this.offset = offset;
            this.type = type;
        }

        @Override
        public int getOffset() {
            return offset;
        }

        @Override
        public Type getType() {
            return type;
        }
    }

    private class NativeImageDebugDataInfo implements DebugDataInfo {
        HostedClass hostedClass;
        ImageHeapPartition partition;
        long offset;
        long address;
        long size;
        String typeName;
        String provenance;

        @SuppressWarnings("try")
        @Override
        public void debugContext(Consumer<DebugContext> action) {
            try (DebugContext.Scope s = debugContext.scope("DebugCodeInfo", provenance)) {
                action.accept(debugContext);
            } catch (Throwable e) {
                throw debugContext.handle(e);
            }
        }

        NativeImageDebugDataInfo(ObjectInfo objectInfo) {
            hostedClass = objectInfo.getClazz();
            partition = objectInfo.getPartition();
            offset = objectInfo.getOffset();
            address = objectInfo.getAddress();
            size = objectInfo.getSize();
            provenance = objectInfo.toString();
            typeName = hostedClass.toJavaName();
        }

        /* Accessors. */
        @Override
        public String getProvenance() {
            return provenance;
        }

        @Override
        public String getTypeName() {
            return typeName;
        }

        @Override
        public String getPartition() {
            return partition.getName() + "{" + partition.getSize() + "}@" + partition.getStartOffset();
        }

        @Override
        public long getOffset() {
            return offset;
        }

        @Override
        public long getAddress() {
            return address;
        }

        @Override
        public long getSize() {
            return size;
        }
    }

    private boolean acceptObjectInfo(ObjectInfo objectInfo) {
        /* This condiiton rejects filler partition objects. */
        return (objectInfo.getPartition().getStartOffset() > 0);
    }

    private DebugDataInfo createDebugDataInfo(ObjectInfo objectInfo) {
        return new NativeImageDebugDataInfo(objectInfo);
    }
}
