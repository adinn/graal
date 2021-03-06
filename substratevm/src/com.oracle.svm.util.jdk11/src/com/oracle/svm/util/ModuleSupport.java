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
package com.oracle.svm.util;

import java.io.IOException;
import java.io.InputStream;
import java.lang.module.ModuleFinder;
import java.lang.module.ModuleReader;
import java.lang.module.ModuleReference;
import java.lang.module.ResolvedModule;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Locale;
import java.util.MissingResourceException;
import java.util.NoSuchElementException;
import java.util.Optional;
import java.util.ResourceBundle;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import jdk.internal.module.Modules;

public final class ModuleSupport {
    private ModuleSupport() {
    }

    public static ResourceBundle getResourceBundle(String bundleName, Locale locale, ClassLoader loader) {
        Class<?> bundleClass;
        try {
            bundleClass = loader.loadClass(bundleName);
        } catch (ClassNotFoundException ex) {
            return getResourceBundleFallback(bundleName, locale, loader);
        }
        /*
         * Open up module that contains the bundleClass so that ResourceBundle.getBundle can
         * succeed.
         */
        ModuleSupport.openModuleByClass(bundleClass, ModuleSupport.class);
        return ResourceBundle.getBundle(bundleName, locale, bundleClass.getModule());
    }

    private static ResourceBundle getResourceBundleFallback(String bundleName, Locale locale, ClassLoader loader) {
        /* Try looking through all modules to find a match. */
        Optional<String> packageName = packageName(bundleName);
        for (Module module : ModuleLayer.boot().modules()) {
            try {
                packageName.ifPresent(p -> {
                    if (module.getPackages().contains(p)) {
                        Modules.addExportsToAllUnnamed(module, p);
                        Modules.addOpensToAllUnnamed(module, p);
                    }
                });
                return ResourceBundle.getBundle(bundleName, locale, module);
            } catch (MissingResourceException e2) {
                /* Continue the loop. */
            }
        }

        /*
         * This call will most likely throw an exception because it will also not find the bundle
         * class. But it avoids special and JDK-specific handling here.
         */
        return ResourceBundle.getBundle(bundleName, locale, loader);
    }

    /**
     * If the bundle is specified via java.class or java.properties format extract the package from
     * the name.
     */
    private static Optional<String> packageName(String bundleName) {
        int classSep = bundleName.replace('/', '.').lastIndexOf('.');
        if (classSep == -1) {
            /* The bundle is not specified via a java.class or java.properties format. */
            return Optional.empty();
        }
        return Optional.of(bundleName.substring(0, classSep));
    }

    public static boolean hasSystemModule(String moduleName) {
        return ModuleFinder.ofSystem().find(moduleName).isPresent();
    }

    public static List<String> getModuleResources(Collection<Path> modulePath) {
        ArrayList<String> result = new ArrayList<>();
        for (ModuleReference moduleReference : ModuleFinder.of(modulePath.toArray(Path[]::new)).findAll()) {
            try (ModuleReader moduleReader = moduleReference.open()) {
                result.addAll(moduleReader.list().collect(Collectors.toList()));
            } catch (IOException e) {
                throw new RuntimeException("Unable get list of resources in module" + moduleReference.descriptor().name(), e);
            }
        }
        return result;
    }

    public static List<String> getSystemModuleResources(Collection<String> names) {
        List<String> result = new ArrayList<>();
        for (String name : names) {
            Optional<ModuleReference> moduleReference = ModuleFinder.ofSystem().find(name);
            if (moduleReference.isEmpty()) {
                throw new RuntimeException("Unable find ModuleReference for module " + name);
            }
            try (ModuleReader moduleReader = moduleReference.get().open()) {
                result.addAll(moduleReader.list().collect(Collectors.toList()));
            } catch (IOException e) {
                throw new RuntimeException("Unable get list of resources in module" + name, e);
            }
        }
        return result;
    }

    public static void openModuleByClass(Class<?> declaringClass, Class<?> accessingClass) {
        Module declaringModule = declaringClass.getModule();
        String packageName = declaringClass.getPackageName();
        Module accessingModule = accessingClass == null ? null : accessingClass.getModule();
        if (accessingModule != null && accessingModule.isNamed()) {
            if (!declaringModule.isOpen(packageName, accessingModule)) {
                Modules.addOpens(declaringModule, packageName, accessingModule);
            }
        } else {
            Modules.addOpensToAllUnnamed(declaringModule, packageName);
        }
    }

    /**
     * Exports and opens a single package {@code packageName} in the module named {@code moduleName}
     * to all unnamed modules.
     */
    @SuppressWarnings("unused")
    public static void exportAndOpenPackageToClass(String moduleName, String packageName, boolean optional, Class<?> accessingClass) {
        Optional<Module> value = ModuleLayer.boot().findModule(moduleName);
        if (value.isEmpty()) {
            if (!optional) {
                throw new NoSuchElementException(moduleName);
            }
            return;
        }
        Module declaringModule = value.get();
        Module accessingModule = accessingClass == null ? null : accessingClass.getModule();
        if (accessingModule != null && accessingModule.isNamed()) {
            if (!declaringModule.isOpen(packageName, accessingModule)) {
                Modules.addOpens(declaringModule, packageName, accessingModule);
            }
        } else {
            Modules.addOpensToAllUnnamed(declaringModule, packageName);
        }

    }

    /**
     * Exports and opens all packages in the module named {@code name} to all unnamed modules.
     */
    @SuppressWarnings("unused")
    public static void exportAndOpenAllPackagesToUnnamed(String name, boolean optional) {
        Optional<Module> value = ModuleLayer.boot().findModule(name);
        if (value.isEmpty()) {
            if (!optional) {
                throw new NoSuchElementException("No module in boot layer named " + name + ". Available modules: " + ModuleLayer.boot());
            }
            return;
        }
        Module module = value.get();
        Set<String> packages = module.getPackages();
        for (String pkg : packages) {
            Modules.addExportsToAllUnnamed(module, pkg);
            Modules.addOpensToAllUnnamed(module, pkg);
        }
    }

    /**
     * Exports and opens a single package {@code pkg} in the module named {@code name} to all
     * unnamed modules.
     */
    @SuppressWarnings("unused")
    public static void exportAndOpenPackageToUnnamed(String name, String pkg, boolean optional) {
        Optional<Module> value = ModuleLayer.boot().findModule(name);
        if (value.isEmpty()) {
            if (!optional) {
                throw new NoSuchElementException(name);
            }
            return;
        }
        Module module = value.get();
        Modules.addExportsToAllUnnamed(module, pkg);
        Modules.addOpensToAllUnnamed(module, pkg);
    }

    public static String getModuleName(Class<?> clazz) {
        return clazz.getModule().getName();
    }

    /**
     * In the modules of the boot module layer, filters all resources that match the given
     * predicate, and calls the operation on the matched resources. This is a temporary solution
     * until we fully support modules in native-image
     *
     * @param resourceNameFilter predicate applied to all resource names in the module
     * @param operation a function to process matched resources, it receives the name of the
     *            resources as the first argument and an open stream as the second argument
     */
    @SuppressWarnings("unused")
    public static void findResourcesInModules(Predicate<String> resourceNameFilter, BiConsumer<String, InputStream> operation) throws IOException {
        for (ResolvedModule resolvedModule : ModuleLayer.boot().configuration().modules()) {
            ModuleReference modRef = resolvedModule.reference();
            try (ModuleReader moduleReader = modRef.open()) {
                final List<String> resources = moduleReader.list()
                                .filter(resourceNameFilter)
                                .collect(Collectors.toList());

                for (String resName : resources) {
                    Optional<InputStream> content = moduleReader.open(resName);
                    if (content.isEmpty()) {
                        continue;
                    }
                    InputStream is = content.get();
                    operation.accept(resName, is);
                    is.close();
                }
            }
        }
    }
}
