import gnu.trove.list.array.TByteArrayList;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintWriter;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import java.util.jar.JarInputStream;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.commons.AnalyzerAdapter;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LocalVariableNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TryCatchBlockNode;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.Multimap;


public class Main {
	
	// First: find all methods in minecraft.jar and merge groups (discovery phase)
	// Then: assign names to groups and write SRG (SRG phase)
	// Then: find exceptions thrown by each method (exception discovery phase)
	// Then: propagate exception declarations (exception propagation phase)
	// Then: write EXC (EXC phase)
	
	static List<File> findLibs(File dir) {
		List<File> rv = new ArrayList<>();
		
		if(!dir.isDirectory())
			throw new IllegalArgumentException(dir.getAbsolutePath()+" not a directory");
		
		for(String fn : dir.list()) {
			File sub = new File(dir, fn);
			if(sub.isDirectory())
				rv.addAll(findLibs(sub));
			else if(fn.endsWith(".jar"))
				rv.add(sub);
		}
		
		return rv;
	}
	
	static class ExceptionEntry {
		MethodDetails method;
		List<TryBlock> tryBlocks = new ArrayList<>();
	}
	
	static class TryBlock {
		Class<?> catches;
		boolean isReachable;
		MethodDetails method;
		TryCatchBlockNode node;
	}
	
	static class MethodDetails implements Comparable<MethodDetails> {
		MethodGroup group = new MethodGroup();
		
		Set<MethodDetails> allDerived = new HashSet<>();
		
		// used during exception discovery and propagation phase
		List<ExceptionEntry> exceptionsFrom = new ArrayList<>();
		List<ExceptionEntry> exceptionsTo = new ArrayList<>();
		Set<String> exceptions = new HashSet<>();

		final MethodIdentifier ident;
		public MethodDetails(MethodIdentifier ident) {
			this.ident = ident;
		}
		
		@Override
		public String toString() {
			return ident.toString();
		}

		@Override
		public int compareTo(MethodDetails o) {
			return ident.compareTo(o.ident);
		}
	}
	
	static class MethodGroup implements Comparable<MethodGroup> {
		// fields not used during discovery phase
		Set<MethodDetails> methods = new TreeSet<>();
		String srgName;
		
		@Override
		public int compareTo(MethodGroup o) {
			return methods.iterator().next().compareTo(o.methods.iterator().next());
		}
	}
	
	static class FieldIdentifier implements Comparable<FieldIdentifier> {
		public final String owner;
		public final String name;
		public final String desc;
		
		public FieldIdentifier(String owner, String name, String desc) {
			this.owner = owner;
			this.name = name;
			this.desc = desc;
		}
		
		@Override
		public int compareTo(FieldIdentifier arg0) {
			int i = owner.compareTo(arg0.owner);
			if(i != 0) return i;
			i = name.compareTo(arg0.name);
			if(i != 0) return i;
			return desc.compareTo(arg0.desc);
		}
	}
	
	static Set<FieldIdentifier> discoveredFields = new TreeSet<>();
	
	static Map<MethodIdentifier, MethodDetails> allMethods = new TreeMap<>();
	static Set<MethodIdentifier> discoveredMethods = new TreeSet<>();
	
	static void setGroup(MethodDetails m, MethodGroup g) {
		MethodGroup old = m.group;
		m.group = g;
		
		if(old != null)
			for(MethodDetails md : allMethods.values())
				if(md.group == old)
					md.group = g;
	}
	
	static void mergeGroup(MethodDetails m1, MethodDetails m2) {
		if(m1.group == null)
			m1.group = m2.group;
		else if(m2.group == null)
			m2.group = m1.group;
		else
			setGroup(m1, m2.group);
	}
	
	//private static Map<Class<?>, List<Class<?>>> superCache = new HashMap<>();
	static List<Class<?>> getAllSupers(Class c) {
		//if(superCache.containsKey(c))
		//	return superCache.get(c);
		List<Class<?>> rv = new ArrayList<>();
		if(c.getSuperclass() != null) {
			rv.add(c.getSuperclass());
			rv.addAll(getAllSupers(c.getSuperclass()));
		}
		for(Class i : c.getInterfaces()) {
			rv.add(i);
			rv.addAll(getAllSupers(i));
		}
		//superCache.put(c, rv);
		return rv;
	}
	
	static MethodDetails getMethod(MethodIdentifier ident) {
		MethodDetails md = allMethods.get(ident);
		if(md == null)
			allMethods.put(ident, md = new MethodDetails(ident));
		return md;
	}
	
	static void discoverMethod(Class c, Method m) {
		MethodIdentifier ident = new MethodIdentifier(c.getName(), m.getName(), Type.getMethodDescriptor(m));
		MethodDetails fm = getMethod(ident);
		
		discoveredMethods.add(ident);
		
		for(Class sc : getAllSupers(c)) {
			try {
				Method fromSuper = sc.getDeclaredMethod(m.getName(), m.getParameterTypes());
				MethodDetails fromSuperFM = getMethod(new MethodIdentifier(sc.getName(), m.getName(), Type.getMethodDescriptor(fromSuper)));
	
				mergeGroup(fromSuperFM, fm);
				
				fromSuperFM.allDerived.add(fm);
			} catch(NoSuchMethodException e) {
			}
		}
	}
	
	static void discoverMethod(Class c, Constructor m) {
		MethodIdentifier ident = new MethodIdentifier(c.getName(), "<init>", Type.getConstructorDescriptor(m));
		getMethod(ident);
		discoveredMethods.add(ident);
	}
	
	private static Map<String, String> knownClassDeobfNames = new HashMap<String, String>();
	
	private static void reportTime(long ns) {
		System.out.println((ns / 1000000)+"ms");
	}
	
	private static ClassLoader loader;
	
	public static void main(String[] args) throws Exception {
		File libdir = new File(args[0]);
		File mcfile = new File(args[1]);
		File confdir = new File(args[2]);
		String version = args[3];
		String side = args[4];
		
		System.out.println("Libraries: " + libdir);
		System.out.println("MC: " + mcfile);
		System.out.println("Conf: " + confdir);
		System.out.println("Version: " + version);
		System.out.println("Side: "+side);
		
		try (Scanner s = new Scanner(Main.class.getResourceAsStream("/" + version + ".txt"))){ 
			while(s.hasNextLine()) {
				String line = s.nextLine();
				String[] parts = line.split(" ");
				if(parts.length == 0 || parts[0].startsWith("#") || line.trim().equals(""))
					continue;
				knownClassDeobfNames.put(parts[0], parts[1]);
			}
		}
		
		List<File> libs = findLibs(libdir);
		
		libs.add(mcfile);
		
		List<URL> urls = new ArrayList<>(libs.size());
		for(File f : libs)
			urls.add(f.toURI().toURL());
		urls.add(mcfile.toURI().toURL());
		
		try (URLClassLoader loader = new URLClassLoader((URL[])urls.toArray(new URL[0]), null)) {
			Main.loader = loader;
			
			long t0 = System.nanoTime();
			
			System.out.print("Gathering class names...");
			
			List<String> classNames = getClassNames(mcfile);
			
			long t1 = System.nanoTime();
			reportTime(t1 - t0);
			
			System.out.print("Discovering methods in "+classNames.size()+" classes...");
			
			Map<FieldIdentifier, String> enumFields = new TreeMap<>();
			
			for(String name : classNames) {
				Class<?> c = loader.loadClass(name);
				
				for(Method m : c.getDeclaredMethods())
					discoverMethod(c, m);
				for(Constructor m : c.getDeclaredConstructors())
					discoverMethod(c, m);
				for(Field f : c.getDeclaredFields())
					discoveredFields.add(new FieldIdentifier(c.getName(), f.getName(), Type.getDescriptor(f.getType())));
				
				if(c.isEnum()) {
					Object[] constants = c.getEnumConstants();
					if(constants != null) {
						Set<Object> constantsSet = new HashSet<>(Arrays.asList(constants));
						for(Field f : c.getDeclaredFields()) {
							if(!c.isAssignableFrom(f.getType()))
								continue;
							
							final int needMods = Modifier.STATIC | Modifier.PUBLIC | Modifier.FINAL; 
							if((f.getModifiers() & needMods) != needMods)
								continue;
							
							f.setAccessible(true);
							
							Object value = f.get(null);
							if(!constantsSet.contains(value))
								continue;
							
							FieldIdentifier fi = new FieldIdentifier(c.getName(), f.getName(), Type.getDescriptor(f.getType()));
							
							enumFields.put(fi, ((Enum)value).name());
						}
					}
				}
				
				
				// this fixes the case where:
				//   interface I {public void X();}
				//   class C1 {public void X() {}}
				//   class C2 extends C1 implements I {}
				// but I.x and C1.x aren't merged
				for(Class i : c.getInterfaces())
					for(Class s : getAllSupers(c))
						for(Method m : i.getMethods()) {
							try {
								Method sm = s.getDeclaredMethod(m.getName(), m.getParameterTypes());
								MethodIdentifier im = new MethodIdentifier(i.getName(), m.getName(), Type.getMethodDescriptor(m));
								MethodIdentifier ism = new MethodIdentifier(s.getName(), sm.getName(), Type.getMethodDescriptor(sm));
								mergeGroup(getMethod(im), getMethod(ism));
							} catch(NoSuchMethodException e) {
							}
						}
			}
			
			long t2 = System.nanoTime();
			reportTime(t2 - t1);
			
			allMethods.keySet().retainAll(discoveredMethods);
			
			Set<MethodGroup> groups = new TreeSet<>();
			for(MethodDetails md : allMethods.values())
				md.group.methods.add(md);
			for(MethodDetails md : allMethods.values())
				groups.add(md.group);
			
			System.out.println(allMethods.size()+" methods discovered in "+groups.size()+" method groups");
			
			try (PrintWriter srg = new PrintWriter(new File(confdir, side+".srg"))) {
				
				srg.println("PK: . net/minecraft/src");
				srg.println("PK: net net");
				srg.println("PK: net/minecraft net/minecraft");
				srg.println("PK: net/minecraft/client net/minecraft/client");
				srg.println("PK: net/minecraft/client/main net/minecraft/client/main");
				srg.println("PK: net/minecraft/server net/minecraft/server");
				
				for(String s : classNames) {
					s = s.replace('.', '/');
					srg.println("CL: " + s + " " + deobfOwner(s));
				}
				
				MethodNameGenerator mng = new MethodNameGenerator();
				
				int nObfMG = 0;
				for(MethodGroup g : groups) {
					
					Set<MethodIdentifier> smi = new TreeSet<MethodIdentifier>();
					for(MethodDetails md : g.methods) smi.add(md.ident);
					g.srgName = mng.generateMethodName(smi, knownClassDeobfNames, loader);
					
					boolean obf = true;
					
					if(knownClassDeobfNames.containsKey(g.srgName))
						g.srgName = knownClassDeobfNames.get(g.srgName);
					
					for(MethodDetails fm : g.methods) {
						String owner = fm.ident.owner.replace('.', '/');
						if(fm.ident.name.length() > 2) {
							g.srgName = fm.ident.name;
							//System.out.println("MD: "+owner+"/"+fm.name+" "+fm.desc+" "+deobfOwner(owner)+"/"+srgName+" "+deobfDesc(fm.desc));
							obf = false;
						}
						
						srg.println("MD: "+owner+"/"+fm.ident.name+" "+fm.ident.desc+" "+deobfOwner(owner)+"/"+g.srgName+" "+deobfDesc(fm.ident.desc));
					}
					
					if(obf)
						nObfMG++;
				}
				System.out.println(nObfMG+" method groups are obfuscated");
				
				int nObfFields = 0;
				FieldNameGenerator fng = new FieldNameGenerator();
				for(FieldIdentifier f : discoveredFields) {
					if(f.name.length() <= 2 || enumFields.containsKey(f)) {
						String srgName;
						if(enumFields.containsKey(f))
							srgName = enumFields.get(f);
						else {
							srgName = fng.generateName(f.owner, f.name, f.desc, deobfOwner(f.owner));
							if(knownClassDeobfNames.containsKey(srgName)) {
								srgName = knownClassDeobfNames.get(srgName);
							}
						}
						srg.println("FD: "+f.owner+"/"+f.name+" "+deobfOwner(f.owner)+"/"+srgName);
						nObfFields++;
					}
				}
				System.out.println(nObfFields+" fields are obfuscated");
				System.out.println(enumFields.size()+" enum fields found");
			}
			
			System.out.println("SRG file written");
			
			
			
			
			
			long te0 = System.nanoTime();
			// Exception discovery
			System.out.println("Discovering exceptions from "+allMethods.size()+" methods");
			for(Map.Entry<MethodIdentifier, MethodDetails> e : allMethods.entrySet()) {
				//System.out.println(e.getKey());
				getExceptions(loader, e.getKey());
			}
			
			long te1 = System.nanoTime();
			reportTime(te1 - te0);
			
			doExceptionPropagation(loader, allMethods.values());
			
			addBogusThrows(loader, classNames);
			
			long te2 = System.nanoTime();
			reportTime(te2 - te1);
			
			writeEXC(allMethods.values(), new File(confdir, side+".exc"));
			
			System.out.println("EXC file written");
		}
	}

	private static String deobfDesc(String desc) {
		String rv = "";
		int pos = 0;
		while(pos < desc.length()) {
			switch(desc.charAt(pos)) {
			case 'L':
				int i = desc.indexOf(';', pos);
				String n = desc.substring(pos+1, i);
				rv += "L" + deobfOwner(n) + ";";
				pos = i+1;
				break;
			default: rv += desc.charAt(pos++); break;
			}
		}
		return rv;
	}

	private static String deobfOwner(String owner) {
		String p = knownClassDeobfNames.get(owner);
		if(p != null)
			return p;
		if(owner.contains("/"))
			return owner;
		return "net/minecraft/src/_" + owner;
	}

	static List<String> getClassNames(File jarfile) throws Exception {
		List<String> rv = new ArrayList<>();
		
		try (JarInputStream jf = new JarInputStream(new FileInputStream(jarfile))) {
			JarEntry je;
			// find all .class files in the jar file
			while((je = jf.getNextJarEntry()) != null) {
				String n = je.getName();
				if(n.startsWith("/"))
					n = n.substring(1);
				if(n.endsWith(".class"))
					rv.add(n.substring(0, n.length()-6).replace('/', '.'));
			}
		}
		
		return rv;
	}
	
	
	
	private static Collection<TryBlock> allTryCatchBlocks = new ArrayList<>();
	
	
	
	
	
	
	private static Class<?>[] typesToClasses(Type[] types) throws Exception {
		Class[] rv = new Class[types.length];
		
		// convert Types to Classes
		for(int k = 0; k < types.length; k++) {
			Type t = types[k];
			
			switch(t.getSort()) {
			case Type.OBJECT:
				rv[k] = loader.loadClass(t.getClassName());
				break;
			case Type.ARRAY:
				rv[k] = Class.forName(t.getInternalName().replace('/', '.'), false, loader);
				break;
			case Type.BOOLEAN: rv[k] = boolean.class; break;
			case Type.BYTE: rv[k] = byte.class; break;
			case Type.CHAR: rv[k] = char.class; break;
			case Type.DOUBLE: rv[k] = double.class; break;
			case Type.FLOAT: rv[k] = float.class; break;
			case Type.INT: rv[k] = int.class; break;
			case Type.LONG: rv[k] = long.class; break;
			case Type.SHORT: rv[k] = short.class; break;
			default: throw new Exception(t.toString());
			}
		}
		return rv;
	}
	
	
	
	private static TryBlock searchExceptionHandlerTable(List<TryBlock> handlers, Class<?> exceptionClass, boolean markReachable) {
		for(TryBlock tb : handlers) {
			if(markReachable && exceptionClass.isAssignableFrom(tb.catches))
				tb.isReachable = true;
			if(tb.catches.isAssignableFrom(exceptionClass))
				return tb;
		}
		return null;
	}
	
	
	private static Map<String, ClassNode> cachedNodes = new HashMap<>();
	private static ClassNode getClassNode(String name) throws Exception {
		ClassNode cn = cachedNodes.get(name);
		if(cn != null)
			return cn;
		cn = new ClassNode();
		try (InputStream in = loader.getResourceAsStream(name.replace('.', '/') + ".class")) {
			new ClassReader(in).accept(cn, ClassReader.EXPAND_FRAMES);
		}
		cachedNodes.put(name, cn);
		return cn;
	}
	

	private static void getExceptions(URLClassLoader loader, MethodIdentifier method) throws Exception {
		ClassNode cn = getClassNode(method.owner);
		
		MethodDetails methodGroup = allMethods.get(method);
		
		for(MethodDetails derived : methodGroup.allDerived) {
			ExceptionEntry e = new ExceptionEntry();
			e.method = derived;
			methodGroup.exceptionsFrom.add(e);
			
			e = new ExceptionEntry();
			e.method = methodGroup;
			derived.exceptionsTo.add(e);
		}
		
		if(method.owner.equals("mp"))
			method=method;
		
		for(MethodNode mn : (List<MethodNode>)cn.methods) {
			//System.out.println(" "+mn.name+mn.desc);
			if(!mn.name.equals(method.name) || !mn.desc.equals(method.desc))
				continue;
			
			Set<LabelNode> seenLabels = new HashSet<>();
			
			AnalyzerAdapter analyzer = new AnalyzerAdapter(cn.name, mn.access, mn.name, mn.desc, null);
			
			// maps handler node to try block object.
			// uses the handler node as a key because sometimes multiple
			// exception table entries are generated for a single catch block?
			Map<LabelNode, TryBlock> tryCatchData = new HashMap<>();
			
			for(TryCatchBlockNode tcbn : mn.tryCatchBlocks) {
				if(tcbn.type == null) continue; // ignore finally blocks
				
				if(tryCatchData.containsKey(tcbn.handler))
					continue; // ignore "split" exception table entries? (actually, merge them)
				
				TryBlock tb = new TryBlock();
				tb.method = methodGroup;
				tb.node = tcbn;
				tb.catches = Class.forName(tcbn.type.replace('/', '.'), false, loader);
				tb.isReachable = false;
				tryCatchData.put(tcbn.handler, tb);
				allTryCatchBlocks.add(tb);
				
				if(Error.class.isAssignableFrom(tb.catches) || RuntimeException.class.isAssignableFrom(tb.catches) || tb.catches.isAssignableFrom(RuntimeException.class))
					tb.isReachable = true;
			}
			
			analyzer.visitCode();
			for(TryCatchBlockNode tcbn : mn.tryCatchBlocks)
				tcbn.accept(analyzer);
			analyzer.visitMaxs(mn.maxStack, mn.maxLocals);
			if(mn.localVariables != null)
				for(LocalVariableNode lvn : mn.localVariables)
					lvn.accept(analyzer);
			
			for(AbstractInsnNode in = mn.instructions.getFirst(); in != null; in = in.getNext()) {
				if(in instanceof LabelNode) {
					seenLabels.add((LabelNode)in);
					
				} else if(in.getOpcode() == Opcodes.ATHROW) {
					String type = (String)analyzer.stack.get(analyzer.stack.size() - 1);
					type = type.replace('/', '.');
					Class<?> excClass = Class.forName(type, false, loader);
					
					// Determine which try-catch blocks this throw is inside.
					List<TryBlock> insideHandlers = new ArrayList<TryBlock>();
					for(TryCatchBlockNode tcb : (List<TryCatchBlockNode>)mn.tryCatchBlocks) {
						if(seenLabels.contains(tcb.start) && !seenLabels.contains(tcb.end)) {
							if(tcb.type != null) // ignore finally blocks
								if(!insideHandlers.contains(tryCatchData.get(tcb.handler)))
									insideHandlers.add(tryCatchData.get(tcb.handler));
						}
					}
					
					
					// Find the first one, out of those, that will catch the exception
					TryBlock caughtBy = searchExceptionHandlerTable(insideHandlers, excClass, true);
					if(caughtBy == null && isCheckedException(excClass))
						methodGroup.exceptions.add(type);
					
				} else if(in instanceof MethodInsnNode) {
					
					// Determine which try-catch blocks this call is inside.
					List<TryBlock> insideHandlers = new ArrayList<TryBlock>();
					for(TryCatchBlockNode tcb : (List<TryCatchBlockNode>)mn.tryCatchBlocks) {
						if(seenLabels.contains(tcb.start) && !seenLabels.contains(tcb.end)) {
							if(tcb.type != null) // ignore finally blocks
								if(!insideHandlers.contains(tryCatchData.get(tcb.handler)))
									insideHandlers.add(tryCatchData.get(tcb.handler));
						}
					}
					
					MethodInsnNode min = (MethodInsnNode)in;
					
					Class<?> systemOwnerClass = null;
					
					boolean isCalledMethodObfuscated =
						!deobfOwner(min.owner).equals(min.owner)
						|| min.name.length() <= 2;
					
					if(min.owner.startsWith("["))
						isCalledMethodObfuscated = false;
					
					if(!isCalledMethodObfuscated)
						try {
							systemOwnerClass = Class.forName(min.owner.replace('/', '.'), false, isCalledMethodObfuscated ? ClassLoader.getSystemClassLoader() : loader);
						} catch(ClassNotFoundException e) {
						}
					else
						try {
							systemOwnerClass = Class.forName(min.owner.replace('/', '.'), false, ClassLoader.getSystemClassLoader());
							isCalledMethodObfuscated = false;
						} catch(ClassNotFoundException e) {
						}
					
					
					
					Type calledType = Type.getMethodType(min.desc);
					Type[] argTypes = calledType.getArgumentTypes();
					Class[] argClasses = typesToClasses(argTypes);
					
					
					
					MethodIdentifier called = new MethodIdentifier(min.owner.replace('/', '.'), min.name, min.desc);
					MethodDetails calledGroup = allMethods.get(called);
					
					if(systemOwnerClass == null) {
						
						if(calledGroup == null) {
							
							// try superclasses
							for(Class<?> sc : getAllSupers(Class.forName(called.owner, false, loader))) {
								MethodIdentifier _try = new MethodIdentifier(sc.getName(), min.name, min.desc);
								calledGroup = allMethods.get(_try);
								if(calledGroup != null) {
									called = _try;
									break;
								}
								
								try {
									sc.getDeclaredMethod(min.name, argClasses);
									systemOwnerClass = sc;
									break;
								} catch(NoSuchMethodException e) {
								}
								
								//System.out.println(_try+" not found");
							}
							
							if(systemOwnerClass != null)
								; //System.out.println(systemOwnerClass+" matches "+called);
							else if(calledGroup == null) {
								throw new Exception("unknown obfuscated method: "+called+" from "+method);
								//continue;
							}
						}
					}
					
					if(systemOwnerClass != null) {
						// called method is a method of a system class, so
						// we can easily get its exception list
						
						Class<?>[] exceptionTypes = null;
						
						if(min.name.equals("<init>"))
							exceptionTypes = systemOwnerClass.getDeclaredConstructor(argClasses).getExceptionTypes();
						else {
							try {
								exceptionTypes = systemOwnerClass.getDeclaredMethod(min.name, argClasses).getExceptionTypes();
							} catch(NoSuchMethodException e) {
								// try superclasses
								for(Class<?> sc : getAllSupers(systemOwnerClass)) {
									try {
										exceptionTypes = sc.getDeclaredMethod(min.name, argClasses).getExceptionTypes();
										break;
									} catch(NoSuchMethodException e2) {
									}
								}
								if(exceptionTypes == null)
									throw (NoSuchMethodException)new NoSuchMethodException().initCause(e);
							}
						}
						
						for(Class<?> excClass : exceptionTypes) {
							
							// CloneNotSupportedException is not actually thrown by arrays.
							if(excClass == CloneNotSupportedException.class && systemOwnerClass.isArray())
								continue;
							
							// Find where this exception is caught.
							TryBlock caughtBy = null;
							for(TryBlock tb : insideHandlers) {
								if(excClass.isAssignableFrom(tb.catches))
									tb.isReachable = true;
								if(tb.catches.isAssignableFrom(excClass)) {
									caughtBy = tb;
									break;
								}
							}
							
							if(caughtBy != null)
								caughtBy.isReachable = true;
							
							else {
								// Not caught; if checked, must appear in method exceptions list
								
								if(isCheckedException(excClass))
									methodGroup.exceptions.add(excClass.getName());
							}
						}
						
					} else {
						
						// called method has unknown exception list.
						// add a record so whatever exceptions it throws
						// will be propagated to this one.
						
						ExceptionEntry entry = new ExceptionEntry();
						entry.tryBlocks = insideHandlers;
						entry.method = calledGroup;
						methodGroup.exceptionsFrom.add(entry);
						
						entry = new ExceptionEntry();
						entry.tryBlocks = insideHandlers;
						entry.method = methodGroup;
						calledGroup.exceptionsTo.add(entry);
						for(MethodDetails md2 : calledGroup.allDerived)
							md2.exceptionsTo.add(entry);
					}
				}
				in.accept(analyzer);
			}
			
			return;
		}
		
		throw new RuntimeException("Method not found: "+method);
		//System.out.println("Method not found: "+method);
	}
	
	private static boolean isCheckedException(Class<?> excClass) {
		if(RuntimeException.class.isAssignableFrom(excClass)) return false;
		if(Error.class.isAssignableFrom(excClass)) return false;
		if(excClass == Throwable.class) return false;
		return true;
		
	}

	private static void addBogusThrows(URLClassLoader loader, Collection<String> classNames) throws Exception {
		System.out.println("Finding unreachable catch blocks...");
		
		for(TryBlock tb : allTryCatchBlocks) {
			//if(tb.method.ident.owner.equals("bem"))
			//	System.out.println("for "+tb.catches+" in "+tb.method.ident);
			if(!tb.isReachable) {
				System.out.println("unreachable catch block: for "+tb.catches+" in "+tb.method.ident);
				
				// find all the methods we could add a bogus throws clause to
				// to make this catch block reachable
				Set<MethodDetails> possible = new TreeSet<>();
				for(ExceptionEntry ee : tb.method.exceptionsFrom) {
					if(!ee.tryBlocks.contains(tb))
						continue; // method call outside this try block
					
					if(searchExceptionHandlerTable(ee.tryBlocks, tb.catches, false) != tb)
						continue; // exception would be caught by a different try block
					
					possible.add(ee.method);
				}
				
				// Victim preference order:
				// * A private method only called from this location (Not implemented)
				// * A method that has this exception caught by all its call sites
				// * A non-private method only called from this location
				
				MethodDetails withOtherCatchBlocks = null;
				MethodDetails onlyCalledHere = null;
				MethodDetails onlyCalledHereAndPrivate = null;
				for(MethodDetails md : possible) {
					if(md.exceptionsTo.size() == 1 && md.group.methods.size() == 1) {
						onlyCalledHere = md;
						
					} else if(withOtherCatchBlocks == null) {
						
						withOtherCatchBlocks = md;
						
						// see if, everywhere else this method is called, the exception
						// would be caught
						for(MethodDetails gmd : md.group.methods)
							for(ExceptionEntry ee : gmd.exceptionsTo)
								if(!ee.method.equals(md) && searchExceptionHandlerTable(ee.tryBlocks, tb.catches, false) == null) {
									withOtherCatchBlocks = null;
									break;
								}
					}
				}
				
				MethodDetails picked = null;
				if(onlyCalledHereAndPrivate != null) picked = onlyCalledHereAndPrivate;
				else if(withOtherCatchBlocks != null) picked = withOtherCatchBlocks;
				else if(onlyCalledHere != null) picked = onlyCalledHere;
				
				if(picked.ident.name.equals("ac"))
					picked = picked;
				
				if(picked == null)
					System.out.println("  Bogus exception victim: NONE CHOSEN!");
				else {
					System.out.println("  Bogus exception victim: "+picked);
					for(MethodDetails md : picked.group.methods)
						md.exceptions.add(tb.catches.getName());
				}
				
			}
		}
	}

	static void doExceptionPropagation(ClassLoader loader, Collection<MethodDetails> methods) throws Exception {
		boolean changed = true;
		int passNo = 0;
		System.out.println("Beginning exception propagation on "+methods.size()+" methods");
		while(changed) {
			changed = false;
			
			passNo++;
			int numAdded = 0;
			int numGroups = 0;
			
			for(MethodDetails g1 : methods) {
				boolean changedGroup = false;
				
				for(ExceptionEntry e : g1.exceptionsFrom) {
					
					exceptions: for(String excClassName : e.method.exceptions) {
						Class<?> excClass = loader.loadClass(excClassName);
						
						TryBlock caughtBy = searchExceptionHandlerTable(e.tryBlocks, excClass, true);
						
						if(caughtBy == null) {
							if(g1.exceptions.add(excClassName)) {
								if(g1.group.srgName.equals("run")/* || excClassName.equals("java.lang.CloneNotSupportedException")*/)
									System.err.println("adding "+excClassName+" to "+g1.group.srgName+" from "+e.method);
								numAdded++;
								changedGroup = true;
							}
						}
					}
				}
				
				changed |= changedGroup;
				
				if(changedGroup)
					numGroups++;
			}
			
			System.out.println("Pass "+passNo+" - added "+numAdded+" exceptions to "+numGroups+" method groups");
		}
		
		System.out.println("Exception propagation done after "+passNo+" passes");
	}
	
	static void writeEXC(Collection<MethodDetails> methods, File file) throws Exception {
		try (PrintWriter exc = new PrintWriter(file)) {
			for(MethodDetails mg : methods) {
				
				String exceptionString = "";
				for(String throwsClass : mg.exceptions) {
					throwsClass = deobfOwner(throwsClass.replace('.','/'));
					if(!exceptionString.isEmpty())
						exceptionString += "," + throwsClass;
					else
						exceptionString = throwsClass;
				}
				
				exc.println(deobfOwner(mg.ident.owner.replace('.', '/')) + "." + mg.group.srgName + deobfDesc(mg.ident.desc) + "=" + exceptionString + "|" + getEXCArgumentString(mg.ident.desc));
			}
		}
	}
	
	static String getEXCArgumentString(Type t) {
		switch(t.getSort()) {
		case Type.ARRAY: return "ArrayOf" + getEXCArgumentString(t.getElementType());
		case Type.BOOLEAN: return "Boolean";
		case Type.BYTE: return "Byte";
		case Type.CHAR: return "Char";
		case Type.DOUBLE: return "Double";
		case Type.FLOAT: return "Float";
		case Type.INT: return "Int";
		case Type.LONG: return "Long";
		case Type.SHORT: return "Short";
		case Type.OBJECT:
			String s = t.getClassName();
			if(s.contains("."))
				s = s.substring(s.lastIndexOf('.') + 1);
			return s;
		default: return "";
		}
	}
	
	static String getEXCArgumentString(String desc) {
		Type[] argTypes = Type.getMethodType(desc).getArgumentTypes();
		List<String> argNames = new ArrayList<>(argTypes.length);
		
		
		for(int k = 0; k < argTypes.length; k++) {
			argNames.add("par"+(k+1)+getEXCArgumentString(argTypes[k]));
		}
		
		
		StringBuilder rv = new StringBuilder();
		for(String s : argNames) {
			if(rv.length() > 0)
				rv.append(',');
			rv.append(s);
		}
		return rv.toString();
	}
}
