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
		MethodDetails from;
		Set<String> caught = new HashSet<>();
	}
	
	static class MethodDetails implements Comparable<MethodDetails> {
		MethodGroup group = new MethodGroup();
		
		Set<MethodDetails> allDerived = new HashSet<>();
		
		// used during exception discovery and propagation phase
		List<ExceptionEntry> exceptionsFrom = new ArrayList<>();
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
		System.in.read();
		
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
	
	
	
	
	
	
	
	

	private static void getExceptions(URLClassLoader loader, MethodIdentifier method) throws Exception {
		ClassNode cn = new ClassNode();
		try (InputStream in = loader.getResourceAsStream(method.owner.replace('.', '/') + ".class")) {
			new ClassReader(in).accept(cn, ClassReader.EXPAND_FRAMES);
		}
		
		MethodDetails methodGroup = allMethods.get(method);
		
		for(MethodDetails derived : methodGroup.allDerived) {
			ExceptionEntry e = new ExceptionEntry();
			e.caught = new HashSet<>();
			e.from = derived;
			methodGroup.exceptionsFrom.add(e);
		}
		
		for(MethodNode mn : (List<MethodNode>)cn.methods) {
			//System.out.println(" "+mn.name+mn.desc);
			if(!mn.name.equals(method.name) || !mn.desc.equals(method.desc))
				continue;
			
			Set<LabelNode> seenLabels = new HashSet<>();
			
			AnalyzerAdapter analyzer = new AnalyzerAdapter(cn.name, mn.access, mn.name, mn.desc, null);
			
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
					
					// Determine which try-catch blocks this throw is inside.
					Set<String> caught = new HashSet<String>();
					for(TryCatchBlockNode tcb : (List<TryCatchBlockNode>)mn.tryCatchBlocks) {
						if(seenLabels.contains(tcb.start) && !seenLabels.contains(tcb.end)) {
							if(tcb.type != null) // ignore finally blocks
								caught.add(tcb.type.replace('/', '.'));
						}
					}
					
					
					boolean isCaught = caught.contains(type) || type.equals("java.lang.Throwable") || type.equals("java.lang.Error") || type.equals("java.lang.RuntimeException");
					for(Class<?> sc : getAllSupers(Class.forName(type, false, loader)))
						if(caught.contains(sc.getName()) || sc == RuntimeException.class || sc == Error.class)
							isCaught = true;
					
					if(!isCaught)
						methodGroup.exceptions.add(type);
					
				} else if(in instanceof MethodInsnNode) {
					
					// Determine which try-catch blocks this call is inside.
					Set<String> caught = new HashSet<String>();
					for(TryCatchBlockNode tcb : (List<TryCatchBlockNode>)mn.tryCatchBlocks) {
						if(seenLabels.contains(tcb.start) && !seenLabels.contains(tcb.end)) {
							if(tcb.type != null) // ignore finally blocks
								caught.add(tcb.type.replace('/', '.'));
						}
					}
					
					MethodInsnNode min = (MethodInsnNode)in;
					
					Class<?> systemOwnerClass = null;
					
					boolean isCalledMethodObfuscated =
						!deobfOwner(min.owner).equals(min.owner)
						|| min.name.length() <= 2;
					
					if(min.owner.startsWith("["))
						isCalledMethodObfuscated = false;
					
					try {
						systemOwnerClass = Class.forName(min.owner.replace('/', '.'), false, isCalledMethodObfuscated ? ClassLoader.getSystemClassLoader() : loader);
					} catch(ClassNotFoundException e) {
					}
					
					
					
					Type calledType = Type.getMethodType(min.desc);
					Type[] argTypes = calledType.getArgumentTypes();
					Class[] argClasses = new Class[argTypes.length];
					
					// convert Types to Classes
					for(int k = 0; k < argTypes.length; k++) {
						Type t = argTypes[k];
						
						switch(t.getSort()) {
						case Type.OBJECT:
							argClasses[k] = loader.loadClass(t.getClassName());
							break;
						case Type.ARRAY:
							argClasses[k] = Class.forName(t.getInternalName().replace('/', '.'), false, loader);
							break;
						case Type.BOOLEAN: argClasses[k] = boolean.class; break;
						case Type.BYTE: argClasses[k] = byte.class; break;
						case Type.CHAR: argClasses[k] = char.class; break;
						case Type.DOUBLE: argClasses[k] = double.class; break;
						case Type.FLOAT: argClasses[k] = float.class; break;
						case Type.INT: argClasses[k] = int.class; break;
						case Type.LONG: argClasses[k] = long.class; break;
						case Type.SHORT: argClasses[k] = short.class; break;
						default: throw new Exception(t.toString());
						}
					}
					
					
					
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
						
						exceptions: for(Class<?> excClass : exceptionTypes) {
							if(RuntimeException.class.isAssignableFrom(excClass) || Error.class.isAssignableFrom(excClass))
								continue;
							if(caught.contains(excClass.getName()))
								continue;
							
							if(excClass == CloneNotSupportedException.class && systemOwnerClass.isArray())
								continue;
							
							for(Class<?> sc : getAllSupers(excClass))
								if(caught.contains(sc.getName()))
									continue exceptions;
							
							//if(mn.name.equals("toString"))
							//	System.err.println(method.owner+"/"+mn.name+mn.desc+" throws "+getAllSupers(excClass)+" from "+systemOwnerClass+" catches "+caught);
							methodGroup.exceptions.add(excClass.getName());
						}
						
					} else {
						
						ExceptionEntry entry = new ExceptionEntry();
						entry.caught = caught;
						entry.from = calledGroup;
						//if(mn.name.equals("toString"))
						//	System.err.println(method.owner+"/"+mn.name+mn.desc+" propagates from "+calledGroup.srgName+" catches "+caught);
						methodGroup.exceptionsFrom.add(entry);
					}
				}
				in.accept(analyzer);
			}
			
			return;
		}
		
		throw new RuntimeException("Method not found: "+method);
		//System.out.println("Method not found: "+method);
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
					
					exceptions: for(String excClassName : e.from.exceptions) {
						Class<?> excClass = loader.loadClass(excClassName);
						
						if(e.caught.contains(excClass.getName()))
							continue exceptions;
						
						for(Class<?> sc : getAllSupers(excClass))
							if(e.caught.contains(sc.getName()))
								continue exceptions;
						
						if(g1.exceptions.add(excClassName)) {
							if(g1.group.srgName.equals("run")/* || excClassName.equals("java.lang.CloneNotSupportedException")*/)
								System.err.println("adding "+excClassName+" to "+g1.group.srgName+" from "+e.from);
							numAdded++;
							changedGroup = true;
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
