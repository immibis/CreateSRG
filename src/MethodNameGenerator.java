import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.objectweb.asm.Type;


public class MethodNameGenerator {
	
	private Map<String, Integer> indexByInfoString = new HashMap<String, Integer>();

	private String makeDescInfo(String desc, Map<String, String> deobfMap) {
		if(desc.startsWith("[")) {
			int levels = 0;
			while(desc.startsWith("[")) {
				levels++;
				desc = desc.substring(1);
			}
			return levels + makeDescInfo(desc, deobfMap);
		}
		if(desc.startsWith("Ljava/")) {
			int i = desc.lastIndexOf('/');
			return desc.substring(i+1, desc.length()-1);
		}
		if(desc.startsWith("L")) {
			String cl = desc.substring(1, desc.length() - 1);
			if(deobfMap.containsKey(cl))
				return stripPkg(deobfMap.get(cl));
		}
		return desc.substring(0, 1);
	}
	
	private String stripPkg(String in) {
		if(in.contains("/"))
			in = in.substring(in.lastIndexOf('/') + 1);
		return in;
	}
	
	int maxIndex = 0;

	public String generateMethodName(Set<MethodIdentifier> idents, Map<String, String> deobfMap, ClassLoader loader) {
		String desc = idents.iterator().next().desc;
		Type type = Type.getMethodType(desc);
		
		String infoString = "";
		
		if(idents.size() == 1) {
			String owner = idents.iterator().next().owner;
			if(deobfMap.containsKey(owner))
				infoString += stripPkg(deobfMap.get(owner)) + "_";
		}
		
		infoString += makeDescInfo(type.getReturnType().getDescriptor(), deobfMap);
		for(Type at : type.getArgumentTypes())
			infoString += makeDescInfo(at.getDescriptor(), deobfMap);
		
		if(!indexByInfoString.containsKey(infoString))
			indexByInfoString.put(infoString, 0);
		
		int index = indexByInfoString.get(infoString);
		indexByInfoString.put(infoString, index+1);
		
		if(index > maxIndex) {
			maxIndex = index;
			//System.out.println("max index: "+maxIndex);
		}
		
		return "func_" + index + "_" + infoString;
	}

}
