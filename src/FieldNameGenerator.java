import java.util.HashMap;
import java.util.Map;


public class FieldNameGenerator {
	
	private Map<String, Integer> indexByInfoString = new HashMap<String, Integer>();

	private String makeDescInfo(String desc) {
		if(desc.startsWith("[")) {
			int levels = 0;
			while(desc.startsWith("[")) {
				levels++;
				desc = desc.substring(1);
			}
			return levels + makeDescInfo(desc);
		}
		if(desc.startsWith("Ljava/")) {
			int i = desc.lastIndexOf('/');
			return desc.substring(i+1, desc.length()-1);
		}
		return desc.substring(0, 1);
	}
	
	public String generateName(String owner, String name, String desc, String deobfOwner) {
		if(deobfOwner.contains("/"))
			deobfOwner = deobfOwner.substring(deobfOwner.lastIndexOf('/') + 1);
		
		String infoString = deobfOwner.replace("_", "") + "_" + makeDescInfo(desc);
		
		if(!indexByInfoString.containsKey(infoString))
			indexByInfoString.put(infoString, 0);
		
		int index = indexByInfoString.get(infoString);
		indexByInfoString.put(infoString, index+1);
		return "field_" + index + "_" + infoString;
	}

}
