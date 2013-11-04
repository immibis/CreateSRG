class MethodIdentifier implements Comparable<MethodIdentifier> {
	public final String owner;
	public final String name;
	public final String desc;
	
	public MethodIdentifier(String owner, String name, String desc) {
		this.owner = owner;
		this.name = name;
		this.desc = desc;
	}
	
	@Override
	public boolean equals(Object obj) {
		if(obj instanceof MethodIdentifier) {
			MethodIdentifier fm = (MethodIdentifier)obj;
			return fm.desc.equals(desc) && fm.name.equals(name) && fm.owner.equals(owner);
		}
		return false;
	}
	
	@Override
	public int hashCode() {
		return desc.hashCode() ^ name.hashCode() ^ owner.hashCode();
	}
	
	@Override
	public String toString() {
		return owner + "/" + name + desc;
	}
	
	@Override
	public int compareTo(MethodIdentifier arg0) {
		int i = owner.compareTo(arg0.owner);
		if(i != 0) return i;
		i = name.compareTo(arg0.name);
		if(i != 0) return i;
		return desc.compareTo(arg0.desc);
	}
}