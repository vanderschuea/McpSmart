package be.ucl.info.ingi1122.highlight.tools;

public class MyPortionSet {
	private boolean[] highlightTable;
	private int nPortions;
	
	public MyPortionSet(int nSize){
		highlightTable = new boolean[nSize];
		nPortions=0;
	}
	
	public void add(int start, int end){	
		int checkStart = Tools.max(0,start-1);
		int checkEnd   = Tools.min(highlightTable.length, end+1); 
		nPortions += 1-getNumberPortions(checkStart,checkEnd);
		for(int i=start;i<end;i++){
			highlightTable[i]=true;
		}
	}
	
	private int getNumberPortions(int start, int end){
		int n=0;
		if(highlightTable[start]) n++;
		for(int i=start+1;i<end;i++){
			if(highlightTable[i] && !highlightTable[i-1]) n++;
		}
		return n;
	}
	
	public Portion[] getPortions(){
		if(nPortions<=0) return null;
		MyPortion[] ports = new MyPortion[nPortions];
		int index=0;
		for(int i=0;i<highlightTable.length;){
			if(highlightTable[i]){
				int end = getUniquePortionEnd(i);
				ports[index]=new MyPortion(i,end);
				index++;
				i=end;
			}
			i=Tools.min(i+1, highlightTable.length);
		}
		return ports;
	}
	
	private int getUniquePortionEnd(final int start){
		int end=start+1;
		while(end<highlightTable.length && highlightTable[end]){
			end++;
		}
		return end;
	}
	
	public boolean contains(int start, int end){
		boolean contains=true;
		for(int i=start;i<end && contains;i++){
			contains=highlightTable[i];
		}
		return contains;
	}

	public int getSize(){ return highlightTable.length; }
}
