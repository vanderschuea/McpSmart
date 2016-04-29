package be.ucl.info.ingi1122.highlight.tools;

import java.util.Arrays;

public class MyPortionSet {
	private boolean[] highlightTable;
	private int nPortions;
	
	public MyPortionSet(int nSize){
		highlightTable = new boolean[nSize];
		nPortions=0;
	}
	
	// TODO: private?public
	public void add(int start, int end){
		//System.out.println(Arrays.toString(highlightTable)+","+nPortions);
		// Check si on lie avec une autre portion au debut et puis fin
		if(start==0 || (start>0 && !highlightTable[start-1])){
			nPortions++;
		}
		if(end<highlightTable.length && highlightTable[end]){
			nPortions--;
		}
		boolean changed = !highlightTable[start]; 
		for(int i=start;i<end;i++){
			if(!changed && !highlightTable[i]) changed=true;
			if(changed && highlightTable[i]){
				nPortions--;
				changed=false;
			}
			highlightTable[i]=true;
		}
		//System.out.println(Arrays.toString(highlightTable)+","+nPortions);
	}
	public Portion[] getPortions(){
		if(nPortions<=0) return null;
		// TODO: verifier creation de tableau en java
		MyPortion[] ports = new MyPortion[nPortions];
		final int l = highlightTable.length;
		int index=0;
		for(int i=0;i<l;i++){
			if(highlightTable[i]){
				int start = i;
				do{
					i++;
				}while(i<l && highlightTable[i]);
				ports[index]=new MyPortion(start,i);
				index++;
			}
		}
		return ports;
	}
	
	/**
	 * @pre:  start & end satisfy the portion-conditions
	 * @post: returns true if this portions is saved as to be highlighted
	 */
	public boolean contains(int start, int end){
		boolean contains=true;
		for(int i=start;i<end && contains;i++){
			contains=highlightTable[i];
		}
		return contains;
	}
	/**
	 * @pre:/
	 * @post: returns the length of highlightTable
	 */
	public int getSize(){ return highlightTable.length; }
}
