package be.ucl.info.ingi1122.highlight.tools;

import java.util.Arrays;

public class MyPortionSet {
	private boolean[] highlightTable;
	private int nPortions;
	
	public MyPortionSet(int nSize){
		highlightTable = new boolean[nSize];
		nPortions=0;
	}
	
	public void add(int start, int end){
		//System.out.println(Arrays.toString(highlightTable)+","+nPortions);
		
		int checkStart = Tools.max(0,start-1);
		int checkEnd   = Tools.min(highlightTable.length, end+1); 
		nPortions += 1-getNumberPortions(checkStart,checkEnd);
		for(int i=start;i<end;i++){
			highlightTable[i]=true;
		}
		//System.out.println(Arrays.toString(highlightTable)+","+nPortions);
	}
	
	/**
	 * 
	 * @pre: start & end are defined like a portion
	 * @post: returns the number of portion within this interval (>=0)
	 */
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
