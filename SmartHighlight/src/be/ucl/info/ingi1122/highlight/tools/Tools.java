package be.ucl.info.ingi1122.highlight.tools;

public class Tools {

	public static Portion[] quoiSurligner(char[] texte, char[][] mots) {
		
		return new Portion[0];
	}
	
	public static boolean correspond(char[] texte, char[][] mots) {
		
		return true;
	}
	
	/*
	 * SORTING ALGORITHM
	 */
	public static void tri(char[][] mots){
		makeHeap(mots);
		for(int i=mots.length-1;i>0;i--){
			swap(0,i,mots);
			getMax(mots,0,i-1);
		}
	}
	private static void makeHeap(char[][]mots){
		int end = mots.length-1;
		for(int i=(end)/2;i>=0;i--){
			getMax(mots,i,end);
		}
	}
	private static void getMax(char[][] mots, int ind, int end){
		int left = 2*ind;
		int right = left+1;
		int max;
		if(left<=end && compareWords(mots[left],mots[ind])>0){
			max=left;
		} else {
			max=ind;
		}
		
		if(right<=end && compareWords(mots[right],mots[max])>0){
			max=right;
		}
		
		if(max!=ind){
			swap(ind,max,mots);
			getMax(mots,max,end);
		}
	}

	// return >0 si w2->w1
	private static int compareWords(char[] w1, char[] w2){
		final int min = (w1.length<w2.length)? w1.length: w2.length;
		for(int i=0;i<min;i++){
			int dw = w1[i]-w2[i];
			if(dw!=0) return dw;
		}
		
		return w1.length-w2.length;
	}
	
	private static void swap(int i, int j, char[][] mots){
		char[] save = mots[i];
		mots[i] = mots[j];
		mots[j] = save;
	}
	
	//--------------------------------------
	
}
