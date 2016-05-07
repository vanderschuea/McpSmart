package be.ucl.info.ingi1122.highlight.tools;

public class Tools {
	
	public static boolean correspond(final char[] texte, char[][] mots) {
		if(mots==null||mots.length==0){
			if(texte==null || texte.length==0) return true;
			else return false;
		}
		if(texte==null || texte.length==0) return false;
		
		boolean [] tested = new boolean[mots.length];
		int count=0;
		for(int i=0;i<texte.length && count<mots.length;i++){
			for(int j=0;j<mots.length && count<mots.length;j++){
				if(!tested[j]){
					if(equalWords(texte,i,min(i+mots[j].length,texte.length),mots[j])){
						tested[j]=true;
						count++;
					}
				}
			}
		}
		return count==mots.length;
	}
	
	public static Portion[] quoiSurligner(final char[] texte, char[][] mots) {
		if(mots==null||mots.length==0||texte==null || texte.length==0){
			return null;
		}
		
		MyPortionSet pset = new MyPortionSet(texte.length);
		for(int i=0;i<texte.length;i++){
			chercheTexte(pset,texte,i,mots);
		}
		return pset.getPortions();
	}
	
	public static void chercheTexte(MyPortionSet pset, final char[] texte, final int start, char[][]mots){
		for(int j=0;j<mots.length;j++){
			int end = start+mots[j].length;
			if(end<=texte.length){
				if(equalWords(texte,start,end,mots[j])){
					pset.add(start, end);
				}
			}
		}
	}
	
	
	
	public static int min(final int a, final int b){
		if(a<b) return a;
		else  	return b;
	}
	

	public static int max(final int a, final int b){
		if(a>b) return a;
		else  	return b;
	}
	
	private static boolean equalWords(final char[] w1, final int start, final int end, final char[] w2){
		final int w1length = end-start;
		final int w2length = w2.length;
		final int min = min(w1length,w2length);
		for(int i=0;i<min;i++){
			int dw = w1[start+i]-w2[i];
			if(dw!=0) return false;
		}
		
		return w1length==w2length;
	}
}
