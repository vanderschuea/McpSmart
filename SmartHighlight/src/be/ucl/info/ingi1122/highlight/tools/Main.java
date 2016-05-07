package be.ucl.info.ingi1122.highlight.tools;

public class Main {

	public static void main(String[] args){
		String[] arr = {"jee", "hey", "je", "teste", "la", "fonction"};
		char[][] mots = toArr(arr);
		print(mots);
		System.out.println("--------------------------");
		print(mots);
	}
	
	public static char[][] toArr(String[] words){
		char [][] mots = new char[words.length][];
		for(int i=0;i<words.length;i++){
			mots[i] = new char[words[i].length()];
			for(int j=0;j<words[i].length();j++){
				mots[i][j]=words[i].charAt(j);
			}
		}
		return mots;
	}
	public static void print(char[][] mots){
		for(int i=0;i<mots.length;i++){
			for(int j=0;j<mots[i].length;j++){
				System.out.print(""+mots[i][j]);
			}
			System.out.print("\n");
		}
	}
}
