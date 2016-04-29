package be.ucl.info.ingi1122.highlight.tools;

public class MyPortion implements Portion{
	int debut,fin;
	public MyPortion(int start, int end){
		this.debut=start;
		this.fin  =end;
	}
	public int getBegin(){
		return debut; 
	}
	public int getEnd(){
		return fin;
	}
	public String toString(){
		return debut+","+fin;
	}
}
