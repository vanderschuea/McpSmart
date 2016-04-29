package be.ucl.info.ingi1122.highlight.tools;

public class Main2 {

	public static void main(String[] args){
		String test2 = "chevalise plop valise";
		String test  = "cheval valise";
		char[][] mots = Main.toArr(test.split(" "));
		Main.print(mots);
		System.out.println("--------------------------");
		System.out.println(Tools.correspond(test2.toCharArray(),mots));
		printPortions(Tools.quoiSurligner(test2.toCharArray(),mots));
		
		
		
	}
	
	public static void printPortions(Portion[] port){
		if(port==null){
			System.out.println("null");
			return;
		}
		for(int i=0;i<port.length;i++){
			if(port[i] instanceof MyPortion){
				MyPortion p = (MyPortion) port[i];
				System.out.println(p.toString());
			}
		}
	}
}
