// Command line : openjml -progress -esc -code-math java -spec-math safe PortionSet.java
public class PortionSet {

	/**
	 * ////////////////////////////////////////////////////
	 *					CLASS FIELDS
	 * ////////////////////////////////////////////////////
	 */
	private /*@spec_public@*/ int[] positions;
	private /*@spec_public@*/ int size;
	private final /*@spec_public@*/ int capacity;


	/**
	 * ////////////////////////////////////////////////////
	 *					CLASS INVARIANTS
	 * ////////////////////////////////////////////////////
	 */
	//@ public invariant size>=0 && size<=capacity;
	//@ public invariant capacity>0 && 2*capacity==positions.length;
	//@ public invariant positions.length>0;
	//@ public invariant (\forall int i; i>=0 && i<2*size-1; positions[i]<positions[i+1]);

	/**
	 * ////////////////////////////////////////////////////
	 *					CONSTRUCTOR
	 * ////////////////////////////////////////////////////
	 */
	//@ requires max>0;
	//@ ensures size==0 && positions.length==max*2 && capacity==max;
	//@ modifies positions, size, capacity;
	public PortionSet(int max) {
		positions = new int[max*2];
		capacity = max;
		size = 0;
	}


	/**
	 * ////////////////////////////////////////////////////
	 *					PUBLIC METHODS
	 * ////////////////////////////////////////////////////
	 */
	// The solver crashes sometimes while trying to prove this method,
	//    relaunching it should solve the problem.
	
	//@ requires n>=0;
	//@ requires size*2 <= positions.length;
	/*@ ensures \result <==>
	  @			(\exists int I; I>=0 && I<size; begin(I) <= n && n < end(I)); */
	//@ pure;
	public boolean contains(int n) {
		boolean result = false;
		int i=0;
		//@ loop_invariant i>=0 && i<=size;
		/*@ loop_invariant !(result) <==>
		  @ 		(\forall int I; I>=0 && I<i; !(begin(I) <= n && n < end(I)));*/
		//@ decreases size-i;
		while (!result && i < size) {
			if (begin(i) <= n && n < end(i)) {
				result = true;
			}
			i=i+1;
		}
		return result;
	}

	//@ requires begin<end;
	//@ requires size>0 ==> begin>=begin(size-1);
	//@ requires size==capacity ==> begin<=end(size-1);

	//@ ensures \old(size)==0 ==> (positions[0]==begin && positions[1]==end && size==1);
	/*@ ensures ( \old(size)==size && end<=end(size-1) )
	  	  		 ==> (end>=end(size-1)<==>positions[(size-1)*2+1]==end &&
					  end<=end(size-1)<==>positions[(size-1)*2+1]==end(size-1));*/
	/*@ ensures (\old(size)==size) 
	  			 ==> positions[size-1]==\old(positions[size-1]);*/
	/*@ ensures ( \old(size)>0 && begin>end(size-1))
				 ==> (size == \old(size)+1 &&
					  positions[\old(size)*2] == begin &&
					  positions[\old(size)*2+1] == end);*/
	public void add(final int begin, final int end) {
		if (size == 0) {
			addInterval(begin, end);
		} else {
			if (begin <= end(size-1)){// && begin(size-1) <= end){
				updateLastInterval(begin, end);
				
			} else {
				addInterval(begin, end);
			}
		}
	}

	/**
	 * ////////////////////////////////////////////////////
	 *					PRIVATE METHODS
	 * ////////////////////////////////////////////////////
	 */
	//@ requires begin<end;
	//@ requires size<capacity;
    //@ requires size>0 ==> (begin>positions[(size-1)*2+1]);

	//@ ensures size == \old(size)+1;
	//@ ensures positions[\old(size)*2] == begin;
	//@ ensures positions[\old(size)*2+1] == end;
	private void addInterval(int begin, int end) {
		positions[size*2] = begin;
		positions[size*2+1] = end;
		size=size+1;
	}

	//@ requires size>0;
	//@ requires begin(size-1)<=begin;
	//@ requires begin<=end(size-1);
	//@ requires begin(size-1)<end;

	//@ ensures  end>=end(size-1)<==>positions[(size-1)*2+1]==end;
	//@ ensures	 end<=end(size-1)<==>positions[(size-1)*2+1]==end(size-1);

	//@ modifies positions[(size-1)*2+1];
	private void updateLastInterval(int begin, int end) {
		if(end>end(size-1)){
			positions[(size-1)*2+1] = end;
		} else {
			positions[(size-1)*2+1] = end(size-1);
		}
	}



	/**
	 * ////////////////////////////////////////////////////
	 *					GIVEN PROOFS
	 * ////////////////////////////////////////////////////
	 */

    // Une méthode annotée "helper" ne doit pas garantir les invariants de classe (post).
    // En contrepartie, ils ne sont pas non plus garantis lors de l'appel (pre).
    // Cela permet d'appeler begin(int) et end(int) à l'intérieur de fonctions qui cassent (temporairement) les invariants.
    // Vous pouvez simplement ignorer ce mot-clé car vous n'en avez pas besoin ailleurs.

    // Les deux méthodes suivantes sont complètement spécifiées.
    // Vous ne devez normalement pas y toucher.

	/*@ private normal_behavior
	  @   requires size*2 <= positions.length;
	  @   requires 0 <= i && i < size;
	  @   ensures \result == positions[i*2];
	  @   modifies \nothing;
	  @ pure helper */
	public int begin(final int i) {
		return positions[i*2];
	}

	/*@ private normal_behavior
	  @   requires size*2 <= positions.length;
	  @   requires 0 <= i && i < size;
	  @   ensures \result == positions[i*2+1];
	  @   modifies \nothing;
	  @ pure helper */
	public int end(final int i) {
		return positions[i*2+1];
	}
}
