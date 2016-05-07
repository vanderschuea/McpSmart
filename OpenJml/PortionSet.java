
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
	// TODO

	/**
	 * ////////////////////////////////////////////////////
	 *					CONSTRUCTOR
	 * ////////////////////////////////////////////////////
	 */
	//@ modifies positions, size, capacity
	//@ requires max>0 && max<Integer.MAX_VALUE/2
	//@ ensures size==0 && positions.length==max*2 && capacity==max
	public PortionSet(int max) {
		positions = new int[max*2];
		capacity = max;
		size = 0;
		// TODO: set class invariants too
	}


	/**
	 * ////////////////////////////////////////////////////
	 *					PUBLIC METHODS
	 * ////////////////////////////////////////////////////
	 */
	public boolean contains(int n) {
		boolean result = false;
		for (int i = 0; !result && i < size; i++) {
			if (begin(i) <= n && n < end(i)) {
				result = true;
				break;
			}
		}
		return result;
	}
	// 		Conditions on the arguments
	//@ requires begin>=0 && begin<end && end<=Integer.MAX_VALUE
	// 		Conditions on the state of class variables/invariants
	// TODO: @ requires size<capacity
	public void add(int begin, int end) {
		if (size == 0) {
			addInterval(begin, end);
		} else {
			if (begin <= end(size-1) && begin(size-1) <= end){
                //@ assert begin <= end(size-1) && begin(size-1) <= end; // OpenJML en aura besoin...
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

	private void addInterval(int begin, int end) {
		positions[size*2] = begin;
		positions[size*2+1] = end;
		size++;
	}

	private void updateLastInterval(int begin, int end) {
		positions[(size-1)*2+1] = end >= end(size-1) ? end : end(size-1);
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
	public int begin(int i) {
		return positions[i*2];
	}

	/*@ private normal_behavior
	  @   requires size*2 <= positions.length;
	  @   requires 0 <= i && i < size;
	  @   ensures \result == positions[i*2+1];
	  @   modifies \nothing;
	  @ pure helper */
	public int end(int i) {
		return positions[i*2+1];
	}
}
