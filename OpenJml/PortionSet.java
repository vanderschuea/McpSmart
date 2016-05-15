// Command line : openjml -progress -esc -code-math java -spec-math safe PortionSet.java
public class PortionSet {

	/**
	 * ////////////////////////////////////////////////////
	 *			CLASS FIELDS
	 * ////////////////////////////////////////////////////
	 */
	private /*@spec_public@*/ int[] positions;
	private /*@spec_public@*/ int size;
	private final /*@spec_public@*/ int capacity;

	/**
	 * Description:
	 *    Nous avons ici a chaque fois impose qu'une portion etait definie par
	 *    [begin,end[. Par ailleurs si 'add' est appele il s'agit d'une portion
	 *    dont le 1er indice vient apres (/est egale à) celui de portion
	 *    precedente.
	 *    Les portions sont aussi toutes definis comme etant positives.
	 */

	/**
	 * ////////////////////////////////////////////////////
	 *			CLASS INVARIANTS
	 * ////////////////////////////////////////////////////
	 */

	/**
	 * Dans l'ordre:
	 *   - Necessaire pour garantir qu'aucun outOfBounds ne se produise
	 *   - Definition de la capacite de positions (>0 pour eviter des trucs inutiles)
	 *   - Pour garantir des portions disjointes
	 *   - Les portions sont définies par des indices (>=0)
	 */

	//@ public invariant size>=0 && size<=capacity;
	//@ public invariant capacity>0 && 2*capacity==positions.length;
	//@ public invariant (\forall int i; i>=0 && i<2*size-1; positions[i]<positions[i+1]);
	//@ public invariant size>0 ==> positions[0]>=0;

	/**
	 * ////////////////////////////////////////////////////
	 *			CONSTRUCTOR
	 * ////////////////////////////////////////////////////
	 */

	/**
	 * Pour respecter les invariants de classe max doit etre >0
	 */

	//@ requires max>0;

	//@ modifies positions, size, capacity;
	public PortionSet(int max) {
		positions = new int[max*2];
		capacity = max;
		size = 0;
	}


	/**
	 * ////////////////////////////////////////////////////
	 *			PUBLIC METHODS
	 * ////////////////////////////////////////////////////
	 */
	// The solver crashes sometimes while trying to prove this method,
	//    relaunching it should solve the problem.

	/**
	 * @Pre:  Un element negatif n'aurait pas de sens
	 * @Post: Retourne vrai si 'n' est compris dans un interval
	 */

	//@ requires n>0;

	/*@ ensures \result <==>
	  	(\exists int I; I>=0 && I<size; begin(I) <= n && n < end(I)); */

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

	/**
	 * @Pre:  - Les conditions pour satisfaire la def. d'une portion
	 *	  - Satisfaire la condition qu'un intervalle ne peut pas se trouver
	 *		avant un autre.
	 *	  - Si un intervalle n'a pas d'elements en commun avec le precedent,
	 *		il ne peut etre ajoute que si le vecteur positions n'est pas
	 *		deja rempli.
	 *
	 * @Post: S'il s'agit du 1er intervalle ou d'un interval disjoint, il a ete ajoute.
	 *	  S'il s'agit d'un intervalle qui chevauche l'intervalle precedent,
	 *		cellui-ci a ete modifie en consequence pour refleter un eventuel
	 * 		aggrandissement, afin de comprendre tous les elements des 2 portions.
	 */

	//@ requires begin<end && begin>=0;
	//@ requires size>0 ==> begin>=begin(size-1);
	//@ requires size==capacity ==> begin<=end(size-1);

	//@ ensures \old(size)==0 ==> (positions[0]==begin && positions[1]==end && size==1);
	/*@ ensures ( \old(size)==size && end<=end(size-1) )
	  	  		 ==> (end>=end(size-1)<==>positions[(size-1)*2+1]==end &&
				      end<=\old(positions[(size-1)*2+1])<==>
						positions[(size-1)*2+1]==\old(positions[(size-1)*2+1]));*/
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
	 *			PRIVATE METHODS
	 * ////////////////////////////////////////////////////
	 */

	/**
	 * @Pre:  - La definition d'une portion
	 *	  - Vu qu'on ajoute un element, il faut qu'il reste une place de libre
	 *	  - L'intervalle ajoute doit etre disjoint
	 *
	 * @Post: La taille a ete augmentee car l'intervalle a ete ajoute.
	 */


	//@ requires begin<end;
	//@ requires size==0 ==> begin>=0;
	//@ requires size<capacity;
	//@ requires size>0  ==> (begin>positions[(size-1)*2+1]);

	//@ ensures size == \old(size)+1;
	//@ ensures positions[\old(size)*2] == begin;
	//@ ensures positions[\old(size)*2+1] == end;
	
	// @ modifies positions[size*2], positions[size*2+1], size;
	private void addInterval(int begin, int end) {
		positions[size*2] = begin;
		positions[size*2+1] = end;
		size=size+1;
	}

	/**
	* @Pre:  - La definition d'une portion
	* 		   - L'intervalle ajoute doit chevaucher le dernier ajoute
	*
	* @Post: La taille est inchangée, mais la fin de l'intervalle a ete deplacee
	*				(pour augment sa taille) afin d'incorporer tous les elements
	*				definis par [begin,end[.
	*/

	//@ requires size>0;
	//@ requires begin<end;
	//@ requires begin(size-1)<=begin;
	//@ requires begin<=end(size-1);
	
	//@ ensures end>=\old(positions[(size-1)*2+1])<==>positions[(size-1)*2+1]==end;
	//@ ensures end<=\old(positions[(size-1)*2+1])<==>positions[(size-1)*2+1]==\old(positions[(size-1)*2+1]);

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
	 *			GIVEN PROOFS
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
