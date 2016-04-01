open util/ordering[Time] as to
open util/ordering[ReceptacleAbstrait] as ro
open util/ordering[Intersection] as io

/**
============================================================
																	SIGS
============================================================
*/

/**
	Le drone : 
	attributs : 
		cheminIntersection : liste de toutes les intersections par lequel va passer le drone pour livrer une commande
			On passe à l'intersection suivante en fonction du temps
		currentIntersection : l'intersection actuelle du drone
		cheminReceptacle : liste de tous les réceptacles par lequel va passer le drone pour livrer une commande
		df : la destination final de la commande

*/
sig Drone 
{
	cheminIntersection: set Intersection -> Time,//Chemin
	currentIntersection: cheminIntersection one -> Time, 
	cheminReceptacle: set ReceptacleAbstrait -> Time,
	df: Receptacle -> Time, //Destination finale
	
	commandes: set Commande,
	currentCommande: commandes one -> Time
}

/**
	ReceptacleAbstrait
		implémenté par tous les Receptacle et l'entrepot.
*/
abstract sig ReceptacleAbstrait
{
	i:Intersection
}

sig Time {}

sig Intersection 
{
	x : Int, //Abscisse
	y : Int	 //Ordonnée
}

sig Commande 
{
	receptacle : lone Receptacle
}

sig Receptacle extends ReceptacleAbstrait
{
}

one sig Entrepot extends ReceptacleAbstrait
{
}

/**
============================================================
																	FACTS
============================================================
*/
/**
	DisjointCommandSets
		Chaque commandes peut être dans un seul drône
*/
fact DisjointCommandSets
{
	Drone<:commandes in Drone lone-> Commande
}


/**
============================================================
																	FUN
============================================================
*/
fun nextReceptacle [r:ReceptacleAbstrait, rs: set ReceptacleAbstrait]: set ReceptacleAbstrait
{
	min[r.nexts & rs]
}

fun nextIntersection [i:Intersection, is: set Intersection]: set Intersection
{
	min[i.nexts & is]
}

fun absVal [n:Int]: Int
{
	(n < 0) implies (Int[minus[0,n]]) else  Int [n]
}


/**
============================================================
																	PRED
============================================================
*/

/**
* Les intersections ne peuvent pas être confondues
*/
pred IntersectionsUniques 
{
	no i,i':Intersection | (i!=i') &&  (i.x = i'.x) && (i.y = i'.y)
}

/**
* Les receptacles ne peuvent pas être confondus
* Un receptacle ne peut pas se trouver au meme endroit que l'entrepot
*/
pred IntersectionsReceptaclesUniques 
{
	no r,r':ReceptacleAbstrait | (r!=r') && (r.i = r'.i)
}

/**
	Initialise les d.currentIntersection.t.t et d.currentCommande.t.receptacle pour tous les drones
*/
pred init [t:Time]
{
	all d:Drone | all e:Entrepot | d.currentIntersection.t.t = e.i
	all d:Drone | d.df.t = d.currentCommande.t.receptacle
}

/**
* On crée la grille d'intersections. Elle est pour l'instant de 3 par 3 
*/
pred Grille 
{
	no i:Intersection | ((i.x) < 0) || ((i.y )<0) || ((i.x)>4) || ((i.y)>4)

	IntersectionsUniques
	IntersectionsReceptaclesUniques

	init[first]

	ToutesLesCommandesSontAttribuees
	TousLesReceptaclesSontAtteignables

	VoisinDirect[first]
}


pred ToutesLesCommandesSontAttribuees
{
	all c:Commande | some d:Drone | some c': d.commandes | c=c'
}

pred TousLesReceptaclesSontAtteignables
{
	all r:ReceptacleAbstrait | some r':ReceptacleAbstrait | ((r != r')&&(absVal[minus[r.i.x,r'.i.x]]+absVal[minus[r.i.y,r'.i.y]] =< 3))
}

/**
* On prends les intersections et non pas les receptacles pour pouvoir tester l'entrepôt
* On s'assure que toutes les intersections du Drone sont voisin directs
*/
pred VoisinDirect [t:Time]
{	
	all d:Drone, e:Entrepot | ((d.cheminReceptacle.t.min = e) && (d.cheminReceptacle.t.max = d.df.t)) && ((d.cheminIntersection.t.min = e.i) && (d.cheminIntersection.t.max = d.df.t.i))
	// Distance de Manhattan entre les réceptacles
	all d:Drone | all r0,r1 : d.cheminReceptacle.t | (r1 = nextReceptacle[r0,d.cheminReceptacle.t]) implies ((r0 != r1)&&(plus[absVal[minus[r1.i.x,r0.i.x]],absVal[minus[r1.i.y,r0.i.y]]]=3))
	// Distance = 1 entre chaque intersection du cheminIntersection
	all d:Drone | all i0, i1 : d.cheminIntersection.t | (i1 = nextIntersection[i0,d.cheminIntersection.t]) implies ((i0 != i1)&&((plus[absVal[minus[i1.x,i0.x]],absVal[minus[i1.y,i0.y]]])= 1) /*&& pasDeDiagonale[i0, i1]*/)
}

pred pasDeDiagonale[i,i': Intersection]
{
	(i.x = i'.x) || (i.y = i'.y)
}

pred Deplacement [d:Drone, t,t':Time, i:Intersection]
{
	// Déplacement suivant x
	/* Précondition */
	i in d.cheminIntersection.t
	/* Postcondition */
	let ci = d.currentIntersection
	{
		(i = nextIntersection[ci.t.t, d.cheminIntersection.t] and ci.t'.t' = i)
	}
	noInternalDroneChange[t,t',d]
}

fact traces 
{
   
	Grille
    all t: Time-last | let t' = t.next
	{
		some d:Drone, i: Intersection |
		Deplacement [d, t,t', i]
	}
}

pred noInternalDroneChange[t,t':Time, d:Drone] 
{
	(d.cheminIntersection.t = d.cheminIntersection.t' and	
	 d.cheminReceptacle.t = d.cheminReceptacle.t' and 
	 d.df.t = d.df.t' and currentCommande.t = currentCommande.t')
}

pred go 
{
	//Grille
}

/**
============================================================
																	ASSERT
============================================================
*/

assert NoDistantReceptacle
{
	Grille =>	all r:ReceptacleAbstrait | some r':ReceptacleAbstrait | ((r != r')&&(absVal[minus[r.i.x,r'.i.x]]+absVal[minus[r.i.y,r'.i.y]] =< 3))
}

/**
============================================================
																	CHECK
============================================================
*/

check NoDistantReceptacle for 5 but 1 Receptacle, 1 Time , 2 Drone , 5 Int


/**
============================================================
																	RUN
============================================================
*/

run go for 5 but exactly 7 Intersection, 1 Receptacle, 4 Time ,exactly 1 Drone , 5 Int
