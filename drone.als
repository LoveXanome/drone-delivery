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
		batterie : la batterie associee au drone
*/
sig Drone 
{
	cheminIntersection: set Intersection -> Time,//Chemin
	currentIntersection: cheminIntersection one -> Time, 
	cheminReceptacle: set ReceptacleAbstrait -> Time,
	df: ReceptacleAbstrait -> Time, //Destination finale
	
	commandes: set Commande,
	currentCommande: commandes one -> Time,

	batterie: Batterie,
}

/**
	Batterie :
		Possede une valeur courante changeant avec le temps (currentalue) et une valeur maximum (maxValue)
*/
sig Batterie
{
	currentValue: Int one -> Time,
	maxValue: Int
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
* Gestion du temps et du déplacement
**/
fact traces 
{
   
	Grille
    all t: Time-last | let t' = t.next
	{
		some d:Drone | some i: Intersection |
		Deplacement [d, t,t', i]
	}
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

fun prevIntersection [i:Intersection, is: set Intersection]: set Intersection
{
	max[is & i.prevs]
}

fun absVal [n:Int]: Int
{
	(n < 0) implies (Int[minus[0,n]]) else  Int [n]
}

fun longueurCheminIntersection [is: set Intersection]: Int
{
	#is
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
	initBatterie[t]
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

	ToutesLesCommandesSontAttribuees // A mettre dans init
	TousLesReceptaclesSontAtteignables

	CalculChemin[first]
}

/**
	Permet d'etre certain que toutes les commandes seront attribuees a un drone
*/
pred ToutesLesCommandesSontAttribuees
{
	all c:Commande | some d:Drone | some c': d.commandes | c=c'
}

/**
	Permet d'etre certain que toutes les batteries seront associees a un drone
*/
pred ToutesLesBatteriesSontAssociees
{
	all b:Batterie | some d:Drone | some b': d.batterie | b = b'
}

/**
	Permet d'etre certain que tous les receptacles seront atteignables
*/
pred TousLesReceptaclesSontAtteignables
{
	all r:ReceptacleAbstrait | some r':ReceptacleAbstrait | ((r != r')&&(absVal[minus[r.i.x,r'.i.x]]+absVal[minus[r.i.y,r'.i.y]] =< 3))
}

/**
* On prends les intersections et non pas les receptacles pour pouvoir tester l'entrepôt
* On s'assure que toutes les intersections du Drone sont voisin directs
*/
pred CalculChemin [t:Time]
{	
	all d:Drone | cheminLePlusCourt[d,t]
	all d:Drone | d.df.t = d.currentCommande.t.receptacle
	all d:Drone, e:Entrepot | ((d.cheminReceptacle.t.min = e) && (d.cheminReceptacle.t.max =  d.currentCommande.t.receptacle)) && ((d.cheminIntersection.t.min = d.cheminReceptacle.t.min.i) && (d.cheminIntersection.t.max = d.cheminReceptacle.t.max.i))
	// Distance de Manhattan entre les réceptacles
	all d:Drone | all r0,r1 : d.cheminReceptacle.t | (r1 = nextReceptacle[r0,d.cheminReceptacle.t]) implies ((r0 != r1)&&(plus[absVal[minus[r1.i.x,r0.i.x]],absVal[minus[r1.i.y,r0.i.y]]]=2))
	// Distance = 1 entre chaque intersection du cheminIntersection
	all d:Drone | all i0, i1 : d.cheminIntersection.t | (i1 = nextIntersection[i0,d.cheminIntersection.t]) implies ((i0 != i1)&&((plus[absVal[minus[i1.x,i0.x]],absVal[minus[i1.y,i0.y]]])= 1) /*&& pasDeDiagonale[i0, i1]*/)
}

pred pasDeDiagonale[i,i': Intersection]
{
	(i.x = i'.x) || (i.y = i'.y)
}

pred Deplacement [d:Drone, t,t':Time, inter:Intersection]
{
	// Déplacement suivant x
	/* Précondition */
	inter in d.cheminIntersection.t
	/* Postcondition */
	let ci = d.currentIntersection
	{
		((all interReceptacleAbstrait:ReceptacleAbstrait.i | ci.t.t = interReceptacleAbstrait) && (NotEnoughBattery[d.batterie, d.currentIntersection.t.t, d.df.t.i, t])) implies ReloadBattery[d,t,t']
		else {
		//On se déplace vers la livraison
		(d.df.t = d.cheminReceptacle.t.max && ci.t.t != d.df.t.i) implies (inter = nextIntersection[ci.t.t, d.cheminIntersection.t] and ci.t'.t' = inter and d.df.t' = d.df.t)
		//Ou on rentre à l'entrepôt
		(d.df.t = d.cheminReceptacle.t.min && ci.t.t != d.df.t.i) implies (inter = prevIntersection[ci.t.t, d.cheminIntersection.t] and ci.t'.t' = inter and d.df.t' = d.df.t)
		//Ou on fait demi-tour. On ne bouge pas pendant le demi-tour (il y a un temps de livraison de 1 unité de temps)!!
		all e:Entrepot | (ci.t.t = d.df.t.i) implies (d.df.t' = e and ci.t'.t'=ci.t.t)
		usingEnergy[d, t, t']
		}
	}
	noInternalDroneChange[t,t',d]
}

pred noInternalDroneChange[t,t':Time, d:Drone] 
{
	(d.cheminIntersection.t = d.cheminIntersection.t' and	
	 d.cheminReceptacle.t = d.cheminReceptacle.t' and
	 currentCommande.t = currentCommande.t')
}

pred cheminLePlusCourt[d:Drone, t:Time]
{
	let deb = d.cheminReceptacle.t.min.i
	{
		let fin = d.cheminReceptacle.t.max.i
		{
			minus[longueurCheminIntersection[d.cheminIntersection.first],1] = plus[absVal[minus[deb.x,fin.x]],absVal[minus[deb.y,fin.y]]]
		}
	}
}

/**
	Initialise la valeur de chaque batterie de chaque drone
*/
pred initBatterie[t:Time]
{
	ToutesLesBatteriesSontAssociees
	all d:Drone | d.batterie.maxValue = 3
	all d:Drone | d.batterie.currentValue.t = d.batterie.maxValue
}

/**
	Le processus de deplacement engendre une baisse de la batterie mais cette valeur ne peut jamais etre negative
*/
pred usingEnergy[d:Drone, t,t': Time]
{
	let oldBatteryValue = d.batterie.currentValue
	{
		(oldBatteryValue.t > 0) implies (oldBatteryValue.t' = minus[oldBatteryValue.t, 1])
		else oldBatteryValue.t' = oldBatteryValue.t
	}
}

/**
	Verification de la batterie pour analyser si le deplacement vers la destination est possible
	Pour l'instant on souhaite recharger la batterie a son maximum avant de partir du receptacle
*/
pred NotEnoughBattery[b:Batterie, currentInter:Intersection, destFinale:Intersection, t:Time]
{
	(currentInter != destFinale) && ((plus[absVal[minus[destFinale.x, currentInter.x]], absVal[minus[destFinale.y, currentInter.y]]]) > 3) && (b.currentValue.t != 3)
}

/**
	Rechargement de la batterie : une unite de temps pour une unite de batterie lorsque le drone se trouve sur l'entrepot ou un
	quelconque receptacle
*/
pred ReloadBattery[d:Drone, t,t':Time]
{
	let oldBatteryValue = d.batterie.currentValue
	{
		(oldBatteryValue.t < 3) implies (oldBatteryValue.t' = plus[oldBatteryValue.t, 1])
		else oldBatteryValue.t' = oldBatteryValue.t
	}
}

pred go {}

/**
============================================================
																	ASSERT
============================================================
*/

assert NoDistantReceptacle
{
	Grille =>	all r:ReceptacleAbstrait | some r':ReceptacleAbstrait | ((r != r')&&(absVal[minus[r.i.x,r'.i.x]]+absVal[minus[r.i.y,r'.i.y]] =< 3))
}

assert NoBatteryBelowZero
{
	all b:Batterie | all t:Time | b.currentValue.t >= 0
}

/**
============================================================
																	CHECK
============================================================
*/

check NoDistantReceptacle for 5 but 1 Receptacle, 1 Time , 2 Drone , 3 Int
check NoBatteryBelowZero for 5 but exactly 5 Intersection, 1 Receptacle, 2 Commande, 10 Time, exactly 1 Drone , 5 Int

/**
============================================================
																	RUN
============================================================
*/

run go for 5 but exactly 5 Intersection, exactly 2 Receptacle, 1 Commande, 10 Time, exactly 1 Drone , 5 Int
