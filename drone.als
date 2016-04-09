open util/ordering[Time] as to
open util/ordering[Iterateur] as ito
open util/ordering[ReceptacleAbstrait] as ro
open util/ordering[Intersection] as io
open util/ordering[Commande] as co


/**
============================================================
																CONTRAT
============================================================
*
* Il faut autant d'itérateurs que de commandes
* Il faut un nombre de drônes inférieur ou égal au nombre de commandes
*/



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
	commande: Commande one -> Time,
	batterie: Int one -> Time
}

/**
	ReceptacleAbstrait
		implémenté par tous les Receptacles et l'entrepot.
*/
abstract sig ReceptacleAbstrait
{
	i:Intersection
}

/**
	Représente l'évolution du temps dans le programme
*/
sig Time {}

/**
	Représente une intersection, sur lesquels sont être situé les receptacles, l'entrepôt et les drônes
*/
sig Intersection 
{
	x : Int, //Abscisse
	y : Int	 //Ordonnée
}

/**
	Une commande pouvant être assigné à un drone. 
	Elle comporte pour le moment seulement le receptacle de livraison, soit le point d'arrivé de la commande
*/
sig Commande 
{
	receptacle : lone Receptacle
}

/**
	Un receptacle est l'endroit où l'on peut délivrer une livraison. 
	Il doivent tous êtres atteignables et permettent également aux drône de pouvoir recharger leurs batteries
*/
sig Receptacle extends ReceptacleAbstrait
{
}

/**
	L'entrepot est le receptacles de départ, où les drônes partent après avoir récupèrer les commandes.
	Ils y reviennent également après chaque livraisons
*/
one sig Entrepot extends ReceptacleAbstrait
{
	commandes: set Commande,
	currentCommande: commandes one -> Iterateur
}

/**
	Permet d'itérer sur les différentes commandes, au fure et à mesur de l'évolution du programme. 
	Ainsi, chaque drône aura une commande différentes des autres.
*/
sig Iterateur {}

/**
============================================================
																	FACTS
============================================================
*/

/**
	DisjointCommandSets
		Chaque commandes peut être dans un seul drône
*/
/*fact DisjointCommandSets
{
	Drone<:commandes in Drone lone-> Commande
}
*/

/**
* Gestion du temps et du déplacement.
	C'est fait principale du programme, qui va ensuite appeller toutes les autres fonctions et prédicats.
	
	But : 	
		On assigne toutes les premières commandes aux drônes, puis on lance le déplacement de chaque drône. 
**/
fact traces 
{
	Grille
	all it: Iterateur-last | let it' = it.next
	{
		some d:Drone |
		initCommandes[d, it, it']
		all t: Time-last | let t' = t.next
		{
			all d:Drone | some i: Intersection | Deplacement [d, t,t', i,it,it']
		}
	}
}

fact BatteryAlwaysBetweenZeroAndThree
{
	all d:Drone | all t:Time | d.batterie.t >= 0 and d.batterie.t <= 3
}

/**
============================================================
																	FUN
============================================================
*/

/**
	Retourne le prochain receptacle le plus proche de r
*/
fun nextReceptacle [r:ReceptacleAbstrait, rs: set ReceptacleAbstrait]: set ReceptacleAbstrait
{
	min[r.nexts & rs]
}

/**
	Retourne la prochaine intersection la plus proche de i
*/
fun nextIntersection [i:Intersection, is: set Intersection]: set Intersection
{
	min[i.nexts & is]
}

/**
	Retourne la précédente intersection la plus proche de i
*/
fun prevIntersection [i:Intersection, is: set Intersection]: set Intersection
{
	max[is & i.prevs]
}

/**
	Retourne la prochaine commande 
*/
fun nextCommande [c : Commande, cs : set Commande]: set Commande
{
	min[c.nexts & cs]
}

/**
	Retourne la valeur absolue d'un entier passé en paramètres.
*/
fun absVal [n:Int]: Int
{
	(n < 0) implies (Int[minus[0,n]]) else  Int [n]
}

/**
	Retourne la longueur du chemin passé en paramètre
*/
fun longueurCheminIntersection [is: set Intersection]: Int
{
	#is
}

/**
	Diminue de 1 la batterie d'un drone
*/
fun diminuerBatterie [d:Drone, t:Time]: Int
{
	Int[minus[d.batterie.t,1]]
}

/**
	Augmente de 1 la batterie d'un drone
*/
fun augmenterBatterie [d:Drone, t:Time]: Int
{
	Int[plus[d.batterie.t,1]]
}

/**
============================================================
																	PRED contraintes
============================================================
*/

/**
* Les intersections ne peuvent pas être confondues
*/
pred IntersectionsUniques 
{
	no i,i':Intersection | (i!=i') and  (i.x = i'.x) and (i.y = i'.y)
}


/**
* Les receptacles ne peuvent pas être confondus
* Un receptacle ne peut pas se trouver au meme endroit que l'entrepot
*/
pred IntersectionsReceptaclesUniques 
{
	no r,r':ReceptacleAbstrait | (r!=r') and (r.i = r'.i)
}

/**
	Permet d'etre certain que toutes les commandes seront attribuees a un drone
*/
/*pred ToutesLesCommandesSontAttribuees
{
	all c:Commande | some d:Drone | some c': d.commandes | c=c'
}*/

/**
	Spécifie que toutes les intersections sont situé cote à cote, et non pas en diagonale
*/
pred pasDeDiagonale[i,i': Intersection]
{
	(i.x = i'.x) || (i.y = i'.y)
}

/**
	Spécifie que toutes les commande on un receptacle existant comme point d'arrivé
*/
pred ToutesCommandesAReceptacle
{
	all c: Commande | some r: Receptacle | c.receptacle = r
}

/**
	Permet d'etre certain que tous les receptacles seront atteignables
*/
pred TousLesReceptaclesSontAtteignables
{
	all r:ReceptacleAbstrait | some r':ReceptacleAbstrait | ((r != r') and (absVal[minus[r.i.x,r'.i.x]]+absVal[minus[r.i.y,r'.i.y]] =< 3))
}

/**
============================================================
													PRED Initialisation
============================================================
*/


/**
	Initialise les d.currentIntersection.t.t et d.currentCommande.t.receptacle pour tous les drones
*/
pred init [t:Time]
{
	all d:Drone | all e:Entrepot | d.currentIntersection.t.t = e.i
	all e:Entrepot | e.currentCommande.first = e.commandes.min
	initBatterie[t]
}


/**
	Initialise les commandes pour chaque drone en prenant les premires dans la liste de commandes de l'entrepot
*/
pred initCommandes[d:Drone, it, it': Iterateur]
{
	all e:Entrepot | d.commande.first = e.currentCommande.it and e.currentCommande.it' = nextCommande[e.currentCommande.it, e.commandes]
}

/**
* On crée la grille d'intersections. Elle est pour l'instant de 3 par 3 
*/
pred Grille 
{
	no i:Intersection | ((i.x) < 0) || ((i.y )<0) || ((i.x)>4) || ((i.y)>4)
	IntersectionsUniques
	IntersectionsReceptaclesUniques
	ToutesCommandesAReceptacle
	init[first]

	//ToutesLesCommandesSontAttribuees // A mettre dans init //@Kévin : On le met pas ça sert à rien finalement
	//TousLesReceptaclesSontAtteignables

	all d:Drone | CalculChemin[first,d]
}

/**
	Initialise la valeur de chaque batterie de chaque drone
*/
pred initBatterie[t:Time]
{
	all d:Drone | d.batterie.t = 3
}

/**
============================================================
													PRED progression du programme
============================================================
*/

/**
* On prends les intersections et non pas les receptacles pour pouvoir tester l'entrepôt
* On s'assure que toutes les intersections du Drone sont voisin directs
*/
pred CalculChemin [t:Time,d:Drone]
{	
	cheminLePlusCourt[d,t]
	d.df.t = d.commande.t.receptacle
	all e:Entrepot | ((d.cheminReceptacle.t.min = e) && (d.cheminReceptacle.t.max =  d.commande.t.receptacle)) && ((d.cheminIntersection.t.min = d.cheminReceptacle.t.min.i) && (d.cheminIntersection.t.max = d.cheminReceptacle.t.max.i))
	// Distance de Manhattan entre les réceptacles
	all r0,r1 : d.cheminReceptacle.t | (r1 = nextReceptacle[r0,d.cheminReceptacle.t]) implies ((r0 != r1)&&(plus[absVal[minus[r1.i.x,r0.i.x]],absVal[minus[r1.i.y,r0.i.y]]]=2))
	// Distance = 1 entre chaque intersection du cheminIntersection
	all i0, i1 : d.cheminIntersection.t | (i1 = nextIntersection[i0,d.cheminIntersection.t]) implies ((i0 != i1)&&((plus[absVal[minus[i1.x,i0.x]],absVal[minus[i1.y,i0.y]]])= 1) /*&& pasDeDiagonale[i0, i1]*/)
}


pred Deplacement [d:Drone, t,t':Time, inter:Intersection, it,it':Iterateur]
{
	// Déplacement suivant x
	/* Précondition */
	inter in d.cheminIntersection.t

	/* Postcondition */
	let ci = d.currentIntersection
	{
			//Si on peut, on recharge jusqu'à pleine charge
			(rechargementPossible[d,t] and no d2: Drone | intersectionOccupee[d,d2,t,t']) implies (ci.t'.t' = ci.t.t and d.df.t' = d.df.t and d.batterie.t' = augmenterBatterie[d,t] and noInternalDroneChange[t,t',d])
			//On se déplace vers la livraison
			(peutAvancer[d, t, t']  and no d2: Drone | intersectionOccupee[d,d2,t,t']) implies (inter = nextIntersection[ci.t.t, d.cheminIntersection.t] and ci.t'.t' = inter and d.df.t' = d.df.t and d.batterie.t' = diminuerBatterie[d,t] and noInternalDroneChange[t,t',d])
			//Ou on rentre à l'entrepôt
			(peutReculer[d, t, t'] and no d2: Drone | intersectionOccupee[d,d2,t,t']) implies (inter = prevIntersection[ci.t.t, d.cheminIntersection.t] and ci.t'.t' = inter and d.df.t' = d.df.t and d.batterie.t' = diminuerBatterie[d,t] and noInternalDroneChange[t,t',d])
			//Ou on fait demi-tour, mais seulement une fois chargé. On ne bouge pas pendant le demi-tour (il y a un temps de livraison de 1 unité de temps)!!
			all e:Entrepot | ((d.batterie.t = 3 and ci.t.t = d.df.t.i ) and no d2: Drone | intersectionOccupee[d,d2,t,t']) implies (d.df.t' = e and ci.t'.t'=ci.t.t and d.batterie.t' = d.batterie.t and noInternalDroneChange[t,t',d])
			// Ou attente
			(some d2: Drone | intersectionOccupee[d,d2,t,t']) implies (Attente[d,t,t'] and noInternalDroneChange[t,t',d])
			//Ou on récupère une nouvelle commande
			all e:Entrepot | (d.batterie.t = 3 && d.df.t = d.cheminReceptacle.t.min && ci.t.t = d.df.t.i) implies (ci.t'.t' = ci.t.t and d.batterie.t' = d.batterie.t and nouveauColis[d, t',it,it',e])
	}
}

pred nouveauColis[d:Drone, t':Time, it,it':Iterateur, e:Entrepot]
{
	let nouvelleCommande =  nextCommande[e.currentCommande.it,e.commandes]
	{
		d.commande.t' =  nouvelleCommande and e.currentCommande.it' = nextCommande[e.currentCommande.it,e.commandes]
		d.df.t' = nouvelleCommande.receptacle
		let deb = e.i
		{
			let fin = nouvelleCommande.receptacle.i
			{
				minus[longueurCheminIntersection[d.cheminIntersection.first],1] = plus[absVal[minus[deb.x,fin.x]],absVal[minus[deb.y,fin.y]]]
			}
		}
		((d.cheminReceptacle.t'.min = e) && (d.cheminReceptacle.t'.max =  nouvelleCommande.receptacle)) && ((d.cheminIntersection.t'.min = e.i) && (d.cheminIntersection.t'.max = nouvelleCommande.receptacle.i))
		// Distance de Manhattan entre les réceptacles
		all r0,r1 : d.cheminReceptacle.t' | (r1 = nextReceptacle[r0,d.cheminReceptacle.t']) implies ((r0 != r1)&&(plus[absVal[minus[r1.i.x,r0.i.x]],absVal[minus[r1.i.y,r0.i.y]]]=2))
		// Distance = 1 entre chaque intersection du cheminIntersection
		all i0, i1 : d.cheminIntersection.t' | (i1 = nextIntersection[i0,d.cheminIntersection.t']) implies ((i0 != i1)&&((plus[absVal[minus[i1.x,i0.x]],absVal[minus[i1.y,i0.y]]])= 1))
	}
}

/**
	Spécifie que rien ne change entre le temps t et t' dans un drone. 
*/
pred peutAvancer[d:Drone, t,t':Time]
{
	let ci = d.currentIntersection
	{
		(not rechargementPossible[d,t]) and d.df.t = d.cheminReceptacle.t.max and ci.t.t != d.df.t.i
	}
}

pred peutReculer[d:Drone, t,t':Time]
{
	let ci = d.currentIntersection
	{
		(not rechargementPossible[d,t]) and d.df.t = d.cheminReceptacle.t.min and ci.t.t != d.df.t.i
	}
}

// La prochaine intersection envisagé au temps t
pred intersectionOccupee[d,d2: Drone, t,t': Time]
{
// TODO attention pour le retour : prevIntersection
	(d != d2) // Les deux drones ne sont pas les mêmes
	and
	(
		(all entrepot : Entrepot | d.df.t != entrepot)
		implies
		(
			(
				let nextInter = nextIntersection[d.currentIntersection.t.t, d.cheminIntersection.t]
				{
					nextInter = nextIntersection[d2.currentIntersection.t.t, d2.cheminIntersection.t] // La prochaine intersection des deux drones est la même
					and nextInter = d2.currentIntersection.t'.t' // et cette prochaine intersection est  déjà la prochaine (choisie comme déplacement définitif) de l'autre drone
					and no interEntrepot : Entrepot.i | (nextInter = interEntrepot) // et ce n'est pas l'entrepot
				}
			)
			or
			(
				let nextInter = nextIntersection[d.currentIntersection.t.t, d.cheminIntersection.t]
				{
					nextInter = d2.currentIntersection.t.t // Drone va là où il y a un autre drone
					and
					(
						rechargementPossible[d2, t] // l'autre se recharge
						or
						d2.df.t != d2.df.t' // l'autre livre (et change ça df)
					)
					and rechargementImpossible[d, t]
					and no interEntrepot : Entrepot.i | (nextInter = interEntrepot) // et ce n'est pas l'entrepot
				}
			)
		)
		else // La même chose pour le retour
		(
			(
				let prevInter = prevIntersection[d.currentIntersection.t.t, d.cheminIntersection.t]
				{
					prevInter = prevIntersection[d2.currentIntersection.t.t, d2.cheminIntersection.t] // La prochaine intersection des deux drones est la même
					and prevInter = d2.currentIntersection.t'.t' // et cette prochaine intersection est  déjà la prochaine (choisie comme déplacement définitif) de l'autre drone
					and no interEntrepot : Entrepot.i | (prevInter = interEntrepot) // et ce n'est pas l'entrepot
				}
			)
			or
			(
				let prevInter = prevIntersection[d.currentIntersection.t.t, d.cheminIntersection.t]
				{
					prevInter = d2.currentIntersection.t.t // Drone va là où il y a un autre drone
					and
					(
						rechargementPossible[d2, t] // l'autre se recharge
						or
						d2.df.t != d2.df.t' // l'autre livre (et change ça df)
					)
					and rechargementImpossible[d, t]
					and no interEntrepot : Entrepot.i | (prevInter = interEntrepot) // et ce n'est pas l'entrepot
				}
			)
		)
	)
}

pred Attente[d:Drone, t,t': Time]
{
	d.currentIntersection.t'.t' = d.currentIntersection.t.t and d.df.t' = d.df.t and d.batterie.t' = d.batterie.t
}

pred noInternalDroneChange[t,t':Time, d:Drone] 
{
	(d.cheminIntersection.t = d.cheminIntersection.t' and	
	 d.cheminReceptacle.t = d.cheminReceptacle.t' and
	 d.commande.t = d.commande.t' )
}

/**
	Calcul le chemin le plus court entre l'entrepot (d.cheminReceptacle.t.min) et la destination du drone (d.cheminReceptacle.t.max), pour savoir par où le drone 
	va passé pour faire sa livraison
*/
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
	Vérifie si le drone peut actuellement se recharger, en fonction de la position où il se trouve. 
	
	Un drone peut se recharger que si il se trouve à l'entrepot ou sur un receptacle et que ça batterie est inférieur à 3
*/
pred rechargementPossible [d:Drone, t:Time]
{
		let ci = d.currentIntersection
	{
		some ie : Entrepot.i, ir : Receptacle.i| ((ci.t.t= ie or ci.t.t= ir) and d.batterie.t <3)
	}
}

/**
	
*/
pred rechargementImpossible [d:Drone, t:Time]
{
		let ci = d.currentIntersection
	{
		no ie : Entrepot.i, ir : Receptacle.i| ((ci.t.t= ie or ci.t.t= ir) or d.batterie.t >=3)
	}
}

/**
	Verification de la batterie pour analyser si le deplacement vers la destination est possible
	Pour l'instant on souhaite recharger la batterie a son maximum avant de partir du receptacle
*/
pred NotEnoughBattery[d:Drone, currentInter:Intersection, destFinale:Intersection, t:Time]
{
	(currentInter != destFinale) && ((plus[ absVal[ minus[destFinale.x, currentInter.x] ], absVal[ minus[destFinale.y, currentInter.y] ] ]) > d.batterie.t) //&& (b.currentValue.t != 3)
}

pred go {}

/**
============================================================
																	ASSERT
============================================================
*/

assert NoDistantReceptacle
{
	Grille =>	all r:ReceptacleAbstrait | some r':ReceptacleAbstrait | ((r != r') and (absVal[minus[r.i.x,r'.i.x]]+absVal[minus[r.i.y,r'.i.y]] =< 3))
}

assert BatteryAlwaysBetweenZeroAndThree
{
	all d:Drone | all t:Time | d.batterie.t >= 0 and d.batterie.t <= 3
}

/**
============================================================
																	CHECK
============================================================
*/

check NoDistantReceptacle for 5 but 1 Receptacle, 1 Time , 2 Drone , 3 Int
check BatteryAlwaysBetweenZeroAndThree for 5 but exactly 5 Intersection, 1 Receptacle, 2 Commande, 10 Time, exactly 1 Drone, 5 Int

/**
============================================================
																	RUN
============================================================
*/

run go for 5 but exactly 5 Intersection, 2 Receptacle, exactly 6 Commande, 14 Time ,exactly 2 Drone , 6 Int, exactly 3 Iterateur
