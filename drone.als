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


/* Informations utiles:
- 18 Time ~> 1min20 de generation

- Affichage conseillé :

* Activer Magic Layout -> Yes
* Projection over Time & Iterateur
* Theme ->
		* $ToutesLesCommandesAReceptacle -> Show as arcs : OFF
		* batterie -> Show as arcs : OFF & Show as attribute : ON
		* x -> Show as arcs : OFF & Show as attribute : ON
		* y -> Show as arcs : OFF & Show as attribute : ON
	* Apply
	* Close
*/

/**
============================================================
																	SIGS
============================================================
*/

/**
	Le drone 
	relations : 
		cheminIntersection : liste de toutes les intersections par lesquelles va passer le drone pour livrer une commande
			On passe à l'intersection suivante en fonction du temps
		currentIntersection : l'intersection actuelle du drone
		cheminReceptacle : liste de tous les réceptacles par lequel va passer le drone pour livrer une commande
		df : la destination finale de la commande
		batterie : la batterie associée au drone
*/
sig Drone 
{
	cheminIntersection: set Intersection -> Time, //Chemin
	currentIntersection: cheminIntersection one -> Time, 
	cheminReceptacle: set ReceptacleAbstrait -> Time,
	df: ReceptacleAbstrait -> Time, //Destination finale
	commande: Commande one -> Time,
	batterie: Int one -> Time
}

/**
	ReceptacleAbstrait
		hérité par les receptacles et l'entrepot.
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
	Représente une intersection, sur laquelle peut être situé un receptacle, l'entrepôt et un drône
*/
sig Intersection 
{
	x : Int, //Abscisse
	y : Int	 //Ordonnée
}

/**
	Une commande pouvant être assignée à un drone. 
	Elle comporte le receptacle de livraison, soit le point d'arrivé de la commande
*/
sig Commande 
{
	receptacle : lone Receptacle
}

/**
	Un receptacle est l'endroit où l'on peut délivrer une livraison. 
	Il doivent tous être atteignables et permettent également aux drones de pouvoir recharger leur batterie
*/
sig Receptacle extends ReceptacleAbstrait
{
}

/**
	L'entrepôt est le receptacles de départ, où les drônes partent après avoir récupéré les commandes.
	Ils y reviennent également après chaque livraison
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
* Gestion du temps et du déplacement : progression
	C'est le fait principal du programme, qui va utiliser tous les autres prédicats et fonctions.
	
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


// Nous n'avons pas d'autres faits car nous assurons la cohérence du système par la progression. Cela nous a, entre autres, facilité le debug

/**
============================================================
													PRED Initialisation
============================================================
*/

/**
* Création de la grille d'intersections. Elle est pour l'instant de 3 par 3 
*/
pred Grille 
{
	no i:Intersection | ((i.x) < 0) || ((i.y) < 0) || ((i.x) > 4) || ((i.y) > 4)
	IntersectionsUniques
	IntersectionsReceptaclesUniques
	ToutesCommandesAReceptacle
	init[first]

	all d:Drone | CalculChemin[first,d]
}

/**
	Initialise les positions de départs des drones ainsi que les commandes de l'entrepôt
*/
pred init [t:Time]
{
	all d:Drone | all e:Entrepot | d.currentIntersection.t.t = e.i
	all e:Entrepot | e.currentCommande.first = e.commandes.min
	initBatterie[t]
}

/**
	Initialise la valeur des batteries des drones
*/
pred initBatterie[t:Time]
{
	all d:Drone | d.batterie.t = 3
}

/**
	Initialise les commandes pour chaque drone en prenant les premiers dans la liste de commandes de l'entrepot
*/
pred initCommandes[d:Drone, it, it': Iterateur]
{
	all e:Entrepot | d.commande.first = e.currentCommande.it and e.currentCommande.it' = nextCommande[e.currentCommande.it, e.commandes]
}

/**
============================================================
													PRED progression du programme
============================================================
*/

/**
* Calcul tous les chemins des drones
* On s'assure que toutes les intersections du drone sont voisins directs
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

/**
	Calcule le chemin le plus court entre l'entrepot (d.cheminReceptacle.t.min) et la destination du drone (d.cheminReceptacle.t.max), pour savoir par où le drone 
	va passer pour faire sa livraison
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
	Réalise le déplacement d'un drone entre deux moments
*/
pred Deplacement [d:Drone, t,t':Time, inter:Intersection, it,it':Iterateur]
{
	/* Précondition */
	inter in d.cheminIntersection.t

	/* Postcondition */
	// Note : chaque ligne ci-dessous s'exclue mutuellement, nous ayant facilité le debug des conditions invalides
	let ci = d.currentIntersection
	{
			// Si on peut, on recharge jusqu'à pleine charge
			(rechargementPossible[d,t] and (no d2:Drone | intersectionOccupee[d,d2,t,t'])) implies (ci.t'.t' = ci.t.t and d.df.t' = d.df.t and d.batterie.t' = augmenterBatterie[d,t] and noInternalDroneChange[t,t',d])
			// On se déplace vers la livraison
			(peutAvancer[d, t, t'] and (no d2:Drone | intersectionOccupee[d,d2,t,t'])) implies (inter = nextIntersection[ci.t.t, d.cheminIntersection.t] and ci.t'.t' = inter and d.df.t' = d.df.t and d.batterie.t' = diminuerBatterie[d,t] and noInternalDroneChange[t,t',d])
			// Ou on rentre à l'entrepôt
			(peutReculer[d, t, t'] and (no d2:Drone | intersectionOccupee[d,d2,t,t'])) implies (inter = prevIntersection[ci.t.t, d.cheminIntersection.t] and ci.t'.t' = inter and d.df.t' = d.df.t and d.batterie.t' = diminuerBatterie[d,t] and noInternalDroneChange[t,t',d])
			// Ou on fait demi-tour, mais seulement une fois chargé. On ne bouge pas pendant le demi-tour (il y a un temps de livraison de 1 unité de temps)!!
			all e:Entrepot | (d.batterie.t = 3 and ci.t.t = d.df.t.i and d.df.t = d.cheminReceptacle.t.max and (no d2:Drone | intersectionOccupee[d,d2,t,t'])) implies (d.df.t' = e and ci.t'.t'=ci.t.t and d.batterie.t' = d.batterie.t and noInternalDroneChange[t,t',d])
			// Ou attente
			(some d2: Drone | intersectionOccupee[d,d2,t,t']) implies (Attente[d,t,t'] and noInternalDroneChange[t,t',d])
			// Ou on récupère une nouvelle commande
			all e:Entrepot | (d.batterie.t = 3 and d.df.t = d.cheminReceptacle.t.min and ci.t.t = d.df.t.i and (no d2:Drone | intersectionOccupee[d,d2,t,t'])) implies (ci.t'.t' = ci.t.t and d.batterie.t' = d.batterie.t and nouveauColis[d, t',it,it',e])
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

/**
	Vérifie si l'intersection suivante est occupée
*/
pred intersectionOccupee[d,d2: Drone, t,t': Time]
{
	(d != d2) // Les deux drones ne sont pas les mêmes
	and
	(
		(all entrepot : Entrepot | d.df.t != entrepot) implies // Si le drone avance vers une commande : on gère les 'next' intersections
		(
			(
				let nextInter = nextIntersection[d.currentIntersection.t.t, d.cheminIntersection.t]
				{
					nextInter = nextIntersection[d2.currentIntersection.t.t, d2.cheminIntersection.t] // La prochaine intersection des deux drones est la même
					and nextInter = d2.currentIntersection.t'.t' // et cette prochaine intersection est déjà la prochaine (choisie comme déplacement définitif) de l'autre drone
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
						d2.df.t != d2.df.t' // ou il livre (et change ça df = destination finale)
					)
					and rechargementImpossible[d, t] // et le drone actuel ne va pas rester sur place pour se recharger
					and no interEntrepot : Entrepot.i | (nextInter = interEntrepot) // et ce n'est pas l'entrepot
				}
			)
		)

		else // Sinon on traite le retour à l'entrepôt
		(
			(
				let prevInter = prevIntersection[d.currentIntersection.t.t, d.cheminIntersection.t]
				{
					prevInter = prevIntersection[d2.currentIntersection.t.t, d2.cheminIntersection.t] // La prochaine intersection des deux drones est la même
					and prevInter = d2.currentIntersection.t'.t' // et cette prochaine intersection est déjà la prochaine (choisie comme déplacement définitif) de l'autre drone
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
						d2.df.t != d2.df.t' // il livre (et change ça df (destination finale))
					)
					and rechargementImpossible[d, t] // et le drone actuel ne va pas se recharger
					and no interEntrepot : Entrepot.i | (prevInter = interEntrepot) // et ce n'est pas l'entrepot
				}
			)
		)
	)
}

/**
	Le drone attend.
	Sa position courante, sa destination finale et sa batterie ne change donc pas.
*/
pred Attente[d:Drone, t,t': Time]
{
	d.currentIntersection.t'.t' = d.currentIntersection.t.t and d.df.t' = d.df.t and d.batterie.t' = d.batterie.t
}

/**
	Les informations (qui ne changent pas à tous les tours) du drone restent pareil.
	(le chemin d'intersection, le chemain de réceptacle et la commande traitée)
*/
pred noInternalDroneChange[t,t':Time, d:Drone] 
{
	(d.cheminIntersection.t = d.cheminIntersection.t' and	
	 d.cheminReceptacle.t = d.cheminReceptacle.t' and
	 d.commande.t = d.commande.t' )
}

/**
	Vérifie si le drone peut actuellement se recharger en fonction de la position où il se trouve
	Un drone peut se recharger que s'il se trouve à l'entrepôt ou sur un receptacle et que sa batterie est inférieure à 3
*/
pred rechargementPossible [d:Drone, t:Time]
{
		let ci = d.currentIntersection
	{
		some ie : Entrepot.i, ir : Receptacle.i| ((ci.t.t= ie or ci.t.t= ir) and d.batterie.t <3)
	}
}

/**
	Vérifie si un drone ne peut pas se recharger
	Il est donc pas sur un entrepôt ou un receptacle, et sa batterie n'est pas inférieure à 3
*/
pred rechargementImpossible [d:Drone, t:Time]
{
		let ci = d.currentIntersection
	{
		no ie : Entrepot.i, ir : Receptacle.i| ((ci.t.t= ie or ci.t.t= ir) or d.batterie.t >=3)
	}
}

pred go {}

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
* Un receptacle ne peut pas se trouver au même endroit que l'entrepôt
*/
pred IntersectionsReceptaclesUniques 
{
	no r,r':ReceptacleAbstrait | (r!=r') and (r.i = r'.i)
}

/**
	Spécifie que toutes les intersections sont situé côte à côte, et non pas en diagonale
*/
pred pasDeDiagonale[i,i': Intersection]
{
	(i.x = i'.x) || (i.y = i'.y)
}

/**
	Spécifie que toutes les commandes ont un receptacle existant comme point d'arrivé
*/
pred ToutesCommandesAReceptacle
{
	all c: Commande | some r: Receptacle | c.receptacle = r
}

/**
	Permet d'être certain que tous les receptacles seront atteignables
*/
pred TousLesReceptaclesSontAtteignables
{
	all r:ReceptacleAbstrait | some r':ReceptacleAbstrait | ((r != r') and (absVal[minus[r.i.x,r'.i.x]]+absVal[minus[r.i.y,r'.i.y]] =< 3))
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
	Retourne l'intersection précédente la plus proche de i
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
	Retourne la valeur absolue d'un entier passé en paramètre.
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

check NoDistantReceptacle for 5 but exactly 5 Intersection, 2 Receptacle, exactly 6 Commande,13 Time ,exactly 2 Drone , 6 Int, exactly 3 Iterateur
check BatteryAlwaysBetweenZeroAndThree for  5 but exactly 5 Intersection, 2 Receptacle, exactly 6 Commande,13 Time ,exactly 2 Drone , 6 Int, exactly 3 Iterateur


/**
============================================================
																	RUN
============================================================
*/

run go for 5 but exactly 5 Intersection, 2 Receptacle, exactly 4 Commande, 19 Time, exactly 2 Drone, 6 Int, exactly 2 Iterateur
//run go for 5 but exactly 5 Intersection, 1 Receptacle, exactly 4 Commande, exactly 2 Iterateur, exactly 2 Drone, 6 Int, 16 Time

