open util/ordering[Time] as to
open util/ordering[ReceptacleAbstrait] as io

sig Drone 
{
	ic: Intersection, //Intersection courante
	chemin: set ReceptacleAbstrait,//Chemin
	df: Receptacle, //Destination finale
	currentDest: chemin one -> Time
}

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


/*
* Les intersections ne peuvent pas être confondues
*/
pred IntersectionsUniques 
{
	no i,i':Intersection |(i!=i') &&  (i.x = i'.x) && (i.y = i'.y)
}

/*
* Les receptacles ne peuvent pas être confondus
* Un receptacle ne peut pas se trouver au meme endroit que l'entrepot
*/
pred IntersectionsReceptaclesUniques 
{
	no r,r':ReceptacleAbstrait | (r!=r') && (r.i = r'.i)
}


pred init [d:Drone]
{
	d.ic = d.chemin.min.i
}

/*
* On crée la grille d'intersections
*/
pred Grille 
{
	//#Intersection = 9
	no i:Intersection | ((i.x) < 0) || ((i.y )<0) || ((i.x)>3) || ((i.y)>3)
	IntersectionsUniques
	IntersectionsReceptaclesUniques
	VoisinDirect
	all d:Drone | init[d]
}

fun nextKey [r:ReceptacleAbstrait, rs: set ReceptacleAbstrait]: set ReceptacleAbstrait
{
	min[r.nexts & rs]
}

fun absVal [n:Int]: Int
{
	(n < 0) implies (Int[minus[0,n]]) else  Int [n]
}

/*
* On prends les intersections et non pas les receptacles pour pouvoir tester l'entrepôt
* On s'assure que toutes les intersections du Drone sont voisin directs
*/
pred VoisinDirect
{	
	all d:Drone, e:Entrepot |((d.chemin.min = e) && (d.chemin.max = d.df))
	all d:Drone | all r0,r1 : d.chemin | (r1 = nextKey[r0,d.chemin]) implies ((r0 != r1)&&(absVal[minus[r1.i.x,r0.i.x]]+absVal[minus[r1.i.y,r0.i.y]]=< 3)) //Distance de Manhattan
	//all d:Drone | all i2:d.chemin | some r:Receptacle | (i2=r.i)
}

assert NoDistantReceptacle
{
	Grille =>	all r:ReceptacleAbstrait | some r':ReceptacleAbstrait | ((r != r')&&(absVal[minus[r.i.x,r'.i.x]]+absVal[minus[r.i.y,r'.i.y]] =< 3))
}

check NoDistantReceptacle for 5 but exactly 1 Receptacle, 1 Time ,exactly 2 Drone , 5 Int

pred Deplacement [d:Drone, t,t':Time]
{
	
}


pred go 
{
	Grille
}
run go for 10 but 1 Time ,4 Drone , 5 Int
