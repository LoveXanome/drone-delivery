open util/ordering[Time] as to
open util/ordering[Intersection] as io

sig Drone 
{
	ic: Intersection, //Intersection courante
	chemin: set Intersection,//Chemin
	df: Intersection, //Destination finale
	currentDest: chemin one -> Time
}
sig Receptacle 
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

one sig Entrepot
{
	i:Intersection
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
*/
pred IntersectionsReceptaclesUniques 
{
	no r,r':Receptacle | (r!=r') && (r.i = r'.i)
	no r:Receptacle, e:Entrepot | (r.i = e.i)
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
}

fun nextKey [i:Intersection, is: set Intersection]: set Intersection
{
	min[i.nexts & is]
}

fun absVal [n:Int]: Int
{
	(n < 0) implies (Int[0-n]) else  Int [n]
}

/*
* On prends les intersections et non pas les receptacles pour pouvoir tester l'entrepôt
* On s'assure que toutes les intersections du Drone sont voisin directs
*/
pred VoisinDirect
{	
	all d:Drone, e:Entrepot |((d.chemin.min = e.i) && (d.chemin.max = d.df))
	all d:Drone | all i0,i1 : d.chemin | (i1 = nextKey[i0,d.chemin]) implies ((i0 != i1)&&(absVal[i1.x - i0.x]+absVal[i1.y - i0.y] =< 3)) //Distance de Manhattan
	//all d:Drone | all i2:d.chemin | some r:Receptacle | (i2=r.i)
}

pred Deplacement [d:Drone, t,t':Time]
{
	
}


pred go 
{
	Grille
}
run go for 10 but 1 Time, 4 Drone , 5 Int
