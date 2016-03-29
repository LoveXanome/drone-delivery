abstract sig S
{
	x : Int, //Abscisse
	y : Int	 //Ordonnée
}

one sig A extends S 
{
}

one sig B extends S 
{
}

fun absVal [n:Int]: Int
{
	(n < 0) implies (Int[minus[0,n]]) else  Int [n]
}

assert A0
{
	all a:A, b:B | (a.x = 0) && (a.y = 3) && (b.y = 0) && (b.x = 3) =>(	absVal[a.x - b.x]+absVal[a.y - b.y] = 6)
}

check A0 for 5

assert A1
{
	absVal[-2] = 2
}

check A1 for 2
