/*One Man's Ceiling is another Man's Floor*/

sig Plateforme{}

sig Humain //Signature: Un élèment
{
	plancher : Plateforme,
	plafond : Plateforme
}

fact I0
{
	all h0:Humain | some h1:Humain | Sous[h0,h1]
}

pred Sous[h0,h1:Humain]{h0.plafond = h1.plancher}
pred Sur[h0,h1:Humain]{h1.plafond = h0.plancher}

assert A0
{
all h0:Humain | some h1:Humain | Sous[h1,h0]  //One Man's Floor is another Man's Ceiling
}

check A0 for 2

pred Vivable 
{
	no h:Humain | h.plafond = h.plancher
}

assert A1
{
	Vivable => all h0:Humain | some h1:Humain | Sous[h1,h0]
}

check A1 for 3 //On cherche des contre-exemples sur n objets

pred Solo
{
	no h0,h1:Humain | (h0 != h1) && ((h0.plafond = h1.plafond) || (h0.plancher = h1.plancher))
}

assert A2
{
	Solo => all h0:Humain | some h1:Humain | Sous[h1,h0]
}

check A2 for 15

pred go {}
run go
