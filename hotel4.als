open util/ordering[Time] as to
open util/ordering[Key] as ko

sig Key {}
sig Time {}

sig Room 
{
	keys: set Key,
	currentKey: keys one -> Time
}

fact DisjointKeySets 
{
	-- each key belongs to at most one room
	Room<:keys   in   Room lone-> Key
}

one sig FrontDesk 
{
	lastKey: (Room -> Key) -> Time,
	occupant: (Room -> Guest) -> Time
}

sig Guest 
{
	keys: Key -> Time
}

fun nextKey [k: Key, ks: set Key]: set Key 
{
	min [k.nexts & ks]
}

pred init [t: Time] 
{
	no Guest.keys.t
	no FrontDesk.occupant.t
	all r: Room | FrontDesk.lastKey.t [r] = r.currentKey.t
}

pred entry [t, t': Time, g: Guest, r: Room, k: Key] 
{
	/*Précondition:*/
    k in g.keys.t
    /*Postcondition:*/
	let ck = r.currentKey 
    {
       /*La clé de la carte est la clé de la chambre:*/
		(k = ck.t and ck.t' = ck.t) or 
       /*La clé de la carte est la prochaine clé de la chambre:*/
		(k = nextKey[ck.t, r.keys] and ck.t' = k)
    }
    /*Ce qui du système doit rester inchangé durant cette opération:*/
	noRoomChangeExcept [t, t', r]
	noGuestChangeExcept [t, t', none]
	noFrontDeskChange [t, t']
}

pred noFrontDeskChange [t, t': Time] 
{
	FrontDesk.lastKey.t = FrontDesk.lastKey.t'
	FrontDesk.occupant.t = FrontDesk.occupant.t'
}

pred noRoomChangeExcept [t, t': Time, rs: set Room] 
{
	all r: Room - rs | r.currentKey.t = r.currentKey.t'
}
	
pred noGuestChangeExcept [t, t': Time, gs: set Guest] 
{
	all g: Guest - gs | g.keys.t = g.keys.t'
}

pred checkout [t, t': Time, g: Guest] 
{
	let occ = FrontDesk.occupant 
    {
		some occ.t.g
		occ.t' = occ.t - Room ->g
    }
	FrontDesk.lastKey.t = FrontDesk.lastKey.t'
	noRoomChangeExcept [t, t', none]
	noGuestChangeExcept [t, t', none]
}

pred checkin [t, t': Time, g: Guest, r: Room, k: Key] 
{
	/*Post. La clé a été délivré au client:*/
    g.keys.t' = g.keys.t + k
    let occ = FrontDesk.occupant 
    {
        /*Pré. La chambre était libre:*/
        no occ.t [r]
        /*Post. La chambre est occupée:*/
        occ.t' = occ.t + r -> g
	}
	let lk = FrontDesk.lastKey
    {
        /*Post. L'accueil a mémorisé la clé donnée au client:*/
        lk.t' = lk.t ++ r -> k
        /*La clé donnée au client est la prochaine du 
           générateur de nombre aléatoire associé à la chambre:*/
        k = nextKey [lk.t [r], r.keys]
    }
    noRoomChangeExcept [t, t', none]
    noGuestChangeExcept [t, t', g]
}

fact traces 
{
    init [first]
    all t: Time-last | let t' = t.next
    {
        some g: Guest, r: Room, k: Key |
            entry [t, t', g, r, k]
            or checkin [t, t', g, r, k]
            or checkout [t, t', g]
    }
}

assert NoBadEntry 
{
    all t: Time, r: Room, g: Guest, k: Key |
        let t' = t.next, 
             o = FrontDesk.occupant.t[r]
        {
            entry [t, t', g, r, k] and some o => g in o
        }
}

/* Aucune action ne peut s'intercaler entre checkin et entering: */
fact NoIntervening
{
    all t:Time-last | let t'=t.next, t''=t'.next
    {
        all g: Guest, r: Room, k: Key |
            checkin[t,t',g,r,k] => (entry[t,t'',g,r,k] or no t'')
    }
}

check NoBadEntry for 3 but 2 Room, 2 Guest, 5 Time
check NoBadEntry for 3 but 3 Room, 3 Guest, 7 Time
check NoBadEntry for 5 but 20 Time
