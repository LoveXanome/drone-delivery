open util/ordering[Time] as to
open util/ordering[Key] as ko

sig Time {}
sig Key {}

sig Room
{
	keys: set Key, //On peut modifier la clé
	currentKey: keys one -> Time
}

fact DisjointKeySets
{
	-- each key belongs to at most one room
	Room<:keys in Room lone-> Key //Toutes les relations binaires qu'on peut construire entre Room et Key pour lesquelles il y a au plus une chambre associée à une clé  	-- i.e. toutes les relations que l'on peut construire
	// Le symbole "<:" permet d'obtenir toutes les paires {Room, Key}
}

one sig FrontDesk //FrontDesk est un singleton (dans l'ensemble des FrontDesk, il n'y a toujours qu'un seul élément)
{
	lastKey:(Room -> Key) -> Time,
	occupant:(Room -> Guest) -> Time
}

sig Guest
{
	keys:  Key -> Time
}

fun nextKey [k:Key, ks: set Key]: set Key
{
	min[k.nexts & ks]
}

pred init [t:Time]
{
	no Guest.keys.t
	no FrontDesk.occupant.t
	all r:Room | FrontDesk.lastKey.t [r] = r.currentKey.t //On garde tous les triplets {Room, Key, Time} du FrontDesk à l'instant t pour la chambre r
}

pred entry [t,t':Time, g:Guest, r:Room, k:Key]
{
	/*Précondition*/
	k in g.keys.t
	/*Postcondition*/
	let ck = r.currentKey
	{
		/*La clé de la carte est la clé de la chambre*/
		(k = ck.t and ck.t' = ck.t) or 
		/*La clé de la carte est la prochaine clé de la chambre*/
		(k= nextKey[ck.t,r.keys] and ck.t' = k)
	}
	/*Ce qui du système doit rester inchangé durant cette opération*/
	noRoomChangeExcept [t, t', r]
	noGuestChangeExcept [t, t', none]
	noFrontDeskChange[t,t']
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

pred checkout[t,t':Time, g:Guest]
{
	let occ = FrontDesk.occupant
	{
		/*Précondition : g était un occupant d'une chambre*/
		some occ.t.g
		/*Postcondition : g n'occupe plus de chambre*/
		occ.t' = occ.t - Room -> g
	}
	FrontDesk.lastKey.t = FrontDesk.lastKey.t'
	noRoomChangeExcept [t, t', none]
	noGuestChangeExcept [t, t', none]
}

pred checkin[t,t':Time, g:Guest, r:Room, k:Key]
{
	/*Post. La clé a été donnée au client*/
	g.keys.t' = g.keys.t + k
	let occ = FrontDesk.occupant
	{
		no occ.t [r] //Pas d'occupant dans la chmabre r
		occ.t' = occ.t + r -> g
	}
	let lk = FrontDesk.lastKey
	{
		lk.t' = lk.t ++ r -> k
		k = nextKey [lk.t[r],r.keys]
	}
	noRoomChangeExcept [t, t', none]
	noGuestChangeExcept [t, t', g]
}

fact traces
{
	init [first]
	all t:Time-last | let t' = t.next
	{
		some g:Guest, r:Room, k:Key |
			entry [t,t',g,r,k]
			or checkin[t,t',g,r,k]
			or checkout[t,t',g]
	}
}

assert NoBadEntry
{	
	all t:Time, r:Room, g:Guest, k:Key |
		let t' = t.next,
				o = FrontDesk.occupant.t[r]
				{
					entry[t,t',g,r,k] and some o=> g in o
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

pred go 
{
	init [first]
}
run go
