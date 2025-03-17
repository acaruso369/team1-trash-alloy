abstract sig Vehicles {

	loc: one Places,   //Every vehicles has one and only one location

		 // (ensures vehicles do not exist in multiple places).
}


sig People {}

sig Materials {}


abstract sig Places {
	peopleAt: set People, //tracks people and materials at different places
	materialsAt: set Materials
}


sig Warehouse, Dwellings, Workplaces extends Places{}


sig Job {

     location: one Places, //Each Job is associated with specific workplace

     ReqPeople: one Int,	    //Minimum # of people needed

     ReqMaterials: one Int	    //Minimum # of Materials needed

}


sig PVehicles extends Vehicles {

	capacity: one Int,

	entries : set People

}{

	#entries <= capacity

}

sig CVehicles extends Vehicles{

	capacity: one Int,

	entries : set Materials

}{

	#entries <= capacity

}
fact init {

	//all v:Vehicles | v.loc in Places

	one Workplaces

	one Dwellings

	one Warehouse

}
fact { //Vehicles must have capacity > 0

	all v: PVehicles | v.capacity > 0

	all v: CVehicles | v.capacity > 0

}
fact { //ReqPeople/Materials > 0

	all j: Job | j.ReqPeople > 0

	all j: Job | j.ReqMaterials > 0

}


pred movePVehicle(v: PVehicles, from: Places, to: Places) {

     v.loc = from   // Vehicle must start at specified place
     v.loc' = to    // After movement, the vehicles location updated to new place

     v.entries' = none //People exit the vehicle on arrival
     to.peopleAt' = to.peopleAt + v.entries
     from.peopleAt' = from.peopleAt - v.entries //remove poeple from old place


}

pred moveCVehicle(v: CVehicles, from: Places, to: Places) {

     v.loc = from
     v.loc' = to

     v.entries' = none //Materials exit on arrival
     to.materialsAt' = to.materialsAt + v.entries
     from.materialsAt' = from.materialsAt - v.entries

}

pred completeJob (j: Job) {
	let LocPeople = {p: People | p in j.location.peopleAt}
	let LocMaterials = {m: Materials | m in j.location.materialsAt}

	#LocPeople >= j.ReqPeople &&
	#LocMaterials >= j.ReqMaterials

	 Job' = Job - j //Only remove completed job
}


run {

     some vP: PVehicles | movePVehicle[vP, Warehouse, Workplaces]
     some vC: CVehicles | moveCVehicle[vC, Warehouse, Dwellings]


     some j: Job | completeJob[j] //Job is completed if requirements are met
} for 5