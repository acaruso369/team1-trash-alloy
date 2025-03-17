abstract sig Vehicles { //Vehicles has a location that is one of the places 
    loc: one Places
}

sig People {}
sig Materials {}

abstract sig Places {
    peopleAt: set People,
    materialsAt: set Materials
}

sig Warehouse, Dwellings, Workplaces extends Places {} //Places 

sig Job {
    location: one Places, 	//Where the job is happening 
    ReqPeople: one Int, 	//Requires certain # of people
    ReqMaterials: one Int	//Requires certain # of material 
}

sig PVehicles extends Vehicles {
    capacity: one Int,		//Passenger vehicles have a max # of people they can hold
    entries: set People	//Set of people currently in the vehicle 
}

fact {
    all v: PVehicles | #v.entries <= v.capacity //Pvehicles cannot exceed their capacity 
}

sig CVehicles extends Vehicles {
    capacity: one Int,		//Cargo Vehicles have a max # of materials they can hold 
    entries: set Materials	//Set of materials currently in the vehicle 
}

fact {
    all v: CVehicles | #v.entries <= v.capacity //Cvehicles cannot exceed their capacity 
}

fact init {			//Ensures that there is exactly one of each place 
    #Workplaces = 1
    #Dwellings = 1
    #Warehouse = 1
}

fact {			//Vehicles must have positive requirements 
    all v: PVehicles | v.capacity > 0
    all v: CVehicles | v.capacity > 0
}

fact {			//Every job must require at least one person and material 
    all j: Job | j.ReqPeople > 0
    all j: Job | j.ReqMaterials > 0
}

fact jobsCanBeCompleted {	//Ensures that Jobs location has enough people and materials to satisfy requirements
    all j: Job | 
        #j.location.peopleAt >= j.ReqPeople and 
        #j.location.materialsAt >= j.ReqMaterials 
}

pred movePVehicle(v: PVehicles, from: Places, to: Places) {	//Moves a PVehicles from one Places to another 
    v.loc = from and
    v.loc' = to and
    no v.entries' and
    to.peopleAt' = to.peopleAt + v.entries and
    from.peopleAt' = from.peopleAt - v.entries
}

pred moveCVehicle(v: CVehicles, from: Places, to: Places) {// Moves a CVehicle from one places to another
    v.loc = from and
    v.loc' = to and
    no v.entries' and
    to.materialsAt' = to.materialsAt + v.entries and
    from.materialsAt' = from.materialsAt - v.entries
}

run {} for 5

run {
    some vP: PVehicles | movePVehicle[vP, Warehouse, Workplaces]
    some vC: CVehicles | moveCVehicle[vC, Warehouse, Dwellings]
} for 5
