abstract sig Vehicles {
    loc: one Places
}

sig People {}
sig Materials {}

abstract sig Places {
    peopleAt: set People,
    materialsAt: set Materials
}

sig Warehouse, Dwellings, Workplaces extends Places {}

sig Job {
    location: one Places,
    ReqPeople: one Int,
    ReqMaterials: one Int
}

sig PVehicles extends Vehicles {
    capacity: one Int,
    entries: set People
}

fact {
    all v: PVehicles | #v.entries <= v.capacity
}

sig CVehicles extends Vehicles {
    capacity: one Int,
    entries: set Materials
}

fact {
    all v: CVehicles | #v.entries <= v.capacity
}

fact init {
    #Workplaces = 1
    #Dwellings = 1
    #Warehouse = 1
}

fact {
    all v: PVehicles | v.capacity > 0
    all v: CVehicles | v.capacity > 0
}

fact {
    all j: Job | j.ReqPeople > 0
    all j: Job | j.ReqMaterials > 0
}

fact jobsCanBeCompleted {
    all j: Job | 
        #j.location.peopleAt >= j.ReqPeople and 
        #j.location.materialsAt >= j.ReqMaterials 
}

pred movePVehicle(v: PVehicles, from: Places, to: Places) {
    v.loc = from and
    v.loc' = to and
    no v.entries' and
    to.peopleAt' = to.peopleAt + v.entries and
    from.peopleAt' = from.peopleAt - v.entries
}

pred moveCVehicle(v: CVehicles, from: Places, to: Places) {
    v.loc = from and
    v.loc' = to and
    no v.entries' and
    to.materialsAt' = to.materialsAt + v.entries and
    from.materialsAt' = from.materialsAt - v.entries
}

run {
    some vP: PVehicles | movePVehicle[vP, Warehouse, Workplaces]
    some vC: CVehicles | moveCVehicle[vC, Warehouse, Dwellings]
} for 5