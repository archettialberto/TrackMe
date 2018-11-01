open util/integer
open util/time
open util/boolean

sig User {
	myData : some DataEntry
}

sig DataType {
	threshold : one Int
}

sig DataEntry {
	timestamp : one Int,
	type : one DataType,
	value : one Int,
	location : one GPSLocation
} {
	timestamp > 0
}

sig GPSLocation {}

fact UniqueDataEntries {
	all u : User| all disj de, de' : u.myData | de.timestamp != de'.timestamp
}

fact NoDataEntryWithoutUser {
	all de : DataEntry | some u : User | de in u.myData
}

pred addDataEntry(u, u' : User, de : DataEntry) {
	u'.myData = u.myData + de
}

pred show{}

run addDataEntry for 3 but exactly 1 User, exactly 3 DataEntry

//run show for 2
//run show for 4 but exactly 4 DataEntry, exactly 2 User
