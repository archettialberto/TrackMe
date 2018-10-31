open util/integer
open util/time
open util/boolean

sig User {}

sig DataEntry {
	threshold : one Int,
	user : one User,
	value : one Int,
	location : one GPSLocation
}

sig SOSSystem {
	emergencies : SOSCall -> DataEntry
}

sig SOSCall {}

sig GPSLocation {}


fact CallIfAboveThreshold {
	all de : DataEntry | de.value > de.threshold implies (
		one emergency : SOSSystem.emergencies | (
			one target : SOSCall -> de| target = emergency
		)
	)
}

fact OneThresholdForDataEntries {
	all disj de1, de2 : DataEntry |de1.threshold = de2.threshold
}

pred show{}

run show for 4 but 2 DataEntry
