open util/integer

sig User {}

one sig Threshold {
	value : one Int
}

sig DataEntry {
	value : one Int
}

sig System {
	data : User ->set DataEntry,
	calls : set DataEntry
} {
	User.data = DataEntry
	data.DataEntry = User
	all disj u, u' : User | u.data & u'.data = none
	all d : calls | d in User.data
	all d : User.data |
		(d.value > Threshold.value => d in calls) and
		(d.value <= Threshold.value => d not in calls)
}

pred acquire[u : User, d : DataEntry, s, s' : System] {
	d not in (User - u).(s.data)
	s'.data = s.data + u->d
	checkCall[d, s, s']
}

pred checkCall[d : DataEntry, s, s' : System] {
	d.value > Threshold.value =>
		s'.calls = s.calls + d
	d.value <= Threshold.value =>
		s'.calls = s.calls
}

run acquire for 1 System, 4 DataEntry, exactly 3 User

callOnEmergency: check {
	all s, s' : System, d : DataEntry, u : User |
		acquire[u, d, s, s'] and d.value > Threshold.value
			=> d in s'.calls
}

dontCallWithoutEmergency: check {
	all s, s' : System, d : DataEntry, u : User |
		acquire[u, d, s, s'] and d.value <= Threshold.value
			=> d not in s'.calls
}
