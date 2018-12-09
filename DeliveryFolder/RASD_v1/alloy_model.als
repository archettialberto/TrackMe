open util/integer
open util/boolean


/** *** DESCRIPTION ***
 *
 * In this Alloy model we will represent Data4Help
 * and AutomatedSOS services in a simplified way:
 *  - Data4Help: we will describe third party
 *    requests according to some assumptions
 *    (single user requests always target ALL
 *    user data in the system; anonymous group
 *    requests have size, but no filter available)
 *  - AutomatedSOS: we will assume that every user
 *    is subscribed to AutomatedSOS and we will test
 *    if SOS calls are always performed correctly
 */


/** *** SIGNATURES *** */

/**
 * Actors of the system
 */
sig User, ThirdParty {}

/**
 * A DataEntry corresponds to one wearable
 * acquisition
 */
sig DataEntry {
	value : one Int
}

/**
 * Every DataEntry has the same data type,
 * therefore a single threshold is needed
 */
one sig Threshold {
	value : one Int
}

/**
 * Simplified single user request:
 * third parties ask for ALL target's data
 */
sig SRequest {
	target   : one User,			// target user
	accepted : one Bool,			// user response
	shared   : set DataEntry	// data shared
} {
	// no data outside the system
	all s : System | shared in User.(s.data)
	// decline implies no data sharing
	accepted = False => shared = none
	// accept implies data sharing
	all s : System | accepted = True
		=> shared = target.(s.data)
}

/**
 * Simplified anonymous group request:
 * filters are not allowed
 */
sig ARequest {
	size   : one Int,				// # of desired d.e.
	shared : set DataEntry	// data shared
} {
	all s : System |
		// no data outside the system
		(shared in User.(s.data)) and
		// enough data implies sharing
		(#s.data >= size => #shared = size) and
		// not enough data implies no data sharing
		(#s.data < size => shared = none)
}

/**
 * S2B with database that contains data entries
 * and requests
 */
sig System {
	// single user requests
	srequests : ThirdParty ->set SRequest,
	// anonymous group requests
	arequests : ThirdParty ->set ARequest,
	// all acquired data entries
	data  : User ->set DataEntry,
	// emergency calls
	calls : set DataEntry
} {
	// no data entry outside the system
	User.data = DataEntry
	// no req. outside the system
	ThirdParty.srequests = SRequest
	ThirdParty.arequests = ARequest
	// no two applicants for same req.
	all disj tp, tp' : ThirdParty |
		tp.srequests & tp'.srequests = none
	all disj tp, tp' : ThirdParty |
		tp.arequests & tp'.arequests = none
	// no same data entry for two users
	all disj u, u' : User |
		u.data & u'.data = none
	// no calls outside the system
	all d : calls | d in User.data
	all d : User.data |
		// above threshold implies emergency
		(d.value > Threshold.value => d in calls) and
		// below threshold implies no emergency
		(d.value <= Threshold.value => d not in calls)
}


/** *** PREDICATES *** */

/**
 * User u acquires a new data entry d,
 * s is the old system,
 * s' is the new system
 */
pred acquire[u : User, d : DataEntry, s, s' : System] {
	// no unrequired changes
	s'.srequests = s.srequests
	s'.arequests = s.arequests
	// add entry
	s'.data = s.data + u->d
	// eventually call emergency
	d.value > Threshold.value =>
		s'.calls = s.calls + d
	d.value <= Threshold.value =>
		s'.calls = s.calls
}

/**
 * Third party tp makes a single user request r
 * to user u; u gives b as response (true
 * means accept, while false means decline),
 * s is the old system,
 * s' is the new system
 */
pred makeSRequest[s, s' : System, tp : ThirdParty,
									r : SRequest, u : User, b : Bool] {
	// no unrequired changes
	s'.data = s.data
	s'.calls = s.calls
	s'.arequests = s.arequests
	// compose request
	r.accepted = b
	r.target = u
	// add request
	s'.srequests = s.srequests + tp->r
}

/**
 * Third party tp makes an anonymous group request r
 * expected to have n entries,
 * s is the old system,
 * s' is the new system
 */
pred makeARequest[s, s' : System, tp : ThirdParty,
									r : ARequest, n : Int] {
	// no unrequired changes
	s'.data = s.data
	s'.calls = s.calls
	s'.srequests = s.srequests
	// compose request
	r.size = n
	// add request
	s'.arequests = s.arequests + tp->r
}


/** *** ASSERTIONS *** */

/**
 * Calls are always performed
 */
assert callOnEmergency {
	all s, s' : System, d : DataEntry, u : User |
			// above threshold implies emergency call
			(acquire[u, d, s, s'] and
			 d.value > Threshold.value
			  => d in s'.calls) and
			// below threshold implies no emergency call
			(acquire[u, d, s, s'] and
  		 d.value <= Threshold.value
				=> d not in s'.calls)
}

/**
 * Single user request access is correct
 */
assert verifyAccessForSRequest {
	all s, s' : System, r : SRequest, tp : ThirdParty |
		// accept implies sharing
		(makeSRequest[s, s', tp, r, r.target, True]
			=> r.shared = r.target.(s.data)) and
		// decline implies no sharing
		(makeSRequest[s, s', tp, r, r.target, False]
			=> r.shared = none)
}

/**
 * Anymous group request access is correct
 */
assert verifyAccessForARequest {
	all s, s' : System, r : ARequest,
  tp : ThirdParty, n : Int |
		// enough data implies sharing
		(n <= #s.data =>
			(makeARequest[s, s', tp, r, n]
				=> #r.shared = n)) and
		// not enough data implies no sharing
		(n > #s.data =>
			(makeARequest[s, s', tp, r, n]
				=> r.shared = none))
}


/** *** COMMANDS *** */
run acquire
run makeSRequest
run makeARequest
check callOnEmergency
check verifyAccessForSRequest
check verifyAccessForARequest
