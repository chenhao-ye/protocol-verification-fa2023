
// Model a lock service that consists of a single server and an
// arbitrary number of clients.
//
// The state of the system includes the server's state (whether the server
// knows that some client holds the lock, and if so which one)
// and the clients' states (for each client, whether that client knows
// it holds the lock).
//
// The system should begin with the server holding the lock.
// An acquire step atomically transfers the lock from the server to some client.
// (Note that we're not modeling the network yet -- the lock disappears from
// the server and appears at a client in a single atomic transition.)
// A release step atomically transfers the lock from the client back to the server.
//
// The safety property is that no two clients ever hold the lock
// simultaneously.

// FIXME: fill in here (solution: 13 lines)
datatype ServerState = LockAvailable | HeldByClient(clientIndex: nat)
datatype ClientState = NoLock | HoldLock
datatype Variables = Variables(serverState: ServerState, clientStates: seq<ClientState>) {
  ghost predicate WellFormed() {
    match serverState
    case HeldByClient(clientIndex) =>
      && (0 <= clientIndex < |clientStates|
          && clientStates[clientIndex].HoldLock?)
    case LockAvailable? =>
      forall i | 0 <= i < |clientStates| :: clientStates[i].NoLock?
  }
}
// END EDIT


ghost predicate Init(v:Variables) {
  && v.WellFormed()
     // FIXME: fill in here (solution: 3 lines)
  && v.serverState == LockAvailable
  && forall i | 0 <= i < |v.clientStates| :: v.clientStates[i].NoLock?
                                             // END EDIT
}
// FIXME: fill in here (solution: 23 lines)
// END EDIT
// Jay-Normal-Form: pack all the nondeterminism into a single object
// that gets there-exist-ed once.
datatype Step =
    // FIXME: fill in here (solution: 2 lines)
  | AcquireLock(clientIndex: nat)
  | ReleaseLock(clientIndex: nat)
    // END EDIT

ghost predicate NextStep(v:Variables, v':Variables, step: Step) {
  match step
  // FIXME: fill in here (solution: 2 lines)
  case AcquireLock(clientIndex) =>
    && v.WellFormed()
    && 0 <= clientIndex < |v.clientStates|
    && v.serverState.LockAvailable?
    && v' == v.(
             serverState := HeldByClient(clientIndex),
             clientStates := v.clientStates[clientIndex := HoldLock])
  case ReleaseLock(clientIndex) =>
    && v.WellFormed()
    && 0 <= clientIndex < |v.clientStates|
    && v.serverState.HeldByClient?
    && v.serverState.clientIndex == clientIndex
    && v' == v.(
             serverState := LockAvailable,
             clientStates := v.clientStates[clientIndex := NoLock]
             )
       // END EDIT
}

lemma NextStepDeterministicGivenStep(v:Variables, v':Variables, step: Step)
  requires NextStep(v, v', step)
  ensures forall v'' | NextStep(v, v'', step) :: v' == v''
{}

ghost predicate Next(v:Variables, v':Variables) {
  exists step :: NextStep(v, v', step)
}

// A good definition of safety for the lock server is that no two clients
// may hold the lock simultaneously. This predicate should capture that
// idea in terms of the Variables you have defined.
ghost predicate Safety(v:Variables) {
  // FIXME: fill in here (solution: 10 lines)
  match v.serverState
  case HeldByClient(clientIndex) =>
    && 0 <= clientIndex < |v.clientStates|
    && v.clientStates[clientIndex].HoldLock?
    && forall i | 0 <= i < |v.clientStates|
         :: v.clientStates[i].HoldLock? ==> i == clientIndex
  case LockAvailable? => forall i | 0 <= i < |v.clientStates|
    :: v.clientStates[i].NoLock?
       // END EDIT
}


// This predicate should be true if and only if the client with index `clientIndex`
// has the lock acquired.
// Since you defined the Variables state, you must define this predicate in
// those terms.
ghost predicate ClientHoldsLock(v: Variables, clientIndex: nat)
  requires v.WellFormed()
{
  // FIXME: fill in here (solution: 1 line)
  && 0 <= clientIndex < |v.clientStates|
  && v.clientStates[clientIndex].HoldLock?
     // END EDIT
}

// Show a behavior that the system can release a lock from clientA and deliver
// it to clientB.
lemma PseudoLiveness(clientA:nat, clientB:nat) returns (behavior:seq<Variables>)
  requires clientA == 2
  requires clientB == 0
  ensures 2 <= |behavior|  // precondition for index operators below
  ensures Init(behavior[0])
  ensures forall i | 0 <= i < |behavior|-1 :: Next(behavior[i], behavior[i+1]) // Behavior satisfies your state machine
  ensures forall i | 0 <= i < |behavior| :: Safety(behavior[i]) // Behavior always satisfies the Safety predicate
  ensures behavior[|behavior|-1].WellFormed() // precondition for calling ClientHoldsLock
  ensures ClientHoldsLock(behavior[1], clientA) // first clientA acquires lock
  ensures ClientHoldsLock(behavior[|behavior|-1], clientB) // eventually clientB acquires lock
{
  // FIXME: fill in here (solution: 9 lines)
  var v1 := Variables(serverState := LockAvailable,
                      clientStates := [NoLock, NoLock, NoLock]);
  var v2 := Variables(serverState := HeldByClient(clientA),
                      clientStates := [NoLock, NoLock, HoldLock]);
  assert(NextStep(v1, v2, AcquireLock(clientA)));

  var v3 := v1;
  assert(NextStep(v2, v3, ReleaseLock(clientA)));

  var v4 := Variables(serverState := HeldByClient(clientB),
                      clientStates := [HoldLock, NoLock, NoLock]);
  assert(NextStep(v3, v4, AcquireLock(clientB)));

  behavior := [v1, v2, v3, v4];
  // END EDIT
}