
// Define the state machine for the Dining Philosophers.
// There are N philosophers sitting around a round table.
// Between every pair of philosophers lies a chopstick.
// Every philosopher has three possible actions:
//  * Acquire the chopstick to their left.
//  * Acquire the chopstick to their right.
//  * Release both chopsticks (in a single step).
//
// (Nota bene: The dining philosophers problem is used to illustrate deadlocks
// and deadlock-freedom. We're not doing any of that here, just using the
// example to teach you to set up a state machine model.)

// Define all the relevant state in this datatype.
// FIXME: fill in here (solution: 8 lines)
datatype ChopstickState = Available | AcquiredAsLeft | AcquiredAsRight
datatype Variables = Variables(tableSize: nat, chopsticks: seq<ChopstickState>)
{
  ghost predicate WellFormed() {
    && 0 < tableSize
    && |chopsticks| == tableSize
  }
}
// END EDIT

ghost predicate Init(v:Variables) {
  // FIXME: fill in here (solution: 3 lines)
  && v.WellFormed()
  && forall i | 0 <= i < v.tableSize :: v.chopsticks[i].Available?
  // END EDIT
}

// FIXME: fill in here (solution: 11 lines)
 // (optional) Add any helper functions desired here
// END EDIT

// Philosopher with index philosopherIndex acquires left chopstick
ghost predicate AcquireLeft(v:Variables, v':Variables, philosopherIndex:nat) {
  // FIXME: fill in here (solution: 5 lines)
  && 0 <= philosopherIndex < |v.chopsticks|
  && v.chopsticks[philosopherIndex] == Available
  && v' == v.(chopsticks := v.chopsticks[philosopherIndex := AcquiredAsLeft])
  // END EDIT
}

// Philosopher with index philosopherIndex acquires right chopstick
ghost predicate AcquireRight(v:Variables, v':Variables, philosopherIndex:nat) {
  // FIXME: fill in here (solution: 5 lines)
  && 0 <= philosopherIndex < |v.chopsticks|
  && v.chopsticks[(philosopherIndex + 1) % |v.chopsticks|] == Available
  && v' == v.(chopsticks := v.chopsticks[(philosopherIndex + 1) % |v.chopsticks| := AcquiredAsRight])
  // END EDIT
}

// Philosopher with index philosopherIndex releases both chopsticks
ghost predicate ReleaseBoth(v:Variables, v':Variables, philosopherIndex:nat) {
  // FIXME: fill in here (solution: 5 lines)
  && 0 <= philosopherIndex < |v.chopsticks|
  && v.chopsticks[philosopherIndex] == AcquiredAsLeft
  && v.chopsticks[(philosopherIndex + 1) % |v.chopsticks|] == AcquiredAsRight
  && v' == v.(chopsticks := v.chopsticks[philosopherIndex := Available])
  && v' == v.(chopsticks := v.chopsticks[(philosopherIndex + 1) % |v.chopsticks| := Available])
  // END EDIT
}

datatype Step =
    // FIXME: fill in here (solution: 3 lines)
    | AcquireLeft(philosopherIndex:nat)
    | AcquireRight(philosopherIndex:nat)
    | ReleaseBoth(philosopherIndex:nat)
    // END EDIT

ghost predicate NextStep(v:Variables, v':Variables, step: Step) {
  match step
  // FIXME: fill in here (solution: 3 lines)
  case AcquireLeft(philosopherIndex) => AcquireLeft(v, v', philosopherIndex)
  case AcquireRight(philosopherIndex) => AcquireRight(v, v', philosopherIndex)
  case ReleaseBoth(philosopherIndex) => ReleaseBoth(v, v', philosopherIndex)
  // END EDIT
}

lemma NextStepDeterministicGivenStep(v:Variables, v':Variables, step: Step)
  requires NextStep(v, v', step)
  ensures forall v'' | NextStep(v, v'', step) :: v' == v''
{}

ghost predicate Next(v:Variables, v':Variables) {
  exists step :: NextStep(v, v', step)
}

// This predicate should be true if and only if no philosopher holds a
// chopstick.
// Since you defined the Variables state, you must define this predicate in
// those terms.
ghost predicate NoSticksAcquired(v: Variables)
  requires v.WellFormed()
{
  // FIXME: fill in here (solution: 8 lines)
  forall i | 0 <= i < |v.chopsticks| :: v.chopsticks[i].Available?
  // END EDIT
}

// Change this predicate to be true if and only if philosopher
// `philosopherIndex` holds both of their chopsticks.
// Since you defined the Variables state, you must define this predicate in
// those terms.
ghost predicate BothSticksAcquired(v: Variables, philosopherIndex: nat)
  requires philosopherIndex < v.tableSize
  requires v.WellFormed()
{
  // FIXME: fill in here (solution: 6 lines)
  && v.chopsticks[philosopherIndex] == AcquiredAsLeft
  && v.chopsticks[(philosopherIndex + 1) % |v.chopsticks|] == AcquiredAsRight
  // END EDIT
}

// Show that, in the Init state, no philosopher has chopsticks.
lemma InitProperty(v: Variables, philosopherIndex:nat)
  requires Init(v)
  ensures NoSticksAcquired(v)
{
  // FIXME: fill in here (solution: 0 lines)
   // Add a proof (if needed).
  // END EDIT
}


// Show a behavior that evolves from the init state to one where a philosopher
// has completed acquiring both chopsticks.
lemma PseudoLiveness(philosopherIndex:nat) returns (behavior:seq<Variables>)
  requires philosopherIndex == 1
  ensures 0 < |behavior|  // precondition for index operators below
  ensures Init(behavior[0])
  ensures forall i | 0 <= i < |behavior|-1 :: Next(behavior[i], behavior[i+1]) // Behavior satisfies your state machine
  ensures forall i | 0 <= i < |behavior| :: behavior[i].tableSize == 3
  ensures behavior[|behavior|-1].WellFormed() // precondition for calling BothSticksAcquired
  ensures BothSticksAcquired(behavior[|behavior|-1], philosopherIndex)  // Behavior ultimately achieves acquisition for philosopherIndex
{
  // FIXME: fill in here (solution: 6 lines)
  var v1 := Variables(tableSize := 3, chopsticks := [Available, Available, Available]);
  assert Init(v1);
  var v2 := v1.(chopsticks := [Available, AcquiredAsLeft, Available]);
  assert NextStep(v1, v2, Step.AcquireLeft(philosopherIndex));
  var v3 := v1.(chopsticks := [Available, AcquiredAsLeft, AcquiredAsRight]);
  assert NextStep(v2, v3, Step.AcquireRight(philosopherIndex));
  behavior := [v1, v2, v3];
  // END EDIT
}
