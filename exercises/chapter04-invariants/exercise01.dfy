// Crawler

module Crawler {
  datatype Variables = Variables(x:int, y:int)

  ghost predicate Init(v:Variables) {
    && v.x == 0
    && v.y == 5
  }

  ghost predicate MoveNorth(v:Variables, v':Variables) {
    && v'.x == v.x
    && v'.y == v.y + 1
  }

  ghost predicate MoveSouthEast(v:Variables, v':Variables) {
    && v'.x == v.x + 1
    && v'.y == v.y - 1
  }

  ghost predicate Next(v:Variables, v':Variables) {
    || MoveNorth(v, v')
    || MoveSouthEast(v, v')
  }

  ghost predicate InManhole(v:Variables) {
    v.x*v.x + v.y*v.y <= 3*3
  }

  ghost predicate Safety(v:Variables) {
    !InManhole(v)
  }

  ghost predicate Inv(v:Variables) {
    // FIXME: fill in here (solution: 1 line)
    v.x + v.y >= 5
    // END EDIT
  }

  // Here's your proof obligation that Safety predicate holds in every behavior
  // allowed by the state machine.
  // With the correct invariant, this proof goes through without a body.
  lemma SafetyTheorem(v:Variables, v':Variables)
    ensures Init(v) ==> Inv(v)
    ensures Inv(v) && Next(v, v') ==> Inv(v')
    ensures Inv(v) ==> Safety(v)
  {
  }
}
