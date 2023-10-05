// Single-Server Lock Service Proof

// We provide a correct spec for the lock server here, but leave you
// to define the Safety property to be proven.
// You are welcome to prove correct your own model from chapter03,
// but note that may be too hard or too easy if your spec is broken.

// Copy your solution for chapter03/exercise03 into the current directory with
// this name:
include "ch03exercise03.dfy"

// FIXME: fill in here (solution: 11 lines)
ghost predicate Inv(v:Variables) {
  && (forall i: nat, j: nat | 0 <= i < |v.clients| && 0 <= j < |v.clients|
        :: v.clients[i].Acquired? && v.clients[j].Acquired? ==> i == j)
  && (forall i: nat | 0 <= i < |v.clients|
        :: v.clients[i].Acquired? ==> v.server.Client? && v.server.id == i)
}
// END EDIT

lemma InvInit(v: Variables)
  requires Init(v)
  ensures Inv(v)
{}

lemma InvInductive(v: Variables, v': Variables)
  requires Inv(v) && Next(v, v')
  ensures Inv(v')
{
  var step :| NextStep(v, v', step);
  match step {
    case AcquireStep(id) => {
      assert v'.server.Client? && v'.server.id == id;
      return;
    }
    case ReleaseStep(id) => { return; }
  }
}

lemma InvSafe(v: Variables)
  requires Inv(v)
  ensures Safety(v)
{}

// Here's your obligation. Probably easiest to break this up into three
// lemmas, each P==>Q becomes requires P ensures Q.
lemma SafetyTheorem(v:Variables, v':Variables)
  ensures Init(v) ==> Inv(v)
  ensures Inv(v) && Next(v, v') ==> Inv(v')
  ensures Inv(v) ==> Safety(v)
{
  // FIXME: fill in here (solution: 10 lines)
  if Init(v) {
    InvInit(v);
  }
  if Inv(v) && Next(v, v') {
    InvInductive(v, v');
  }
  if Inv(v) {
    InvSafe(v);
  }
  // END EDIT
}
