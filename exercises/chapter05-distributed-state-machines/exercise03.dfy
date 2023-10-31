// Two Phase Commit Safety Proof
// Prove that the 2PC distributed system (from exercise01) accomplishes the Safety spec (from exercise02)

include "exercise02.dfy"

module TwoPCInvariantProof {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened Obligations

  // This is a conjunct of the inductive invariant, indicating that the messages carrying
  // decisions should reflect the votes of the participants as relayed to the coordinator
  ghost predicate DecisionMsgsAgreeWithDecision(v: Variables)
    requires v.WF()
  {
    // FIXME: fill in here (solution: 5 lines)
    && (forall m: Message | m in v.network.sentMsgs && m.MsgDecison?
          :: && CoordinatorVars(v).decision.Some?
             && m.d == CoordinatorVars(v).decision.value)
    && (forall m: Message, i: HostId |
          && m in v.network.sentMsgs
          && m.MsgDecison?
          && ValidParticipantId(v, i)
          && ParticipantVars(v, i).decision.Some?
          :: (m.d == ParticipantVars(v, i).decision.value))
       // END EDIT
  }

  // We use this block of code to define additional invariants. We recommend you
  // define predicates for the individual parts of your invariant, to make
  // debugging easier.
  // FIXME: fill in here (solution: 20 lines)
  ghost predicate ParticipantDecideAfterCoordinator(v: Variables)
    requires v.WF()
  {
    CoordinatorVars(v).decision.None? ==> forall i: HostId | ValidParticipantId(v, i)
        :: ParticipantVars(v, i).decision.None?
  }

  ghost predicate RecvVoteImpliesVoteMsgSent(v: Variables)
    requires v.WF()
  {
    forall i: HostId | ValidParticipantId(v, i)
      :: CoordinatorVars(v).votes[i].Some? ==> (
             exists m: Message ::
               && m in v.network.sentMsgs
               && m.MsgVote?
               && m.p == i
               && m.vote == CoordinatorVars(v).votes[i].value
           )
  }

  ghost predicate VoteMsgImpliesPreference(v: Variables)
    requires v.WF()
  {
    forall i: HostId | ValidParticipantId(v, i)
      :: (exists m: Message ::
            && m in v.network.sentMsgs
            && m.MsgVote?
            && m.p == i) ==> (
             forall m: Message | && m in v.network.sentMsgs
                                 && m.MsgVote?
                                 && m.p == i
               :: m.vote == ParticipantVars(v, i).c.preference
           )
  }

  // END EDIT


  ghost predicate Inv(v: Variables)
  {
    && v.WF()
       // FIXME: fill in here (solution: 2 lines)
       // END EDIT
       // We give you the blueprint for one invariant to get you started...
    && DecisionMsgsAgreeWithDecision(v)
    && ParticipantDecideAfterCoordinator(v)
    && RecvVoteImpliesVoteMsgSent(v)
    && VoteMsgImpliesPreference(v)
       // && VoteAgreeWithPreference(v)
       // ...but you'll need more.
    && Safety(v)
  }

  lemma InitImpliesInv(v: Variables)
    requires Init(v)
    ensures Inv(v)
  {
    // FIXME: fill in here (solution: 3 lines)
    assert !CoordinatorVars(v).decision.Some?;
    // END EDIT
  }

  lemma InvInductive(v: Variables, v': Variables)
    requires Inv(v)
    requires Next(v, v')
    ensures Inv(v')
  {
    //(not all of the below but much of it)
    // FIXME: fill in here (solution: 59 lines)
    var step :| NextStep(v, v', step);
    var hostId := step.hostId;
    var msgOps := step.msgOps;

    var cv := CoordinatorVars(v);
    var cv' := CoordinatorVars(v');

    if ValidParticipantId(v, hostId) {
      var pv := ParticipantVars(v, hostId);
      var pv' := ParticipantVars(v', hostId);
      var hostStep :| ParticipantHost.NextStep(pv, pv', hostStep, msgOps);
      if msgOps.recv.Some? && msgOps.send.Some? {
        assert hostStep.CastVoteStep?;
        assert forall i: HostId | ValidParticipantId(v, i)
            :: ParticipantVars(v, i) == ParticipantVars(v', i);
        assert SafetyAC1(v');
        assert SafetyAC3(v');
        assert SafetyAC4(v');
        assert VoteMsgImpliesPreference(v');
      } else if msgOps.recv.Some? && msgOps.send.None? {
        var m := msgOps.recv.value;
        assert m.MsgDecison?;
        assert hostStep.AcceptDecisionStep?;
        assert ParticipantHost.AcceptDecision(pv, pv', msgOps);

        {
          forall i: HostId, j: HostId |
            && ValidParticipantId(v', i)
            && ValidParticipantId(v', j)
            && ParticipantVars(v', i).decision.Some?
            && ParticipantVars(v', j).decision.Some?
            ensures ParticipantVars(v', i).decision.value == ParticipantVars(v', j).decision.value
          {
            var di' := ParticipantVars(v', i).decision.value;
            var dj' := ParticipantVars(v', j).decision.value;

            assert (forall m: Message | m in v'.network.sentMsgs && m.MsgDecison?
                      :: && CoordinatorVars(v').decision.Some?
                         && m.d == CoordinatorVars(v').decision.value);
            forall m_: Message, i: HostId |
              && m_ in v'.network.sentMsgs
              && m_.MsgDecison?
              && ValidParticipantId(v', i)
              && ParticipantVars(v', i).decision.Some?
              ensures (m_.d == ParticipantVars(v', i).decision.value) {
              assert m_ in v'.network.sentMsgs;
              if i != hostId {
                assert m_.d == ParticipantVars(v, i).decision.value;
                assert ParticipantVars(v, i).decision == ParticipantVars(v', i).decision;
              } else {
                assert ParticipantVars(v', i).decision.Some? && ParticipantVars(v', i).decision.value == m.d;
              }
            }
            assert DecisionMsgsAgreeWithDecision(v');
            assert di' == m.d;
            assert dj' == m.d;
            assert di' == dj';
          }
          assert SafetyAC1(v');
        }

        {
          if exists i: HostId :: ValidParticipantId(v', i) && ParticipantVars(v', i).c.preference == No {
            var i: HostId :| ValidParticipantId(v', i) && ParticipantVars(v', i).c.preference == No;
            assert ParticipantVars(v, i).c.preference == No;
            if CoordinatorVars(v').decision.Some? {
              assert cv.decision == cv'.decision;
              assert cv'.decision.value == Abort;
            }
          }
          assert SafetyAC3(v');
        }

        {
          if forall i: HostId | ValidParticipantId(v', i) :: ParticipantVars(v', i).c.preference == Yes
          {
            assert SafetyAC4(v);
            assert forall i: HostId :: ValidParticipantId(v, i) == ValidParticipantId(v', i);
            assert forall i: HostId | ValidParticipantId(v, i) :: ParticipantVars(v, i).c.preference == Yes;
            assert CoordinatorVars(v).decision.Some? ==> (CoordinatorVars(v).decision.value == Commit);
            assert cv' == cv;
            assert cv.decision.Some? ==> (cv.decision.value == Commit);
            assert cv'.decision.Some? ==> (cv'.decision.value == Commit);
          }
          assert (forall i: HostId | ValidParticipantId(v', i) :: ParticipantVars(v', i).c.preference == Yes)
            ==> (forall i: HostId | ValidParticipantId(v', i)
                   :: (ParticipantVars(v', i).decision.Some? ==> ParticipantVars(v', i).decision.value == Commit)
              );
          assert SafetyAC4(v');
        }

        {
          forall i: HostId, m: Message |
            && ValidParticipantId(v', i)
            && m in v'.network.sentMsgs
            && m.MsgVote?
            && m.p == i
            ensures m.vote == ParticipantVars(v', i).c.preference {
            assert v.network.sentMsgs == v'.network.sentMsgs;
            assert ParticipantVars(v, i).c.preference == ParticipantVars(v', i).c.preference;
          }
          assert VoteMsgImpliesPreference(v');
        }
      } else if msgOps.recv.None? && msgOps.send.Some? {
        assert false;
      } else { // msgOps.recv.None? && msgOps.send.None?
        assert false;
      }
    } else if ValidCoordinatorId(v, hostId) { // must be coordinator
      var hostStep :| CoordinatorHost.NextStep(cv, cv', hostStep, msgOps);
      if msgOps.recv.Some? && msgOps.send.Some? {
        assert false;
      } else if msgOps.recv.Some? && msgOps.send.None? {
        var m := msgOps.recv.value;
        assert m.MsgVote?;
        assert hostStep.RecvVoteStep?;
        assert cv.decision == cv'.decision;
        assert forall i | ValidParticipantId(v, i) :: ParticipantVars(v, i) == ParticipantVars(v', i);
        assert SafetyAC1(v');
        assert SafetyAC3(v');
        assert SafetyAC4(v');
        assert VoteMsgImpliesPreference(v');
      } else if msgOps.recv.None? && msgOps.send.Some? {
        var m := msgOps.send.value;
        match m {
          case MsgReqVote => {
            var hostStep :| CoordinatorHost.NextStep(cv, cv', hostStep, msgOps);
            assert hostStep.ReqVoteStep?;
            assert CoordinatorHost.ReqVote(cv, cv', msgOps);
            assert cv == cv';
            assert forall i | ValidParticipantId(v, i) :: ParticipantVars(v, i) == ParticipantVars(v', i);
            assert SafetyAC1(v');
            assert SafetyAC3(v');
            assert SafetyAC4(v');
            assert VoteMsgImpliesPreference(v');
          }
          case MsgDecison(d) => {
            var hostStep :| CoordinatorHost.NextStep(cv, cv', hostStep, msgOps);
            assert hostStep.DecideAndSendStep?;
            assert CoordinatorHost.DecideAndSend(cv, cv', msgOps);

            {
              assert forall i: HostId | ValidParticipantId(v, i)
                  :: ParticipantVars(v, i).decision == ParticipantVars(v', i).decision;
              assert (forall i: HostId, j: HostId |
                        && ValidParticipantId(v', i)
                        && ValidParticipantId(v', j)
                        && ParticipantVars(v', i).decision.Some?
                        && ParticipantVars(v', j).decision.Some?
                        :: ParticipantVars(v', i).decision.value == ParticipantVars(v', j).decision.value);

              assert forall i: HostId | ValidParticipantId(v, i)
                  :: ParticipantVars(v, i).decision.None?;
              assert (forall i: HostId |
                        && ValidParticipantId(v', i)
                        && ParticipantVars(v', i).decision.Some?
                        && CoordinatorVars(v').decision.Some?
                        :: ParticipantVars(v', i).decision.value == CoordinatorVars(v').decision.value);
              assert SafetyAC1(v');
            }

            {
              if exists i: HostId :: ValidParticipantId(v', i) && ParticipantVars(v', i).c.preference == No {
                var i: HostId :| ValidParticipantId(v', i) && ParticipantVars(v', i).c.preference == No;
                assert cv'.votes[i].Some?;
                assert RecvVoteImpliesVoteMsgSent(v');
                assert forall m: Message | m in v'.network.sentMsgs && m.MsgVote? && m.p == i
                    :: m.vote == CoordinatorVars(v').votes[i].value;
                assert VoteMsgImpliesPreference(v');
                assert cv'.votes[i].value == No;
                assert m.d == Abort;
                assert cv'.decision.Some? && cv'.decision.value == Abort;
              }
              assert SafetyAC3(v');
            }

            {
              if forall i: HostId | ValidParticipantId(v', i) :: ParticipantVars(v', i).c.preference == Yes {
                var i: HostId :| ValidParticipantId(v', i);
                if CoordinatorVars(v').decision.Some? {
                  assert RecvVoteImpliesVoteMsgSent(v');
                  assert exists m: Message ::
                      && m in v'.network.sentMsgs
                      && m.MsgVote?
                      && m.p == i
                      && m.vote == CoordinatorVars(v').votes[i].value;
                  assert VoteMsgImpliesPreference(v');
                  assert forall m: Message | && m in v'.network.sentMsgs
                                             && m.MsgVote?
                                             && m.p == i
                      :: m.vote == ParticipantVars(v', i).c.preference;
                  assert CoordinatorVars(v').decision.value == Commit;
                }
              }

              assert (forall i: HostId | ValidParticipantId(v', i) :: ParticipantVars(v', i).c.preference == Yes)
                ==> (forall i: HostId | ValidParticipantId(v', i)
                       :: (ParticipantVars(v', i).decision.Some? ==> (ParticipantVars(v', i).decision.value == Commit))
                  );
              assert SafetyAC4(v');
            }
            assert VoteMsgImpliesPreference(v');
          }
          case _ => assert false;
        }
        assert SafetyAC1(v');
        assert SafetyAC3(v');
        assert SafetyAC4(v');
      } else { // msgOps.recv.None? && msgOps.send.None?
        assert false;
      }
    } else {
      assert false;
    }

    assert SafetyAC1(v');
    assert SafetyAC3(v');
    assert SafetyAC4(v');
    assert RecvVoteImpliesVoteMsgSent(v');
    assert VoteMsgImpliesPreference(v');
    // END EDIT
  }

  lemma InvImpliesSafety(v: Variables)
    requires Inv(v)
    ensures Safety(v)
  { // Trivial, as usual, since safety is a conjunct in Inv.
  }
}
