// Two Phase Commit Model
// Model a distributed protocol using compound state machines.

// Your goal is to model a 2-Phase Commit protocol. You're modeling a single
// instance of the problem -- a designated coordinator, no concurrent
// instances. Furthermore, you may assume there are no coordinator or
// participant failures. This is indeed a fairly simplistic setting, but it's
// still nontrivial, and is a nice example for reasoning about the
// state-machine composition framework.
//
// The input to the algorithm is that each participant has a Yes/No preference.
// The output is that each participant learns a decision value based on the
// collective preferences.
//
// 2-Phase Commit Protocol English design doc:
//
// 1, Coordinator sends VOTE-REQ to all participants.
// 2. Each participant i sends back Vote(vote_i) to coordinator according to its
//    local preference.
//    Optimization: if vote_i=No then i sets decision_i := Abort (rather than
//    waiting for a decision from the coordinator)
// 3. Coordinator collects votes.
//    If all votes are yes then coordinator sets local decision_c := Commit and
//    sends Commit to all participants.
//      else coordinator sets decision_c := Abort and sends Abort to all
//      participants who voted yes.
// 4. Participants receiving Commit set decision_i := Commit
//
// This file provides a lot of helpful framework. You only need to
// define Types.Message and then fill in the state machine types and actions
// in module CoordinatorHost and module ParticipantHost.
//
// Unlike chapter01, where you could work through each file sequentially,
// WE STRONGLY ENCOURAGE YOU to read the entire file before beginning
// work. Later pieces of the file are helpful, for example by explaining
// the network model you're working in.

include "UtilitiesLibrary.dfy"
include "CommitTypes.dfy"

module Types {
  import opened UtilitiesLibrary
  import opened CommitTypes

  type HostId = nat

  // Have to define our message datatype so network can refer to it.
  // (There are cleverer ways to parameterize the network module, but
  // we're trying to avoid getting fancy with the Dafny module system.)
  datatype Message =
      // FIXME: fill in here (solution: 3 lines)
    | MsgReqVote
    | MsgVote(p: HostId, vote: Vote)
    | MsgDecison(d: Decision)
      // END EDIT

  // A MessageOps is a "binding variable" used to connect a Host's Next step
  // (what message got received, what got sent?) with the Network (only allow
  // receipt of messages sent prior; record newly-sent messages).
  // Note that both fields are Option. A step predicate can say recv.None?
  // to indicate that it doesn't need to receive a message to occur.
  // It can say send.None? to indicate that it doesn't want to transmit a message.
  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
}

// There are two host roles in 2PCoordinator and Participant. We'll define
// separate state machines for each.
// This state machine defines how a coordinator host should behave: what state
// it records, and what actions it's allowed to take in response to incoming
// messages (or spontaneously by thinking about its existing state).
module CoordinatorHost {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary

  datatype Constants = Constants(participantCount: nat)

  datatype Variables = Variables(
    c: Constants,
    decision: Option<Decision>,
    // FIXME: fill in here (solution: 1 line)
    votes: seq<Option<Vote>>
    // END EDIT
  )
  {
    ghost predicate WF() {
      // FIXME: fill in here (solution: 1 line)
      |votes| == c.participantCount && c.participantCount > 0
      // END EDIT
    }

    ghost predicate HasParticipantCount(participantCount: nat)
    {
      c.participantCount == participantCount
    }
  }

  ghost predicate Init(v: Variables)
  {
    // FIXME: fill in here (solution: 5 lines)
    && v.WF()
    && v.decision.None?
    && forall i: HostId | i < |v.votes| :: v.votes[i].None?
                                           // END EDIT
  }

  // Protocol steps. Define an action predicate for each step of the protocol
  // that the coordinator is involved in.
  // Hint: it's probably easiest to separate the receipt and recording of
  // incoming votes from detecting that all have arrived and making a decision.
  // FIXME: fill in here (solution: 46 lines)
  ghost predicate ReqVote(v: Variables, v': Variables, msgOps: MessageOps)
  {
    && msgOps.recv.None?
    && msgOps.send.Some?
    && msgOps.send.value.MsgReqVote?
    && v.decision.None? // no point to request vote after the decision made
    && v == v'
  }

  ghost predicate RecvVote(v: Variables, v': Variables, msgOps: MessageOps)
  {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && msgOps.recv.value.MsgVote?
    && var p: HostId := msgOps.recv.value.p;
    && var vote := msgOps.recv.value.vote;
    && p < |v.votes|
    && v.votes[p] == None
    && v' == v.(votes := v.votes[p := Some(vote)])
  }

  ghost predicate DecideAndSend(v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send.Some?
    && v.decision.None?
    && (forall i: HostId | i < |v.votes| :: v.votes[i].Some?)
    && ((forall i: HostId | i < |v.votes| :: v.votes[i].value == Yes)
        ==> (&& v' == v.(decision := Some(Commit))
             && msgOps.send.value == MsgDecison(Commit))
       )
    && ((exists i: HostId :: i < |v.votes| && v.votes[i].value == No)
        ==> (&& v' == v.(decision := Some(Abort))
             && msgOps.send.value == MsgDecison(Abort))
       )
  }

  // END EDIT

  // JayNF
  datatype Step =
      // FIXME: fill in here (solution: 3 lines)
    | ReqVoteStep
    | RecvVoteStep
    | DecideAndSendStep
      // END EDIT

  // msgOps is a "binding variable" -- the host and the network have to agree
  // on its assignment to make a valid transition. So the host explains what
  // would happen if it could receive a particular message, and the network
  // decides whether such a message is available for receipt.
  ghost predicate NextStep(v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
    // FIXME: fill in here (solution: 3 lines)
    case ReqVoteStep => ReqVote(v, v', msgOps)
    case RecvVoteStep => RecvVote(v, v', msgOps)
    case DecideAndSendStep => DecideAndSend(v, v', msgOps)
    // END EDIT
  }

  lemma NextStepDeterministicGivenStep(v: Variables, v'1: Variables, v'2: Variables, step: Step, msgOps: MessageOps)
    requires NextStep(v, v'1, step, msgOps)
    requires NextStep(v, v'2, step, msgOps)
    ensures v'1 == v'2
  {}

  ghost predicate Next(v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(v, v', step, msgOps)
  }
}

module ParticipantHost {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary

  datatype Constants = Constants(hostId: HostId, preference: Vote)

  datatype Variables = Variables(c: Constants, decision: Option<Decision>)
  {
    ghost predicate WF() {
      // FIXME: fill in here (solution: 1 line)
      true
      // END EDIT
    }

    ghost predicate HasHostId(hostId: HostId)
    {
      c.hostId == hostId
    }
  }

  ghost predicate Init(v: Variables)
  {
    // FIXME: fill in here (solution: 1 line)
    && v.WF()
    && v.decision == None
       // END EDIT
  }

  // Protocol steps. Define an action predicate for each step of the protocol
  // that participant can take.
  // FIXME: fill in here (solution: 20 lines)
  // END EDIT

  ghost predicate CastVote(v: Variables, v': Variables, msgOps: MessageOps)
  {
    && msgOps.recv.Some?
    && msgOps.send.Some?
    && msgOps.recv.value.MsgReqVote?
    && msgOps.send.value.MsgVote?
    && msgOps.send.value.p == v.c.hostId
    && msgOps.send.value.vote == v.c.preference
    && v == v'
  }

  ghost predicate AcceptDecision(v: Variables, v': Variables, msgOps: MessageOps)
  {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && msgOps.recv.value.MsgDecison?
    && v.decision == None
    && v' == v.(decision := Some(msgOps.recv.value.d))
  }

  // JayNF
  datatype Step =
      // FIXME: fill in here (solution: 2 lines)
    | CastVoteStep
    | AcceptDecisionStep
      // END EDIT

  ghost predicate NextStep(v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
    // FIXME: fill in here (solution: 2 lines)
    case CastVoteStep => CastVote(v, v', msgOps)
    case AcceptDecisionStep => AcceptDecision(v, v', msgOps)
    // END EDIT
  }

  lemma NextStepDeterministicGivenStep(v: Variables, v'1: Variables, v'2: Variables, step: Step, msgOps: MessageOps)
    requires NextStep(v, v'1, step, msgOps)
    requires NextStep(v, v'2, step, msgOps)
    ensures v'1 == v'2
  {}

  ghost predicate Next(v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(v, v', step, msgOps)
  }
}

// We define a generic Host as able to be either of the specific roles.
// This is the ultimate (untrusted) definition of the protocol we're
// trying to verify.
// This definition is given to you to clarify how the two protocol roles above
// are pulled together into the ultimate distributed system.
module Host {
  import opened UtilitiesLibrary
  import opened CommitTypes
  import opened Types
  import CoordinatorHost
  import ParticipantHost

  datatype Variables =
    | CoordinatorVariables(coordinator: CoordinatorHost.Variables)
    | ParticipantVariables(participant: ParticipantHost.Variables)
  {
    ghost predicate WF() {
      // subtype WF satisfied
      && (match this
          case CoordinatorVariables(_) => coordinator.WF()
          case ParticipantVariables(_) => participant.WF()
      )
    }
  }

  // What property must be true of any group of hosts to run the protocol?
  // Generic DistributedSystem module calls back into this predicate to ensure
  // that it has a well-formed *group* of hosts.
  ghost predicate GroupWFConstants(grp: seq<Variables>)
  {
    // There must at least be a coordinator
    && 0 < |grp|
       // Last host is a coordinator
    && Last(grp).CoordinatorVariables?
       // All the others are participants
    && (forall hostid:HostId | hostid < |grp|-1 :: grp[hostid].ParticipantVariables?)
       // The coordinator's constants must correctly account for the number of participants
    && Last(grp).coordinator.HasParticipantCount(|grp|-1)
       // The participants's constants must match their group positions.
       // (Actually, they just need to be distinct from one another so we get
       // non-conflicting votes, but this is an easy way to express that property.)
    && (forall hostid:HostId | hostid < |grp|-1
          :: grp[hostid].participant.HasHostId(hostid))
  }

  ghost predicate GroupWF(grp_v: seq<Variables>)
  {
    && GroupWFConstants(grp_v)
       // Each host is well-formed
    && (forall hostid:HostId | hostid < |grp_v| :: grp_v[hostid].WF())
  }

  // Generic DistributedSystem module calls back into this predicate to give
  // the protocol an opportunity to set up constraints across the various
  // hosts.  Protocol requires one coordinator and the rest participants;
  // coordinator must know how many participants, and participants must know
  // own ids.
  ghost predicate GroupInit(grp_v: seq<Variables>)
  {
    // constants & variables are well-formed (same number of host slots as constants expect)
    && GroupWF(grp_v)
       // Coordinator is initialized to know about the N-1 participants.
    && CoordinatorHost.Init(Last(grp_v).coordinator)
       // Participants initted with their ids.
    && (forall hostid:HostId | hostid < |grp_v|-1 ::
          ParticipantHost.Init(grp_v[hostid].participant)
       )
  }

  // Dispatch Next to appropriate underlying implementation.
  ghost predicate Next(v: Variables, v': Variables, msgOps: MessageOps)
  {
    && v.WF()
       // needed to justify types below
    && v'.CoordinatorVariables? == v.CoordinatorVariables?
    && (match v
        case CoordinatorVariables(_) => CoordinatorHost.Next(v.coordinator, v'.coordinator, msgOps)
        case ParticipantVariables(_) => ParticipantHost.Next(v.participant, v'.participant, msgOps)
       )
  }
}

// The (trusted) model of the environment: There is a network that can only deliver
// messages that some Host (running the protocol) has sent, but once sent, messages
// can be delivered repeatedly and in any order.
// This definition is given to you because it's a common assumption you can
// reuse. Someday you might decide to assume a different network model (e.g.
// reliable or at-most-once delivery), but this is a good place to start.
module Network {
  import opened CommitTypes
  import opened Types

  // Network state is the set of messages ever sent. Once sent, we'll
  // allow it to be delivered over and over.
  // (We don't have packet headers, so duplication, besides being realistic,
  // also doubles as how multiple parties can hear the message.)
  datatype Variables = Variables(sentMsgs:set<Message>)

  ghost predicate Init(v: Variables)
  {
    && v.sentMsgs == {}
  }

  ghost predicate Next(v: Variables, v': Variables, msgOps: MessageOps)
  {
    // Only allow receipt of a message if we've seen it has been sent.
    && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
       // Record the sent message, if there was one.
    && v'.sentMsgs ==
       v.sentMsgs + if msgOps.send.None? then {} else { msgOps.send.value }
  }
}

// The (trusted) model of the distributed system: hosts don't share memory. Each
// takes its steps independently, interleaved in nondeterministic order with others.
// They only communicate through the network, and obey the communication model
// established by the Network model.
// This is given to you; it can be reused for just about any shared-nothing-concurrency
// protocol model.
module DistributedSystem {
  import opened UtilitiesLibrary
  import opened CommitTypes
  import opened Types
  import Network
  import Host
  import CoordinatorHost
  import ParticipantHost

  datatype Variables = Variables(
    hosts: seq<Host.Variables>,
    network: Network.Variables)
  {
    ghost predicate ValidHostId(id: HostId) {
      id < |hosts|
    }

    ghost predicate WF() {
      && Host.GroupWF(hosts)
    }
  }

  ghost predicate Init(v: Variables)
  {
    && v.WF()
    && Host.GroupInit(v.hosts)
    && Network.Init(v.network)
  }

  ghost predicate HostAction(v: Variables, v': Variables, hostid: HostId, msgOps: MessageOps)
  {
    && v.WF()
    && v.ValidHostId(hostid)
    && |v'.hosts| == |v.hosts|
    && Host.Next(v.hosts[hostid], v'.hosts[hostid], msgOps)
       // all other hosts UNCHANGED
    && (forall otherHost:nat | v.ValidHostId(otherHost) && otherHost != hostid :: v'.hosts[otherHost] == v.hosts[otherHost])
  }

  // JayNF is pretty simple as there's only a single action disjunct
  datatype Step =
    | HostActionStep(hostId: HostId, msgOps: MessageOps)

  ghost predicate NextStep(v: Variables, v': Variables, step: Step)
  {
    && HostAction(v, v', step.hostId, step.msgOps)
       // network agrees recv has been sent and records sent
    && Network.Next(v.network, v'.network, step.msgOps)
  }

  ghost predicate Next(v: Variables, v': Variables)
  {
    exists step :: NextStep(v, v', step)
  }

  ghost function GetDecisionForHost(hv: Host.Variables) : Option<Decision>
  {
    match hv
    case CoordinatorVariables(coordinator) => coordinator.decision
    case ParticipantVariables(participant) => participant.decision
  }

  // Convince us that your model does something
  lemma PseudoLiveness() returns (behavior: seq<Variables>)
    // requires |c.hosts| == 2 // There's exactly one voting participant...
    // requires c.hosts[0].participant.preference.Yes? // ... who wants a Yes.
    // Exhibit a behavior that satisfies your state machine...
    ensures 0 < |behavior|
    ensures Init(behavior[0])
    ensures forall i:nat | i < |behavior|-1 :: Next(behavior[i], behavior[i+1])
    // ...and all the participants arrive at a decision.
    ensures Last(behavior).WF()
    ensures forall hostid:HostId | Last(behavior).ValidHostId(hostid)
              :: GetDecisionForHost(Last(behavior).hosts[hostid]) == Some(Commit)
  {
    // FIXME: fill in here (solution: 60 lines)
    var v0 := Variables(hosts := [
                          Host.ParticipantVariables(
                            participant := ParticipantHost.Variables(
                              c := ParticipantHost.Constants(hostId := 0,
                                                             preference := Yes),
                              decision := None)),
                          Host.CoordinatorVariables(
                            coordinator := CoordinatorHost.Variables(
                              c := CoordinatorHost.Constants(participantCount := 1),
                              decision := None,
                              votes := [None]))
                        ],
                        network := Network.Variables({}));
    var v1 := v0.(
    network := Network.Variables(
      sentMsgs := {MsgReqVote}));
    assert CoordinatorHost.NextStep(v0.hosts[1].coordinator,
                                    v1.hosts[1].coordinator,
                                    CoordinatorHost.ReqVoteStep,
                                    MessageOps(recv := None, send := Some(MsgReqVote)));
    assert NextStep(v0, v1, HostActionStep(1, MessageOps(recv := None, send := Some(MsgReqVote))));

    var v2 := v1.(
    network := Network.Variables(
      sentMsgs := {MsgReqVote, MsgVote(0, Yes)}));
    assert ParticipantHost.NextStep(v1.hosts[0].participant,
                                    v2.hosts[0].participant,
                                    ParticipantHost.CastVoteStep,
                                    MessageOps(recv := Some(MsgReqVote), send := Some(MsgVote(0, Yes))));
    assert NextStep(v1, v2, HostActionStep(0, MessageOps(recv := Some(MsgReqVote), send := Some(MsgVote(0, Yes)))));

    var v3 := v2.(
    hosts := v2.hosts[1 := v2.hosts[1].(coordinator := v2.hosts[1].coordinator.(votes := [Some(Yes)]))]
    );
    assert CoordinatorHost.NextStep(v2.hosts[1].coordinator,
                                    v3.hosts[1].coordinator,
                                    CoordinatorHost.RecvVoteStep,
                                    MessageOps(recv := Some(MsgVote(0, Yes)), send := None));
    assert NextStep(v2, v3, HostActionStep(1, MessageOps(recv := Some(MsgVote(0, Yes)), send := None)));

    var v4 := v3.(
    hosts := v3.hosts[1 := v3.hosts[1].(coordinator := v3.hosts[1].coordinator.(decision := Some(Commit)))],
    network := Network.Variables(
      sentMsgs := {MsgReqVote, MsgVote(0, Yes), MsgDecison(Commit)})
    );
    assert CoordinatorHost.NextStep(v3.hosts[1].coordinator,
                                    v4.hosts[1].coordinator,
                                    CoordinatorHost.DecideAndSendStep,
                                    MessageOps(recv := None, send := Some(MsgDecison(Commit))));
    assert NextStep(v3, v4, HostActionStep(1, MessageOps(recv := None, send := Some(MsgDecison(Commit)))));

    var v5 := v4.(
    hosts := v4.hosts[0 := v4.hosts[0].(participant := v4.hosts[0].participant.(decision := Some(Commit)))]
    );
    assert ParticipantHost.NextStep(v4.hosts[0].participant,
                                    v5.hosts[0].participant,
                                    ParticipantHost.AcceptDecisionStep,
                                    MessageOps(recv := Some(MsgDecison(Commit)), send := None));
    assert NextStep(v4, v5, HostActionStep(0, MessageOps(recv := Some(MsgDecison(Commit)), send := None)));

    behavior := [v0, v1, v2, v3, v4, v5];
    // END EDIT
  }
}
