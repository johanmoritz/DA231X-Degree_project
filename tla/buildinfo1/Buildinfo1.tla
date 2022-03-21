---- MODULE Buildinfo1 ----
EXTENDS Integers, TLC, FiniteSets, Sequences

(*--algorithm ChainCode
variables
  Data = "data",
  ID = 1..3,
  Version = 1..3,
  worldState = [x \in {} |-> Data],
  readSet = [x \in {} |-> ReadSetObject],
  writeSet = [x \in {} |-> WriteSetObject],
  testOutput,

define
    ReadSetType == readSet = <<>> \/ (\A key \in DOMAIN readSet: readSet[key].id \in 1..3 /\ readSet[key].version \in 1..3)
    WriteSetType == writeSet = <<>> \/ (\A key \in DOMAIN writeSet: writeSet[key].id \in 1..3 /\ writeSet[key].data \in {"a", "b"})
    FinishedState == <>[](testOutput = "a") /\ <>[](writeSet = <<>> \/ writeSet[2].data = "b")

    DelKey(id, state) == LET  newKeys == DOMAIN state \ {id} IN [key \in newKeys |-> state[key]]
    PutKey(id, data, state) == [x \in (DOMAIN state \union {id}) |->
        IF x = id THEN data ELSE state[x]]
    GetKey(id, state) == state[id]

    ReadSetObject == [id |-> ID, version |-> Version]
    WriteSetObject == [id |-> ID, data |-> Data]
end define;

macro ReadState1(id, state, out) begin
    with value = GetKey(id, state) do
        readSet := PutKey(id, [id |-> value.id, version |-> value.version], readSet);
        out := value.data;
    end with;
end macro;

macro WriteState1(id, data) begin
    writeSet := PutKey(id, [id |-> id, data |-> data], writeSet)
end macro;

fair process q = "q"
begin
    Go: 
        worldState := PutKey(1, [id |-> 1, data |-> "a", version |-> 1], worldState);
        ReadState1(1, worldState, testOutput);
        WriteState1(2, "b");
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "b472d0c0" /\ chksum(tla) = "5b63db80")
CONSTANT defaultInitValue
VARIABLES Data, ID, Version, worldState, readSet, writeSet, testOutput, pc

(* define statement *)
ReadSetType == readSet = <<>> \/ (\A key \in DOMAIN readSet: readSet[key].id \in 1..3 /\ readSet[key].version \in 1..3)
WriteSetType == writeSet = <<>> \/ (\A key \in DOMAIN writeSet: writeSet[key].id \in 1..3 /\ writeSet[key].data \in {"a", "b"})
FinishedState == <>[](testOutput = "a") /\ <>[](writeSet = <<>> \/ writeSet[2].data = "b")

DelKey(id, state) == LET  newKeys == DOMAIN state \ {id} IN [key \in newKeys |-> state[key]]
PutKey(id, data, state) == [x \in (DOMAIN state \union {id}) |->
    IF x = id THEN data ELSE state[x]]
GetKey(id, state) == state[id]

ReadSetObject == [id |-> ID, version |-> Version]
WriteSetObject == [id |-> ID, data |-> Data]


vars == << Data, ID, Version, worldState, readSet, writeSet, testOutput, pc
        >>

ProcSet == {"q"}

Init == (* Global variables *)
        /\ Data = "data"
        /\ ID = 1..3
        /\ Version = 1..3
        /\ worldState = [x \in {} |-> Data]
        /\ readSet = [x \in {} |-> ReadSetObject]
        /\ writeSet = [x \in {} |-> WriteSetObject]
        /\ testOutput = defaultInitValue
        /\ pc = [self \in ProcSet |-> "Go"]

Go == /\ pc["q"] = "Go"
      /\ worldState' = PutKey(1, [id |-> 1, data |-> "a", version |-> 1], worldState)
      /\ LET value == GetKey(1, worldState') IN
           /\ readSet' = PutKey(1, [id |-> value.id, version |-> value.version], readSet)
           /\ testOutput' = value.data
      /\ writeSet' = PutKey(2, [id |-> 2, data |-> "b"], writeSet)
      /\ pc' = [pc EXCEPT !["q"] = "Done"]
      /\ UNCHANGED << Data, ID, Version >>

q == Go

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == q
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(q)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
