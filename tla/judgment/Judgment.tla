---- MODULE Judgment ----
EXTENDS TLC, FiniteSets, Integers


(*--algorithm Judgment

variables
    hashMessage = [b \in Builders |-> ""],
    result = "unknown",
    status = "commit"


define
NULL == ""
Builders == {"b1", "b2", "b3"}
Reproduceability == "reproducible"
Phases == {"commit", "verify", "done"}

Safety == result = "unknown" \/ result = Reproduceability

Range(f) == {f[x] : x \in DOMAIN f}

end define;

fair process builder \in Builders
begin Judgment:
    while status # "done" do
        if status = "commit" then
            \* Commit chaincode
            if \A b \in Builders: hashMessage[b] # NULL then
                status := "verify";
            else
                hashMessage[self] := Reproduceability
            end if;
        elsif status = "verify" then
            \* Verify chaincode 
            with 
                reproducibleVotes = Cardinality({v \in Range(hashMessage): v = "reproducible"}),
                notReproducibleVotes = Cardinality({v \in Range(hashMessage): v = "non-reproducible"})
            do
                if reproducibleVotes > notReproducibleVotes then
                    result := "reproducible";
                else
                    result := "non-reproducible";
                end if;
                status := "done";
            end with;
        end if;
    end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "254044d8" /\ chksum(tla) = "77458937")
VARIABLES hashMessage, result, status, pc

(* define statement *)
NULL == ""
Builders == {"b1", "b2", "b3"}
Reproduceability == "reproducible"
Phases == {"commit", "verify", "done"}

Safety == result = "unknown" \/ result = Reproduceability

Range(f) == {f[x] : x \in DOMAIN f}


vars == << hashMessage, result, status, pc >>

ProcSet == (Builders)

Init == (* Global variables *)
        /\ hashMessage = [b \in Builders |-> ""]
        /\ result = "unknown"
        /\ status = "commit"
        /\ pc = [self \in ProcSet |-> "Judgment"]

Judgment(self) == /\ pc[self] = "Judgment"
                  /\ IF status # "done"
                        THEN /\ IF status = "commit"
                                   THEN /\ IF \A b \in Builders: hashMessage[b] # NULL
                                              THEN /\ status' = "verify"
                                                   /\ UNCHANGED hashMessage
                                              ELSE /\ hashMessage' = [hashMessage EXCEPT ![self] = Reproduceability]
                                                   /\ UNCHANGED status
                                        /\ UNCHANGED result
                                   ELSE /\ IF status = "verify"
                                              THEN /\ LET reproducibleVotes == Cardinality({v \in Range(hashMessage): v = "reproducible"}) IN
                                                        LET notReproducibleVotes == Cardinality({v \in Range(hashMessage): v = "non-reproducible"}) IN
                                                          /\ IF reproducibleVotes > notReproducibleVotes
                                                                THEN /\ result' = "reproducible"
                                                                ELSE /\ result' = "non-reproducible"
                                                          /\ status' = "done"
                                              ELSE /\ TRUE
                                                   /\ UNCHANGED << result, 
                                                                   status >>
                                        /\ UNCHANGED hashMessage
                             /\ pc' = [pc EXCEPT ![self] = "Judgment"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                             /\ UNCHANGED << hashMessage, result, status >>

builder(self) == Judgment(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Builders: builder(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Builders : WF_vars(builder(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
