---- MODULE Judgment3 ----
EXTENDS TLC, FiniteSets, Reals, Sequences

VARIABLE public, private, packages


Nodes == {"node1", "node2"}

Packages == {"package1", "package2", "package3"}

Status == {"active", "initialized"}

IsReproducible == [package1 |-> TRUE, package2 |-> FALSE, package3 |-> TRUE]

Range(f) == {f[k]: k \in DOMAIN f}

KeyValues(m) == {<<k, m[k]>> : k \in DOMAIN m}

InitialPrivate == private = [
    node1 |-> [
        judgements |-> <<>>,
        preferences |-> <<>>
    ]
]

InitialPublic == public = [
    nodes |-> [
        node1 |-> [wallet |-> 10],
        node2 |-> [wallet |-> 20]
    ],
    \* judgments |-> <<
    \*     [id |-> "0", package |-> "p1", owner |-> "node1", status |-> "active", maxCost |-> 10],
    \*     [id |-> "1", package |-> "p1", owner |-> "node2", status |-> "active", maxCost |-> 15]
    \* >>
    judgments |-> <<>>
]

RECURSIVE Cost(_)
Cost(level) == IF level = 0 THEN 0 ELSE level + Cost(level - 1 )


\* ======== Chaincode ======== 

InitializeJudgment(package, owner, maxCost) == 
    \* Guards
    /\ maxCost <= public.nodes[owner].wallet
    /\ (\A j \in Range(public.judgments): j.status = "active" => j.owner # owner)
    \* Update
    \* TODO: Better ids. Currently there can only be one judgment per package.
    /\ LET judgmentId == package IN
        public' = [public EXCEPT !.judgments = Append(@,
                    [   id |-> judgmentId, 
                        package |-> package, 
                        owner |-> owner, 
                        maxCost |-> maxCost, 
                        status |-> "active",
                        secretJudgments |-> <<>>])]

AddSecretJudgment(judgmentId, judge, secretVote) ==
    \/  Len(public.judgments) = 0
    \/  \E index \in DOMAIN public.judgments: 
            LET j == public.judgments[index] IN 
                /\  j.id = judgmentId
                /\ j.status = "active"
                \* Too expensive for the owner?
                /\ Cost(Len(j.secretJudgments) + 1) <= j.maxCost
                \* Has 'judge' added their vote before?
                /\ {sj \in Range(j.secretJudgments): sj.judge = judge} = {}
                \* Update
                /\  public' = [public EXCEPT !.judgments = [@ EXCEPT ![index] =
                    [@ EXCEPT !.secretJudgments = Append(@, 
                        [   judge |-> judge, 
                            vote |-> secretVote])]]] 


\* ======== Invariants ======== 

OwnOneJudgmentAtATime == 
    \* For all active judgments j, j2 where j # j2: j.owner # j2.owner
    \* Needed to ensure that judgments can be paid for.
    \A j \in Range(public.judgments) : j.status = "active" => 
        (\A j2 \in Range(public.judgments): j2.status = "active" /\
            j.id # j2.id => j.owner # j2.owner)

LessActiveThenNodes == 
    \* There should never be more active judgments than nodes
    LET active == {j \in Range(public.judgments) : j.status = "active"}
    IN  Cardinality(active) <= Cardinality(Nodes)

CostLessThanMaxCost ==
    \/  Len(public.judgments) = 0
    \/  \A j \in Range(public.judgments) : Cost(Len(j.secretJudgments)) <= j.maxCost

\* ======== Spec ======== 

Init == 
    /\ InitialPublic
    /\ InitialPrivate
    /\ packages = Packages
Next == 
    \/  \E n \in Nodes:
        \E p \in packages: 
            /\ InitializeJudgment(p, n, 10)
            /\ packages' = packages \ {p}
            /\ UNCHANGED private    
    \/  \E n \in Nodes:
        \E j \in Range(public.judgments):
            LET secretVote == IsReproducible[j.package] IN
            /\ AddSecretJudgment(j.id, n, secretVote)
            /\ UNCHANGED <<private, packages>>
    \/  /\  Cardinality(packages) = 0
        /\ UNCHANGED <<public, private, packages>>

Spec == Init /\ [][Next]_<<public, private, packages>>


====