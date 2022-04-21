---- MODULE Judgment3 ----
EXTENDS TLC, FiniteSets, Reals, Sequences

VARIABLE public, private, packages


Nodes == {"node1", "node2", "node3"}

Packages == {"package1", "package2", "package3", "package3"}

Status == {"active", "initialized"}

IsReproducible == [package1 |-> TRUE, package2 |-> FALSE, package3 |-> TRUE, package4 |-> TRUE, package5 |-> TRUE, package6 |-> TRUE]

Range(f) == {f[k]: k \in DOMAIN f}

KeyValues(m) == {<<k, m[k]>> : k \in DOMAIN m}

\* Source: https://learntla.com/libraries/sets/
Pick(S) == CHOOSE s \in S : TRUE
RECURSIVE SetReduce(_, _, _)
SetReduce(Op(_, _), S, value) == IF S = {} THEN value
                              ELSE LET s == Pick(S)
                              IN SetReduce(Op, S \ {s}, Op(s, value)) 

Sum(S) == 
    LET _op(a, b) == a + b
    IN  SetReduce(_op, S, 0)

InitialPrivate == private = [
    node1 |-> [
        preferences |-> <<
            [package |-> "package1", level |-> 2, status |-> "not-processed"]
        >>
    ],
    node2 |-> [
        preferences |-> <<
            [package |-> "package2", level |-> 1, status |-> "not-processed"],
            [package |-> "package3", level |-> 2, status |-> "not-processed"],
            [package |-> "package4", level |-> 2, status |-> "not-processed"]
        >>
    ],
    node3 |-> [
        preferences |-> <<
            [package |-> "package5", level |-> 3, status |-> "not-processed"],
            [package |-> "package6", level |-> 3, status |-> "not-processed"]
        
        >>
    ]
]

InitialPublic == public = [
    nodes |-> [
        node1 |-> [wallet |-> 0],
        node2 |-> [wallet |-> 0],
        node3 |-> [wallet |-> 6]
    ],
    judgments |-> <<>>
]

RECURSIVE Cost(_)
Cost(level) == IF level = 0 THEN 0 ELSE level + Cost(level - 1 )


RECURSIVE WalletUpdatesFromVotes(_, _)
WalletUpdatesFromVotes(votes, updates) ==
    IF Len(votes) = 0 
        THEN updates
        ELSE LET 
                reward == Len(votes) + 1
                judge == Head(votes).judge
                newUpdates == [updates EXCEPT ![judge].wallet = @ + reward]
            IN WalletUpdatesFromVotes(Tail(votes), newUpdates)

\* Base reward on timing of open vote
Rewards(judgment) == 
    LET updates == WalletUpdatesFromVotes(judgment.openJudgments, [n \in Nodes |-> public.nodes[n]])
        cost == Cost(Len(judgment.openJudgments))
    IN  [updates EXCEPT ![judgment.owner].wallet = @ - cost]


FutureCost(node) ==
    Sum({Cost(p.level) : p \in Range(private[node].preferences)})


\* ======== Chaincode ======== 

InitializeJudgment(package, owner, targetCost) == 
    \* Guards
    /\ targetCost <= public.nodes[owner].wallet
    /\ (\A j \in Range(public.judgments): j.status = "active" => j.owner # owner)
    \* Update
    \* TODO: Better ids. Currently there can only be one judgment per package.
    /\ LET judgmentId == package IN
        public' = [public EXCEPT !.judgments = Append(@,
                    [   id |-> judgmentId, 
                        package |-> package, 
                        owner |-> owner, 
                        targetCost |-> targetCost, 
                        status |-> "active",
                        phase |-> "secretVotes",
                        secretJudgments |-> <<>>,
                        openJudgments |-> <<>>])]

AddSecretJudgment(judgmentId, judge, secretVote) ==
    \/  Len(public.judgments) = 0
    \/  \E index \in DOMAIN public.judgments: 
            LET j == public.judgments[index] IN 
                /\  j.id = judgmentId
                /\ j.status = "active"
                /\ j.phase = "secretVotes"
                \* Too expensive for the owner?
                /\ Cost(Len(j.secretJudgments) + 1) <= j.targetCost
                \* Has 'judge' added their vote before?
                /\ {sj \in Range(j.secretJudgments): sj.judge = judge} = {}
                \* Update
                /\  public' = [public EXCEPT !.judgments = [@ EXCEPT ![index] =
                    [@ EXCEPT !.secretJudgments = Append(@, 
                        [   judge |-> judge, 
                            vote |-> secretVote])]]] 

EndSecretSubmissions(judgmentId, owner) ==
    \/ Len(public.judgments) = 0
    \/ \E index \in DOMAIN public.judgments:
        LET j == public.judgments[index] IN
            /\ j.id = judgmentId
            /\ j.status = "active"
            /\ j.phase = "secretVotes"
            /\ j.owner = owner
            /\ j.targetCost = Cost(Len(j.secretJudgments))
            /\ public' = [public EXCEPT !.judgments = [@ EXCEPT ![index] =
                [@ EXCEPT !.phase = "openVotes"]]]

ShowJudgment(judgmentId, judge, openVote) ==
    \/  Len(public.judgments) = 0
    \/  \E index \in DOMAIN public.judgments: 
            LET j == public.judgments[index] IN 
                /\ j.id = judgmentId
                /\ j.status = "active"
                /\ j.phase = "openVotes"
                \* Has 'judge' added their vote before?
                /\ {sj \in Range(j.secretJudgments): sj.judge = judge} # {}
                \* Has 'judge' showed their vote before?
                /\ {oj \in Range(j.openJudgments): oj.judge = judge} = {}
                \* Update
                /\  public' = [public EXCEPT !.judgments = [@ EXCEPT ![index] =
                    [@ EXCEPT !.openJudgments = Append(@, 
                        [   judge |-> judge, 
                            vote |-> openVote])]]] 


CloseJudgment(judgmentId, owner) ==
    \/  Len(public.judgments) = 0
    \/  \E index \in DOMAIN public.judgments:
            LET j == public.judgments[index] IN
                /\  j.id = judgmentId
                /\  j.status = "active"
                /\  j.phase = "openVotes"
                /\  j.owner = owner
                /\ j.targetCost = Cost(Len(j.openJudgments))
                /\  public' = [public EXCEPT 
                        !.judgments = [@ EXCEPT ![index] = 
                             [@ EXCEPT !.status = "closed", !.phase = "judgment"]],
                        !.nodes = Rewards(j)]
                        

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
    \/  \A j \in Range(public.judgments) : Cost(Len(j.secretJudgments)) <= j.targetCost

\* AllButOnePackagedIsJudgedPerNode == \A n \in Nodes: 
\*         Cardinality({p \in Range(private[n].preferences): p.status = "not-processed"}) <= 1

\* Fairness == WF_public(AllButOnePackagedIsJudgedPerNode)

\* ======== Spec ======== 

Init == 
    /\ InitialPublic
    /\ InitialPrivate
    /\ packages = Packages
Next == 
    \/  \E n \in Nodes:
        \E index \in DOMAIN private[n].preferences: 
            LET p == private[n].preferences[index] IN
                /\ p.status = "not-processed"
                /\ InitializeJudgment(p.package, n, Cost(p.level))
                /\ private' = [private EXCEPT   ![n] = [@ EXCEPT 
                                                !.preferences = [@ EXCEPT 
                                                ![index] = [@ EXCEPT 
                                                !.status = "started"]]]]
                /\ UNCHANGED packages    
    \/  \E n \in Nodes:
        \E j \in Range(public.judgments):
            LET secretVote == IsReproducible[j.package] IN
            \* Nodes only build/judge if they have to  
            /\  \/  FutureCost(n) > public.nodes[n].wallet
                \/  j.package \in {p.package : p \in Range(private[n].preferences)}
            /\  AddSecretJudgment(j.id, n, secretVote)
            /\  UNCHANGED <<private, packages>>
    \/  \E n \in Nodes:
        \E j \in Range(public.judgments):
            /\  EndSecretSubmissions(j.id, n)
            /\ UNCHANGED <<private, packages>>
    \/  \E n \in Nodes:
        \E j \in Range(public.judgments):
            LET openVote == IsReproducible[j.package] IN
            /\ ShowJudgment(j.id, n, openVote)
            /\ UNCHANGED <<private, packages>>
    \/  \E n \in Nodes:
        \E j \in Range(public.judgments):
            /\  CloseJudgment(j.id, n)
            /\  \E preferenceIndex \in DOMAIN private[n].preferences:
                    /\  private[n].preferences[preferenceIndex].package = j.package
                    /\  private' = [private EXCEPT ![n].preferences[preferenceIndex].status = "processed"]
            /\ UNCHANGED  <<packages>>
    \/  /\  \E n \in Nodes: 
                Cardinality({p \in Range(private[n].preferences): p.status = "not-processed"}) = 0
        /\ UNCHANGED <<public, private, packages>>

Spec == Init /\ [][Next]_<<public, private, packages>>


====