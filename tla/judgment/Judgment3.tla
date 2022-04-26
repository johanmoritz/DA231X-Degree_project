---- MODULE Judgment3 ----
EXTENDS TLC, FiniteSets, Reals, Sequences

VARIABLE public, private, packages

\* How to run:
\* alias tlc="java -XX:+UseParallelGC -Xmx12g -cp tla2tools.jar tlc2.TLC -workers auto" 
\* tlc -config Judgment3.cfg Judgment3.tla


Nodes == {"node1", "node2", "node3", "node4"}

Packages == {"package1", "package2", "package3", "package3"}

Status == {"active", "initialized"}

IsReproducible == [package1 |-> "TRUE", package2 |-> "FALSE", package3 |-> "TRUE", package4 |-> "TRUE", package5 |-> "TRUE", package6 |-> "TRUE", package7 |-> "TRUE", package8 |-> "TRUE"]

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
            [package |-> "package1", level |-> 2, status |-> "not-processed"],
            [package |-> "package2", level |-> 2, status |-> "not-processed"]
            \* [package |-> "package3", level |-> 2, status |-> "not-processed"]
        >>
    ],
    node2 |-> [
        preferences |-> <<
            \* [package |-> "package4", level |-> 2, status |-> "not-processed"],
            [package |-> "package3", level |-> 2, status |-> "not-processed"],
            [package |-> "package4", level |-> 2, status |-> "not-processed"]
        >>
    ],
    node3 |-> [
        preferences |-> <<
            [package |-> "package5", level |-> 2, status |-> "not-processed"],
            [package |-> "package6", level |-> 2, status |-> "not-processed"]
        
        >>
    ],
    node4 |-> [
        preferences |-> <<
            [package |-> "package7", level |-> 2, status |-> "not-processed"],
            [package |-> "package8", level |-> 2, status |-> "not-processed"]
        
        >>
    ]
]

InitialPublic == public = [
    nodes |-> [
        node1 |-> [wallet |-> 3],
        node2 |-> [wallet |-> 1],
        node3 |-> [wallet |-> 1],
        node4 |-> [wallet |-> 1]
    ],
    judgments |-> <<>>
]

RECURSIVE Cost(_)
Cost(level) == IF level = 0 THEN 0 ELSE level + Cost(level - 1 )


RECURSIVE WalletUpdatesFromVotes(_, _, _)
WalletUpdatesFromVotes(judgment, votes, updates) ==
    IF Len(votes) = 0 
        THEN updates
        ELSE LET 
                finalResult == ToString(judgment.tally.for > judgment.tally.against)
                judge == Head(votes).judge
                \* We add '1' for free (but not to the owner)
                participationReward == IF judge = judgment.owner THEN 0 ELSE 1
                positionalReward == Cardinality({v \in Range(votes) : v.vote = finalResult})
                reward == IF Head(votes).vote = finalResult 
                            THEN participationReward + positionalReward
                            ELSE 0 
                newUpdates == [updates EXCEPT ![judge].wallet = @ + reward]
            IN WalletUpdatesFromVotes(judgment, Tail(votes), newUpdates)

\* Base reward on timing of open vote
Rewards(judgment) == 
    LET updates == WalletUpdatesFromVotes(judgment, judgment.openJudgments, [n \in Nodes |-> public.nodes[n]])
        cost == Cost(Len(judgment.openJudgments))
        \* Owners don't get the additional '1'
    IN  [updates EXCEPT ![judgment.owner].wallet = @ - cost]


FutureCost(node) ==
    Sum({Cost(p.level) : p \in Range(private[node].preferences)})


\* ======== Chaincode ======== 

InitializeJudgment(package, owner, targetVotes) == 
    \* Guards
    /\ Cost(targetVotes) <= public.nodes[owner].wallet
    /\ (\A j \in Range(public.judgments): j.status = "active" => j.owner # owner)
    \* Update
    \* TODO: Better ids. Currently there can only be one judgment per package.
    /\ LET judgmentId == package IN
        public' = [public EXCEPT !.judgments = Append(@,
                    [   id |-> judgmentId, 
                        tally |-> [for |-> 0, against |-> 0],
                        finalResult |-> "undecided",
                        package |-> package, 
                        owner |-> owner, 
                        targetVotes |-> targetVotes, 
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
                \* Should be able to create a majority with j.targetVotes #votes
                /\ Len(j.secretJudgments) + 1 < 2 * j.targetVotes
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
            \* Should this be in the smart contract?
            /\ 2 * j.targetVotes - 1 = Len(j.secretJudgments)
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
                \* Secret and open votes should be the same
                \* This validation is done with HMAC in practice
                /\ \E sj \in Range(j.secretJudgments): 
                    /\  sj.judge = judge 
                    /\  openVote = sj.vote
                \* No majority yet!
                /\ 2 * j.tally.for <= Len(j.secretJudgments)
                /\ 2 * j.tally.against <= Len(j.secretJudgments)
                \* Update
                /\  public' = [public EXCEPT !.judgments[index] = [@ EXCEPT
                                !.openJudgments = Append(@, 
                                    [   judge |-> judge, 
                                        vote |-> openVote]),
                                !.tally.for = IF openVote = "TRUE" THEN @ + 1 ELSE @,
                                !.tally.against = IF openVote = "FALSE" THEN @ + 1 ELSE @]] 


CloseJudgment(judgmentId, owner) ==
    \/  Len(public.judgments) = 0
    \/  \E index \in DOMAIN public.judgments:
            LET j == public.judgments[index]
                finalResult == ToString(j.tally.for > j.tally.against) IN
                /\  j.id = judgmentId
                /\  j.status = "active"
                /\  j.phase = "openVotes"
                /\  j.owner = owner
                    \* Undecided result, majority FOR, or majority AGAINST
                /\  \/ Len(j.openJudgments) = Len(j.secretJudgments) 
                    \/ 2 * j.tally.for > Len(j.secretJudgments)
                    \/ 2 * j.tally.against > Len(j.secretJudgments)
                    \* We have a majority for!
                /\  \/  /\  2 * j.tally.for > Len(j.secretJudgments)
                        /\  public' = [public EXCEPT 
                                !.judgments = [@ EXCEPT ![index] = 
                                    [@ EXCEPT 
                                        !.status = "closed", 
                                        !.phase = "judgment",
                                        !.finalResult = "TRUE"]],
                                !.nodes = Rewards(j)]
                    \* We have a majority against!
                    \/  /\  2 * j.tally.against > Len(j.secretJudgments)
                        /\  public' = [public EXCEPT 
                                !.judgments = [@ EXCEPT ![index] = 
                                    [@ EXCEPT 
                                        !.status = "closed", 
                                        !.phase = "judgment",
                                        !.finalResult = "FALSE"]],
                                !.nodes = Rewards(j)]
                    \* Everyone has voted, and we don't have a majority
                    \/  /\  Len(j.openJudgments) = Len(j.secretJudgments) 
                        /\  public' = [public EXCEPT !.judgments[index] = [@ EXCEPT 
                                    !.status = "closed",
                                    !.finalResult = "undecided"]]
                    \* /\  PrintT("Majority: " \o ToString(public'.judgments[index].tally.for) \o " to " \o ToString(public'.judgments[index].tally.against))
                        

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

\* TODO: Add filtering so this one works
CostLessThanMaxCost ==
    \/  Len(public.judgments) = 0
    \/  \A j \in Range(public.judgments) : Len(j.secretJudgments) <= j.targetVotes

AllButOnePackagedIsJudgedPerNode == \A n \in Nodes: 
        Cardinality({p \in Range(private[n].preferences): p.status = "not-processed"}) <= 1

NoPackagesAreWronglyJudged == 
    \A j \in Range(public.judgments): 
        \/  j.finalResult = IsReproducible[j.id]
        \/  j.finalResult = "undecided"


Fairness == WF_public(AllButOnePackagedIsJudgedPerNode)

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
                /\ InitializeJudgment(p.package, n, p.level)
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
            /\  \/  FutureCost(n) > public.nodes[n].wallet
                \/  j.package \in {p.package : p \in Range(private[n].preferences)}
            /\ ShowJudgment(j.id, n, openVote)
            /\ UNCHANGED <<private, packages>>
    \/  \E n \in Nodes:
        \E j \in Range(public.judgments):
            /\  CloseJudgment(j.id, n)
            /\  \E preferenceIndex \in DOMAIN private[n].preferences:
                    /\  private[n].preferences[preferenceIndex].package = j.package
                    /\  private' = [private EXCEPT ![n].preferences[preferenceIndex].status = "processed"]
            /\ UNCHANGED  <<packages>>
    \* \/  /\  \E n \in Nodes: 
    \*             Cardinality({p \in Range(private[n].preferences): p.status = "not-processed"}) = 0
    \*     /\  LET 
    \*             concat(a, b) == a \o ", " \o b
    \*             wallets == {ToString(public.nodes[n].wallet): n \in Nodes}
    \*         IN  PrintT(SetReduce(concat, wallets, ""))
    \*     /\ UNCHANGED <<public, private, packages>>
    \/  /\  AllButOnePackagedIsJudgedPerNode
        \* /\  LET 
        \*         concat(a, b) == a \o ", " \o b
        \*         wallets == {ToString(public.nodes[n].wallet): n \in Nodes}
        \*     IN  PrintT(SetReduce(concat, wallets, ""))
        /\ UNCHANGED <<public, private, packages>>


Spec == Init /\ [][Next]_<<public, private, packages>> /\ Fairness


====