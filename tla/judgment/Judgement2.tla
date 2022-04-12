---- MODULE Judgement2 ----
EXTENDS TLC, FiniteSets, Integers, Sequences
VARIABLES 
    nextJudgmentId,
    judgments,
    privateStorage,
    packages,
    votes

Organizations == {"org1", "org2", "org3"}


Peers == {"peer1", "peer2", "peer3"}
Clients == {"client1", "client2", "client3"}

orgOf == [
    client1 |-> "org1",
    peer1 |-> "org1",
    client2 |-> "org2",
    peer2 |-> "org2",
    client3 |-> "org3",
    peer3 |-> "org3"
]

clientOf == [
    org1 |-> "client1",
    org2 |-> "client2",
    org3 |-> "client3"
]

peerOf == [
    org1 |-> "peer1",
    org2 |-> "peer2",
    org3 |-> "peer3"

]

Packages == {"p1", "p2", "p3"}
Wallet == [b \in Organizations |-> 0]
\* Prefered == [o \in Organizations |-> Subset(Packages)]

\* Subset(set) == ??

Safety == nextJudgmentId >= 0

Range(f) == {f[k]: k \in DOMAIN f}

\* Chaincode:

\* Begin the judgement of a package
Begin(client, package) == 
    \* /\ PrintT("Begin!")
    /\ judgments' = Append(judgments, [
        requester |-> client, 
        package |-> package,
        status |-> "initialized"])

Build(client, package) ==
    \* /\ PrintT("Build!")
    /\  privateStorage' = [privateStorage EXCEPT ![client] = @ \union {package}]
    /\  votes' = [votes EXCEPT ![package] = @ \union {client}]

Init == /\ nextJudgmentId = 0 
        /\ judgments = <<>> 
        /\ privateStorage = [c \in Clients |-> {}]
        /\ votes = [p \in Packages |-> {}]
        /\ packages = Packages

Next == 
    /\  \/  /\ \E c \in Clients:
                \E j \in Range(judgments): 
                    /\ j.package \notin privateStorage[c] 
                    /\ Build(c, j.package)
            /\ UNCHANGED <<judgments, nextJudgmentId, packages>>
            /\ Cardinality(Range(judgments)) > 0
                
        \/  /\ \E c \in Clients:
                \E p \in Packages:
                    /\ \A j \in Range(judgments): j.package # p
                    /\ Begin(c, p)
                    /\ packages' = packages \ {p}
            /\ nextJudgmentId' = nextJudgmentId + 1
            /\ UNCHANGED privateStorage

        \* \/ \E p \in DOMAIN votes:
        \*         IF votes[p] = 3 THEN 
        \*             judgments' = 
            
    \* /\ PrintT(judgments)
    \* /\ PrintT(privateStorage)

Spec == Init /\ [][Next]_<<nextJudgmentId, judgments, privateStorage, packages>> 

====
