----------------------------- MODULE Consensus -----------------------------
EXTENDS Integers

CONSTANTS PCS  \* The set of all processes

VARIABLES   states,     \* states of each process in PCS
            proposals,  \* proposals of each process in PCS
            pset,       \* set of all proposals 
            decisions   \* decision of each process in PCS
            
typeOK == /\ states \in [PCS -> {"working", "proposed", "decided"}]
          /\ proposals \in [PCS -> {0, 1}]
          /\ pset \subseteq {0, 1}
          /\ decisions \in [PCS -> {-1, 0, 1}]

init == /\ states = [p \in PCS |-> "working"]
        /\ proposals \in [PCS -> {0, 1}]
        /\ pset = {}
        /\ decisions = [p \in PCS |-> -1]
        
propose(p) == /\ states[p] = "working"
              /\ states' = [states EXCEPT ![p] = "proposed"]
              /\ pset' = pset \cup {proposals[p]}
              /\ UNCHANGED <<proposals, decisions>>
              
decide(p) == /\ ~ \E q \in PCS : states[q] = "working"
             /\ states[p] = "proposed"
             /\ states' = [states EXCEPT ![p] = "decided"]
             /\ decisions[p] = -1
             /\ decisions' = [decisions EXCEPT ![p] = CHOOSE x \in pset : TRUE]
             /\ UNCHANGED <<proposals, pset>>

next == \E p \in PCS : propose(p) \/ decide(p)

-------------------------------------------------------------------------------

validity == \E v \in {0, 1} : (\A p \in PCS : proposals[p] = v) 
                => \A q \in PCS : (states[q] = "decided" 
                    => decisions[q] = v)

agreement == \A p1, p2 \in PCS : ~ /\ decisions[p1] = 0
                                   /\ decisions[p2] = 1
                                  
integrity == \A p \in PCS : 
                (states[p] = "decided" 
                => \E r \in PCS : proposals[r] = decisions[p])

specOK == /\ validity
          /\ agreement
          /\ integrity

=============================================================================
\* Modification History
\* Last modified Sun Jan 21 04:06:32 JST 2018 by Zhang
\* Created Thu Jan 18 15:52:38 SRET 2018 by Zhang
