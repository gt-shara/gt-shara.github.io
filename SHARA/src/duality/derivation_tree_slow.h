
#include <stdio.h>
#include "duality.h"
#include "duality_profiling.h"
#include <set>
#include <map>
#include <list>
#include <iterator>
#include <sstream>
#include <queue>
namespace Duality{
    class Reporter {
    protected:
        RPFP *rpfp;
    public:
        Reporter(RPFP *_rpfp){
            rpfp = _rpfp;
        }
        virtual void Extend(RPFP::Node *node){}
        virtual void Update(RPFP::Node *node, const RPFP::Transformer &update, bool eager){}
        virtual void Bound(RPFP::Node *node){}
        virtual void Expand(RPFP::Edge *edge){}
        virtual void AddCover(RPFP::Node *covered, std::vector<RPFP::Node *> &covering){}
        virtual void RemoveCover(RPFP::Node *covered, RPFP::Node *covering){}
        virtual void Conjecture(RPFP::Node *node, const RPFP::Transformer &t){}
        virtual void Forcing(RPFP::Node *covered, RPFP::Node *covering){}
        virtual void Dominates(RPFP::Node *node, RPFP::Node *other){}
        virtual void InductionFailure(RPFP::Edge *edge, const std::vector<RPFP::Node *> &children){}
        virtual void UpdateUnderapprox(RPFP::Node *node, const RPFP::Transformer &update){}
        virtual void Reject(RPFP::Edge *edge, const std::vector<RPFP::Node *> &Children){}
        virtual void Message(const std::string &msg){}
        virtual void Depth(int){}
        virtual ~Reporter(){}
    };
    struct Candidate {
        RPFP::Edge *edge;
        std::vector<RPFP::Node *> Children;
        int parentLevel;
        bool operator<(const Duality::Candidate& rhs) const{
            int l_level=this->parentLevel;
            int r_level=rhs.parentLevel;
            if(l_level<r_level){
                return false;
            }
            if(l_level>r_level){
                return true;
            }
            else{
                int l_TopoSortValue=this->edge->Parent->TopoSort;
                int r_TopoSortValue=rhs.edge->Parent->TopoSort;
                if(l_TopoSortValue<r_TopoSortValue){
                    return false;
                }
                else{
                    return true;
                }
            }
        }
    };
    
    struct colorNode {
        int nodeIndex;
        int nodeSort;
        std::set<colorNode*> edges;
        int color;
        RPFP::Edge *edge;
        int position;
    };
    
    class Duality : public Solver {
        
    public:
        Duality(RPFP *_rpfp);
        
        
        ~Duality();
        
        RPFP_caching *clone_rpfp;
        RPFP_caching *gen_cands_rpfp;
        
        
        typedef RPFP::Node Node;
        typedef RPFP::Edge Edge;
        
        /** This struct represents a candidate for extending the
         unwinding. It consists of an edge to instantiate
         and a vector of children for the new instance. */
        
        /** comparsion between Candidate to use priorityQuee candidates **/
        /** Comparison operator, allowing us to sort Nodes
         by their number field. */
        
        struct lnode
        {
            bool operator()(const Node* s1, const Node* s2) const
            {
                return s1->number < s2->number;
            }
        };
        
        typedef std::set<Node *, lnode> Unexpanded;  // sorted set of Nodes
        
        /** This class provides a heuristic for expanding a derivation
         tree. */
        
        class Heuristic {
            RPFP *rpfp;
            
            /** Heuristic score for unwinding nodes. Currently this
             counts the number of updates. */
            struct score {
                int updates;
                score() : updates(0) {}
            };
            hash_map<RPFP::Node *,score> scores;
            
        public:
            Heuristic(RPFP *_rpfp);
            
            virtual ~Heuristic();
            
            virtual void Update(RPFP::Node *node);
            
            /** Heuristic choice of nodes to expand. Takes a set "choices"
             and returns a subset "best". We currently choose the
             nodes with the fewest updates.
             */
#if 0
            virtual void ChooseExpand(const std::set<RPFP::Node *> &choices, std::set<RPFP::Node *> &best);
#else
            virtual void ChooseExpand(const std::set<RPFP::Node *> &choices, std::set<RPFP::Node *> &best, bool high_priority=false, bool best_only=false);
#endif
            
            /** Called when done expanding a tree */
            virtual void Done();
            
            /** Ask whether a node should be used/unused in the tree. Returns,
             1 if yes, -1 if no, and 0 if don't care. */
            
            virtual int UseNode(Node *node);
        };
        
        /** The Proposer class proposes conjectures eagerly. These can come
         from any source, including predicate abstraction, templates, or
         previous solver runs. The proposed conjectures are checked
         with low effort when the unwinding is expanded.
         */
        
        class Proposer {
        public:
            /** Given a node in the unwinding, propose some conjectures */
            virtual std::vector<RPFP::Transformer> &Propose(Node *node) = 0;
            virtual ~Proposer(){};
        };
        
        
        class Covering; // see below
        
        // These members represent the state of the algorithm.
        
        RPFP *rpfp;                          // the input RPFP
        Reporter *reporter;                  // object for logging
        Reporter *conj_reporter;             // object for logging conjectures
        Heuristic *heuristic;                // expansion heuristic
        context &ctx;                        // Z3 context
        solver &slvr;                        // Z3 solver
        std::vector<RPFP::Node *> &nodes;    // Nodes of input RPFP
        std::vector<RPFP::Node *> originalNodes;
        std::vector<RPFP::Node *> allCHCnodes;
        std::vector<RPFP::Edge *> &edges;    // Edges of input RPFP
        std::vector<RPFP::Edge *> specialedges;
        std::set<RPFP::Edge *> backedges;
        std::vector<RPFP::Edge *> originalEdges;
        std::vector<RPFP::Edge *> allCHCedges;
        std::vector<RPFP::Edge *> CheckEdges;
        std::vector<RPFP::Node *> leaves;    // leaf nodes of unwinding (unused)
        Unexpanded unexpanded;               // unexpanded nodes
        std::priority_queue<Candidate,std::vector<Candidate> > candidates;     // candidates for expansion
        // maps children to edges in input RPFP
        hash_map<Node *, std::vector<Edge *> > edges_by_child;
        // maps parents to edges in input RPFP
        hash_map<Node *, std::vector<Edge *> > edges_by_parent;
        // maps each node in input RPFP to its expanded instances
        hash_map<Node *, std::vector<Node *> > insts_of_node;
        // maps each node in input RPFP to all its instances
        hash_map<Node *, std::vector<Node *> > all_of_node;
        RPFP *unwinding;                     // the unwinding
        Covering *indset;                    // proposed inductive subset
        Counterexample cex;                  // counterexample
        std::list<Node *> to_expand;
        hash_set<Node *> updated_nodes;
        hash_map<Node *, Node *> underapprox_map; // maps underapprox nodes to the nodes they approximate
        int last_decisions;
        hash_set<Node *> overapproxes;
        std::vector<Proposer *> proposers;
        std::string ConjectureFile;
        bool stratified_inlining_done;
        bool getNewSolution;
        int loopCount;
        
#ifdef BOUNDED
        struct Counter {
            unsigned val;
            Counter(){val = 0;}
        };
        typedef std::map<Node *,Counter> NodeToCounter;
        hash_map<Node *,NodeToCounter> back_edges; // counts of back edges
#endif
        
        /** Solve the problem. */
        virtual bool Solve();
        
        void PreSolve();
        
        void PostSolve();
        
        void collectNode(Node *n,std::set<Node *> &allNodes);
        
        bool RecheckBounds();
        
        void CreateInitialUnwinding();
        
        void Cancel();
        
#if 0
        virtual void Restart(RPFP *_rpfp);
#endif
        
        virtual void LearnFrom(Solver *other_solver);
        
        /** Return a reference to the counterexample */
        virtual Counterexample &GetCounterexample();
        
        // options
        bool FullExpand;    // do not use partial expansion of derivation tree
        bool NoConj;        // do not use conjectures (no forced covering)
        bool FeasibleEdges; // use only feasible edges in unwinding
        bool UseUnderapprox; // use underapproximations
        bool Report;         // spew on stdout
        bool StratifiedInlining; // Do stratified inlining as preprocessing step
        int RecursionBound;  // Recursion bound for bounded verification
        bool BatchExpand;
        bool EnableRestarts;
        
        bool SetBoolOption(bool &opt, const std::string &value);
        
        bool SetIntOption(int &opt, const std::string &value);
        
        virtual bool ifAllAssertionHold();
        
        virtual void addAllBackEdge();
        
        /** Set options (not currently used) */
        virtual bool SetOption(const std::string &option, const std::string &value);
        
        /** Create an instance of a node in the unwinding. Set its
         annotation to true, and mark it unexpanded. */
        Node* CreateNodeInstance(Node *node, int number = 0,bool ifAdd=false);
        
        /** Create an instance of an edge in the unwinding, with given
         parent and children. */
        void CreateEdgeInstance(Edge *edge, Node *parent, const std::vector<Node *> &children,bool ifAdd=false);
        
        void MakeLeaf(Node *node, bool do_not_expand = false);
        
        void MakeOverapprox(Node *node);
        
        /** We start the unwinding with leaves that under-approximate
         each relation with false. */
        void CreateLeaves();
        
        /** Create the map from children to edges in the input RPFP.  This
         is used to generate candidates for expansion. */
        void CreateEdgesByChildMap();
        
        void NullaryCandidates();
        
        void InstantiateAllEdges();
        
        bool ProducedBySI(Edge *edge, std::vector<Node *> &children);
        
        /** Add a candidate for expansion, but not if Stratified inlining has already
         produced it */
        
        void AddCandidate(Edge *edge, std::vector<Node *> &children);

        // wrharris: wrapper that adds edges to queries last
        void AddCandidate2(Candidate);

        void AddCandidate3(Candidate c);
        
        /** Generate candidates for expansion, given a vector of candidate
         sets for each argument position.  This recursively produces
         the cross product.
         */
        void GenCandidatesRec(int pos, Edge *edge,
                              const std::vector<std::vector<Node *> > &vec,
                              std::vector<Node *> &children);
        
        /** Setup for above recursion. */
        void GenCandidates(int pos, Edge *edge,
                           const std::vector<std::vector<Node *> > &vec);
        
        /** Expand a node. We find all the candidates for expansion using
         this node and other already expanded nodes. This is a little
         tricky, since a node may be used for multiple argument
         positions of an edge, and we don't want to produce duplicates.
         */
        
#ifndef NEW_EXPAND
        void ExpandNode(Node *node);
#else
        /** If the current proposed solution is not inductive,
         use the induction failure to generate candidates for extension. */
        void ExpandNode(Node *node);
#endif
        
        void ExpandNodeFromOther(Node *node, Node *other);
        
        /** Expand a node based on some uncovered node it dominates.
         This pushes cahdidates onto the *front* of the candidate
         queue, so these expansions are done depth-first. */
        bool ExpandNodeFromCoverFail(Node *node);
        
        
        /** Make a boolean variable to act as a "marker" for a node. */
        expr NodeMarker(Node *node);
        
        /** Make a boolean variable to act as a "marker" for a pair of nodes. */
        expr NodeMarker(Node *node1, Node *node2);
        
        /** Union the annotation of dst into src. If with_markers is
         true, we conjoin the annotation formula of dst with its
         marker. This allows us to discover which disjunct is
         true in a satisfying assignment. */
        void UnionAnnotations(RPFP::Transformer &dst, Node *src, bool with_markers = false);
        
        void GenNodeSolutionFromIndSet(Node *node, RPFP::Transformer &annot, bool with_markers = false);
        
        bool NodeSolutionFromIndSetFull(Node *node);
        
        bool recursionBounded;
        
        /** See if the solution might be bounded. */
        void TestRecursionBounded();
        
        bool IsResultRecursionBounded();
        
        /** Generate a proposed solution of the input RPFP from
         the unwinding, by unioning the instances of each node. */
        void GenSolutionFromIndSet(bool with_markers = false);
        
        bool NodePastRecursionBound(Node *node, bool report = false);
        
        /** Test whether a given extension candidate actually represents
         an induction failure. Right now we approximate this: if
         the resulting node in the unwinding could be labeled false,
         it clearly is not an induction failure. */
        
        bool CandidateFeasible(const Candidate &cand);
        
        
        hash_map<Node *, int> TopoSort;
        int TopoSortCounter;
        std::vector<Edge *> SortedEdges;
        
        void DoTopoSortRec(Node *node);
        
        void DoTopoSort();
        
        
        int StratifiedLeafCount;
        

        
        /** Stratified inlining builds an initial layered unwinding before
         switching to the LAWI strategy. Currently the number of layers
         is one. Only nodes that are the targets of back edges are
         consider to be leaves. This assumes we have already computed a
         topological sort.
         */
        
        bool DoStratifiedInlining();
        
        Node *CreateLeaf(Node *node);
        
        void MarkExpanded(Node *node);
        

        
        /** In stratified inlining, we build the unwinding from the bottom
         down, trying to satisfy the node bounds. We do this as a pre-pass,
         limiting the expansion. If we get a counterexample, we are done,
         else we continue as usual expanding the unwinding upward.
         */
        
        

        
        /** Here, we do the downward expansion for stratified inlining */
        
        hash_map<Node *, Node *> LeafMap, StratifiedLeafMap;
        
        Edge *GetNodeOutgoing(Node *node, int last_decs = 0);
        
        void SetHeuristicOldNode(Node *node);
        
        bool SolveMain();
        
        /** This does the actual solving work. We try to generate
         candidates for extension. If we succed, we extend the
         unwinding. If we fail, we have a solution. */
        bool SolveMainInt();
        
        // hack: put something local into the underapproximation formula
        // without this, interpolants can be pretty bad
        void AddThing(expr &conj);
        
        Node *CreateUnderapproxNode(Node *node);
        
        /** Try to prove a conjecture about a node. If successful
         update the unwinding annotation appropriately. */
        bool ProveConjecture(Node *node, const RPFP::Transformer &t,Node *other = 0, Counterexample *_cex = 0);
        
        /** If a node is part of the inductive subset, expand it.
         We ask the inductive subset to exclude the node if possible.
         */
        void TryExpandNode(RPFP::Node *node);
        
        /** Make the conjunction of markers for all (expanded) instances of
         a node in the input RPFP. */
        expr AllNodeMarkers(Node *node);
        
        void RuleOutNodesPastBound(Node *node, RPFP::Transformer &t);
        
        
        void GenNodeSolutionWithMarkersAux(Node *node, RPFP::Transformer &annot, expr &marker_disjunction, Node *other_node);
        
        bool GenNodeSolutionWithMarkers(Node *node, RPFP::Transformer &annot, bool expanded_only = false, Node *other_node = 0);
        
        /** Make a checker to determine if an edge in the input RPFP
         is satisfied. */
        Node *CheckerJustForEdge(Edge *edge, RPFP *checker, bool expanded_only = false);
        
#ifndef MINIMIZE_CANDIDATES_HARDER
        
#if 0
        /** Make a checker to detheermine if an edge in the input RPFP
         is satisfied. */
        Node *CheckerForEdge(Edge *edge, RPFP *checker);
        
#else
        /** Make a checker to determine if an edge in the input RPFP
         is satisfied. */
        Node *CheckerForEdge(Edge *edge, RPFP *checker);
#endif
        
        /** If an edge is not satisfied, produce an extension candidate
         using instances of its children that violate the parent annotation.
         We find these using the marker predicates. */
        void ExtractCandidateFromCex(Edge *edge, RPFP *checker, Node *root, Candidate &candidate);
#else
        
        
        /** Make a checker to determine if an edge in the input RPFP
         is satisfied. */
        Node *CheckerForEdge(Edge *edge, RPFP *checker);
        
        /** If an edge is not satisfied, produce an extension candidate
         using instances of its children that violate the parent annotation.
         We find these using the marker predicates. */
        void ExtractCandidateFromCex(Edge *edge, RPFP *checker, Node *root, Candidate &candidate);
        
#endif
        
        
        Node *CheckerForEdgeClone(Edge *edge, RPFP_caching *checker);
        
        /** If the current proposed solution is not inductive,
         use the induction failure to generate candidates for extension. */
        void GenCandidatesFromInductionFailure(bool full_scan = false);
        
#ifdef CANDS_FROM_UPDATES
        /** If the given edge is not inductive in the current proposed solution,
         use the induction failure to generate candidates for extension. */
        void GenCandidatesFromEdgeInductionFailure(RPFP::Edge *edge);
#endif
        
        /** Find the unexpanded nodes in the inductive subset. */
        void FindNodesToExpand();
        
        /** Try to create some extension candidates from the unexpanded
         nodes. */
        void ProduceSomeCandidates();
        
        std::list<Candidate> postponed_candidates;
        
        /** Try to produce some extension candidates, first from unexpanded
         nodes, and if this fails, from induction failure. */
        void ProduceCandidatesForExtension();
        
        bool Update(Node *node, const RPFP::Transformer &fact, bool eager=false);
        
        bool UpdateNodeToNode(Node *node, Node *top);
        
        /** Update the unwinding solution, using an interpolant for the
         derivation tree. */
        void UpdateWithInterpolant(Node *node, RPFP *tree, Node *top);
        
        /** Update unwinding lower bounds, using a counterexample. */
        
        void UpdateWithCounterexample(Node *node, RPFP *tree, Node *top);
        
        /** Try to update the unwinding to satisfy the upper bound of a
         node. */
        bool SatisfyUpperBound(Node *node);
        
        /* For a given nod in the unwinding, get conjectures from the
         proposers and check them locally. Update the node with any true
         conjectures.
         */
        
        void DoEagerDeduction(Node *node);
        
        
        check_result CheckEdge(RPFP *checker, Edge *edge);
        
        check_result CheckEdgeCaching(Edge *unwinding_edge, const RPFP::Transformer &bound);
        
        
        /* If the counterexample derivation is partial due to
         use of underapproximations, complete it. */
        
        void BuildFullCex(Node *node);
        
        void UpdateBackEdges(Node *node);
        
        /** Extend the unwinding, keeping it solved. */
        bool Extend(Candidate &cand, Node *&node);

        // Extend, mering heads of edges
        std::set<Node*> collectDependencies(std::set<Node*>);
        std::set<Node*> collectDependents(std::set<Node*>);

        bool ExtendMerge(Candidate &cand, Node *&node);
        
        void ExpandUnderapproxNodes(RPFP *tree, Node *root);
        
        // Propagate conjuncts up the unwinding
        void Propagate();
        
        
        /** This class represents a derivation tree. */
        class DerivationTree {
        public:
            
            virtual ~DerivationTree();
            
            DerivationTree(Duality *_duality, RPFP *rpfp, Reporter *_reporter, Heuristic *_heuristic, bool _full_expand);
            
            
            Duality *duality;
            Reporter *reporter;
            Heuristic *heuristic;
            solver &slvr;
            context &ctx;
            RPFP *tree;
            RPFP::Node *top;
            std::list<RPFP::Node *> leaves;
            bool full_expand;
            bool underapprox;
            bool constrained;
            bool false_approx;
            std::vector<Node *> underapprox_core;
            int start_decs, last_decs;
            
            /* We build derivation trees in one of three modes:
             
             1) In normal mode, we build the full tree without considering
             underapproximations.
             
             2) In underapprox mode, we use underapproximations to cut off
             the tree construction. THis means the resulting tree may not
             be complete.
             
             3) In constrained mode, we build the full tree but use
             underapproximations as upper bounds. This mode is used to
             complete the partial derivation constructed in underapprox
             mode.
             */
            
            virtual bool Derive(RPFP *rpfp, RPFP::Node *root, bool _underapprox, bool _constrained = false, RPFP *_tree = 0);
            
#define WITH_CHILDREN
            
            void InitializeApproximatedInstance(RPFP::Node *to);
            
            Node *CreateApproximatedInstance(RPFP::Node *from);
            
            bool CheckWithUnderapprox();
            
            virtual bool Build();
            
            virtual void ExpandNode(RPFP::Node *p);
            
#define      UNDERAPPROXCORE
#ifndef UNDERAPPROXCORE
            void ExpansionChoices(std::set<Node *> &best);
#else
#if 0
            
            void ExpansionChoices(std::set<Node *> &best);
#else
            void ExpansionChoicesFull(std::set<Node *> &best, bool high_priority, bool best_only = false);
            
            void ExpansionChoicesRec(std::vector <Node *> &unused_set, std::vector <Node *> &used_set,
                                     std::set<Node *> &choices, int from, int to);
            
            std::set<Node *> old_choices;
            
            void ExpansionChoices(std::set<Node *> &best, bool high_priority, bool best_only = false);
#endif
#endif
            
            bool ExpandSomeNodes(bool high_priority = false, int max = INT_MAX);
            
            void RemoveExpansion(RPFP::Node *p);
            
            // remove all the descendants of tree root (but not root itself)
            void RemoveTree(RPFP *tree, RPFP::Node *root);
        };
        
        class DerivationTreeSlow : public DerivationTree {
        public:
            
            struct stack_entry {
                unsigned level; // SMT solver stack level
                std::vector<Node *> expansions;
            };
            
            std::vector<stack_entry> stack;
            
            hash_map<Node *, expr> updates;
            
            int restart_interval;
            
            DerivationTreeSlow(Duality *_duality, RPFP *rpfp, Reporter *_reporter, Heuristic *_heuristic, bool _full_expand);
            
            struct DoRestart {};
            
            virtual bool Build();
            
            
            // When we check, try to use the same children that were used in the
            // previous counterexample.
            check_result Check();
            
            bool BuildMain();
            
            std::vector<Node *> node_order;
            
            void Reduce();
            
            void PopLevel();
            
            bool NodeTooComplicated(Node *node);
            
            void SimplifyNode(Node *node);
            
            bool LevelUsedInProof(unsigned level);
            
            void RemoveUpdateNodesAtCurrentLevel() ;
            
            void RemoveLeaves(hash_set<Node *> &leaves_to_remove);
            
            hash_map<Node *, std::vector<Node *> > node_map;
            std::list<Node *> updated_nodes;
            
            virtual void ExpandNode(RPFP::Node *p);
            
            bool RecordUpdate(Node *node);
            
            void HandleUpdatedNodes();
            
            bool AtCurrentStackLevel(Node *node);
            
            void UnmapNode(Node *node);
            
            void Generalize(Node *node);
            
            bool Propagate(Node *node);
            
        };
        // wrharris: shara additions
        /* DerivationDAGShara: overrides Build method to implement the
         shara solving algorithm. */
        class DerivationDAGShara : public DerivationTreeSlow {
            
        static   bool dep_cmp(Node* lhs, Node* rhs);
        static   bool colorNode_cmp(colorNode* ln, colorNode* rn);
        static   bool dep_cmp2(Node* lhs, Node* rhs);
        public:
            DerivationDAGShara(Duality *_duality, RPFP *rpfp, Reporter *_reporter, Heuristic *_heuristic, bool _full_expand);
            
            virtual bool Derive(RPFP *rpfp, RPFP::Node *root, bool _underapprox, bool _constrained = false, RPFP *_tree = 0);
            
            virtual bool Build();
            
            virtual Node* CopyRec(Node *root,std::set<Node *> &visited);
            
            virtual void  Copy();
            
            Node *virtualTop;
            
            std::map<Node *,Node *> CopyToOriginal;
            
            std::map<Node *,Node *> OriginalToCopy;
            
            std::map<Node *,expr> currentInterpolants;
            
            std::map<Node *,std::set<Node *> > underDependencies;
            
            std::map<Node *,std::set<Node *> > siblings;
            
            std::map<Node *,expr> NodesToBoolean;
            
            std::set<Node *> SmartcollectConjunctionNodes(Node * root);
            
            void  splitNode(Node * root);
            
            void buildCDD2();
            
        private:
            std::vector<Node*> sort_nodes();
            
            Node* copy_top;
            
            void buildCDDRec(Node *n,std::set<Node *>);
            
            void buildCDD();
            
            bool solveCDD();
            
            void restore();
            
            virtual std::set<int> getPossibleColorSet();
            
            void getColorResultRec(std::vector<colorNode*> & graph, int currentNode);
            
            std::set<Node *> buildVisitedNodes;
            
            std::set<Node *> originalNodes;
            
            std::set<Node *> CopyNodes;
            
            std::set<Node *> collectConjunctionNodes(Node * root);
            
            std::set<Node *> collectConjunctionSiblingsRec(Node * root);
            
            std::set<Node *> specialCollectDependencies(std::set<Node *> roots);
            
            std::set<Node *> specialCollectDependencies2(Node * root);
            
            std::set<Node *> collectDependenciesAndSiblings(Node* n,std::set<Node *> &siblings);
            
            std::set<Node *> collectAllContextNodes(Node* n);
            
            TermTree* buildPreFormula(Node* n);
            
            TermTree* buildContextFormula(Node* n);
            
            int colorCount;
        };
        
        class Covering {
            
            struct cover_info {
                Node *covered_by;
                std::list<Node *> covers;
                bool dominated;
                std::set<Node *> dominates;
                cover_info(){
                    covered_by = 0;
                    dominated = false;
                }
            };
            
            typedef hash_map<Node *,cover_info> cover_map;
            cover_map cm;
            Duality *parent;
            bool some_updates;
            
#define NO_CONJ_ON_SIMPLE_LOOPS
#ifdef NO_CONJ_ON_SIMPLE_LOOPS
            hash_set<Node *> simple_loops;
#endif
            
            Node *&covered_by(Node *node);
            
            std::list<Node *> &covers(Node *node);
            
            std::vector<Node *> &insts_of_node(Node *node);
            
            Reporter *reporter();
            
            std::set<Node *> &dominates(Node *x);
            
            bool dominates(Node *x, Node *y);
            
            bool &dominated(Node *x);
            
        public:
            
            Covering(Duality *_parent);
            
            bool IsCoveredRec(hash_set<Node *> &memo, Node *node);
            
            bool IsCovered(Node *node);
            
#ifndef UNDERAPPROX_NODES
            void RemoveCoveringsBy(Node *node);
#else
            void RemoveCoveringsBy(Node *node);
#endif
            
            void RemoveAscendantCoveringsRec(hash_set<Node *> &memo, Node *node);
            
            void RemoveAscendantCoverings(Node *node);
            
            bool CoverOrder(Node *covering, Node *covered);
            
            bool CheckCover(Node *covered, Node *covering);
            
            bool CoverByNode(Node *covered, Node *covering);
            
            bool CoverByAll(Node *covered);
            
            bool Close(Node *node);
            
            bool CloseDescendantsRec(hash_set<Node *> &memo, Node *node);
            
            bool CloseDescendants(Node *node);
            
            bool Contains(Node *node);
            
            bool Candidate(Node *node);
            
            void SetDominated(Node *node);
            
            bool CouldCover(Node *covered, Node *covering);
            
            bool ContainsCex(Node *node, Counterexample &cex);
            
            /** We conjecture that the annotations of similar nodes may be
             true of this one. We start with later nodes, on the
             principle that their annotations are likely weaker. We save
             a counterexample -- if annotations of other nodes are true
             in this counterexample, we don't need to check them.
             */
            
#ifndef UNDERAPPROX_NODES
            bool Conjecture(Node *node);
#else
            bool Conjecture(Node *node);
#endif
            
            void Update(Node *node, const RPFP::Transformer &update);
            
#ifndef UNDERAPPROX_NODES
            Node *GetSimilarNode(Node *node);
#else
            Node *GetSimilarNode(Node *node);
#endif
            
            bool Dominates(Node * node, Node *other);
            
            void Add(Node *node);
            
        };

        /* This expansion heuristic makes use of a previuosly obtained
         counterexample as a guide. This is for use in abstraction
         refinement schemes.*/
        
        class ReplayHeuristic : public Heuristic {
            
            Counterexample old_cex;
        public:
            ReplayHeuristic(RPFP *_rpfp, Counterexample &_old_cex);
            
            ~ReplayHeuristic();
            // Maps nodes of derivation tree into old cex
            hash_map<Node *, Node*> cex_map;
            
            void Done();
            
            void ShowNodeAndChildren(Node *n);
            
            // HACK: When matching relation names, we drop suffixes used to
            // make the names unique between runs. For compatibility
            // with boggie, we drop suffixes beginning with @@
            std::string BaseName(const std::string &name);
            
            Node *MatchNode(Node *node);
            
            int UseNode(Node *node);
            
            virtual void ChooseExpand(const std::set<RPFP::Node *> &choices, std::set<RPFP::Node *> &best, bool high_priority, bool best_only);
        };
        
        
        class LocalHeuristic : public Heuristic {
            
            RPFP::Node *old_node;
        public:
            LocalHeuristic(RPFP *_rpfp);
            void SetOldNode(RPFP::Node *_old_node);
            
            // Maps nodes of derivation tree into old subtree
            hash_map<Node *, Node*> cex_map;
            
            virtual void ChooseExpand(const std::set<RPFP::Node *> &choices, std::set<RPFP::Node *> &best);
        };
        
        /** This proposer class generates conjectures based on the
         unwinding generated by a previous solver. The assumption is
         that the provious solver was working on a different
         abstraction of the same system. The trick is to adapt the
         annotations in the old unwinding to the new predicates.  We
         start by generating a map from predicates and parameters in
         the old problem to the new.
         
         HACK: mapping is done by cheesy name comparison.
         */
        
        class HistoryProposer : public Proposer
        {
            Duality *old_solver;
            Duality *new_solver;
            hash_map<Node *, std::vector<RPFP::Transformer> > conjectures;
            
        public:
            /** Construct a history solver. */
            HistoryProposer(Duality *_old_solver, Duality *_new_solver);
            
            virtual std::vector<RPFP::Transformer> &Propose(Node *node);
            
            virtual ~HistoryProposer();
            
        private:
            void MatchNodes(Node *new_node, Node *old_node, hash_map<func_decl,func_decl> &bckg_map);
            
            // We match names by removing suffixes beginning with double at sign
            
            std::string GetKey(Node *node);
            
            std::string GetKey(const expr &var);
            
            std::string GetKey(const func_decl &f);
        };
    };

	
}
