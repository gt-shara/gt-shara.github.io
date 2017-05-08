/* shara.cpp: experiemental alternate implementation of a solver for
   recursion-free CHC systems.

   authors:

   Bill Harris <wharris@cc.gatech.edu>
   Qi Zhou <qizhou@gatech.edu>
*/

#include "derivation_tree_slow.h"
#include <sstream>
#include <string>
#include <stdio.h>
namespace Duality {
  typedef Duality::Node Node;
  typedef Duality::Edge Edge;
    
    void collectAllEdge(Node* root, std::set<Node *> & visited){
        std::vector<Edge *> outgoings=root->Outgoing;
        visited.insert(root);
        for(std::vector<Edge *>::iterator it=outgoings.begin();it!=outgoings.end();it++){
            Edge *theEdge=*it;
            std::vector<Node *> children=theEdge->Children;
            for(std::vector<Node *>::iterator it2=children.begin();it2!=children.end();it2++){
                Node *child=*it2;
                if(visited.find(child) == visited.end()){
                    collectAllEdge(child,visited);
                }
            }
        }
    }
    void prettyPrint(Node* root,std::set<Node *>& visited){
        std::cout<<"===================================\n";
        std::cout<<"one node:"<<root->Name.name()<<"#"<<root->number;
        std::cout<<"\n";
        std::vector<Edge *> outgoings=root->Outgoing;
        std::cout<<"outgoins size:"<<outgoings.size()<<"\n";
        for(std::vector<Edge *>::iterator it=outgoings.begin();it!=outgoings.end();it++){
            Edge *theEdge=*it;
            std::cout<<"--------------------------\n";
            //std::cout<<"Edge: "<<theEdge->F.Formula<<"\n";
            std::cout<<"Edge number:"<<theEdge->number<<"\n";
            std::vector<Node *> children=theEdge->Children;
            std::cout<<"Children:\n";
            for(std::vector<Node *>::iterator it2=children.begin();it2!=children.end();it2++){
                Node *child=*it2;
                std::cout<<child->Name.name()<<"#"<<child->number<<"\n";
            }
            std::cout<<"--------------------------\n";
        }
        std::vector<Edge *> ingoings=root->Incoming;
        std::cout<<"ingoing size:"<<ingoings.size()<<"\n";
        for(std::vector<Edge *>::iterator it=ingoings.begin();it!=ingoings.end();it++){
            Edge *theEdge=*it;
            std::cout<<"--------------------------\n";
            //std::cout<<"Edge: "<<theEdge->F.Formula<<"\n";
            std::cout<<"Edge number:"<<theEdge->number<<"\n";
            Node *parentNode=theEdge->Parent;
            std::cout<<"Points to "<<parentNode->Name.name()<<"#"<<parentNode->number<<"\n";
        }

        visited.insert(root);
        for(std::vector<Edge *>::iterator it=outgoings.begin();it!=outgoings.end();it++){
            Edge *theEdge=*it;
            std::vector<Node *> children=theEdge->Children;
            for(std::vector<Node *>::iterator it2=children.begin();it2!=children.end();it2++){
                Node *child=*it2;
                if(visited.find(child) == visited.end()){
                    prettyPrint(child,visited);
                }
            }
        }
    }

    Duality::DerivationDAGShara::DerivationDAGShara(Duality *_duality, RPFP *rpfp, Reporter *_reporter, Heuristic *_heuristic, bool _full_expand)
    :DerivationTreeSlow(_duality, rpfp, _reporter, _heuristic, _full_expand){
        //std::cout<<"test for shara\n";
    }
    
    bool Duality::DerivationDAGShara::dep_cmp(Node* lhs, Node* rhs) {
        int l_level=lhs->level;
        int r_level=rhs->level;
        if(l_level<r_level){
            return true;
        }
        if(l_level>r_level){
            return false;
        }
        else{
            int l_TopoSortValue=lhs->TopoSort;
            int r_TopoSortValue=rhs->TopoSort;
            if(l_TopoSortValue<r_TopoSortValue){
                return true;
            }
            else{
                return false;
            }
        }
    }
    
    std::set<Node*> collectDependents2(Node * leave) {
        std::set<Node*> deps;
        std::set<Node*> worklist;
        worklist.insert(leave);
        
        // wrharris: lookup names of all std methods
        // replace with: = worklist.is_empty() in loop;
        while (!worklist.empty()) {
            // choose an element, remove it from the worklist, add it to the deps
            Node* dep = * worklist.begin();; // worklist.choose();
            worklist.erase(dep);
            if(deps.find(dep) == deps.end()){
                deps.insert(dep);
            }
            
            // for each edge going into dep,
            for (std::vector<Edge*>::iterator clause_it = dep->Incoming.begin();
                 clause_it != dep->Incoming.end();
                 clause_it++) {
                Edge* clause = *clause_it;
                Node* n = clause->Parent;
                if (deps.find(n) == deps.end()){
                    worklist.insert(n);
                }
            }
        }
        return deps;
    }
    
    bool Duality::DerivationDAGShara::dep_cmp2(Node* lhs, Node* rhs) {
        int l_level=lhs->level;
        int r_level=rhs->level;
        if(l_level<r_level){
            return false;
        }
        if(l_level>r_level){
            return true;
        }
        else{
            int l_TopoSortValue=lhs->TopoSort;
            int r_TopoSortValue=rhs->TopoSort;
            if(l_TopoSortValue<r_TopoSortValue){
                return false;
            }
            else{
                return true;
            }
        }
    }
    
    bool Duality::DerivationDAGShara::colorNode_cmp(colorNode *ln,colorNode *rn){
        if(ln->edges.size() > rn->edges.size()){
            return true;
        }
        return false;
    }
    
    Node* Duality::DerivationDAGShara::CopyRec(Node *root,std::set<Node *> &visited){
        Node* cp_root=this->tree->CloneNode(root);
        this->CopyNodes.insert(cp_root);
        cp_root->Annotation.Formula=this->ctx.bool_val(true);
        cp_root->level=root->level;
        //std::cout<<"copy a new nodes: "<<cp_root->Name.name()<<"#"<<cp_root->number<<"\n";
        CopyToOriginal[cp_root]=root;
        OriginalToCopy[root]=cp_root;
        std::vector<Edge *> OutgoingEdges=root->Outgoing;
        std::vector<Edge *> newOutgoingEdge;
        for(std::vector<Edge *>::iterator it=OutgoingEdges.begin();it!=OutgoingEdges.end();it++){
            Edge* theEdge=*it;
            std::vector<Node *> Children=theEdge->Children;
            std::vector<Node *> newChildren;
            for(std::vector<Node *>::iterator it2=Children.begin();it2!=Children.end();it2++){
                Node* theChild=*it2;
                if(visited.find(theChild) == visited.end()){
                    visited.insert(theChild);
                    Node* cp_theChild=CopyRec(theChild,visited);
                    newChildren.push_back(cp_theChild);
                }
                else{
                    newChildren.push_back(OriginalToCopy[theChild]);
                }
            }
            Edge *cp_theEdge=this->tree->CreateEdge(cp_root,theEdge->F,newChildren);
            newOutgoingEdge.push_back(cp_theEdge);
        }
        cp_root->Outgoing=newOutgoingEdge;
        return cp_root;
    }
    void Duality::DerivationDAGShara::Copy(){
        std::set<Node *> visited;
        visited.insert(top);
        virtualTop=CopyRec(top,visited);
        //std::cout<<"the size of total copy:"<<visited.size()<<"\n";
    }
    std::set<Node *> Duality::DerivationDAGShara::collectConjunctionSiblingsRec(Node * root){
        std::set<Node *> visitedParents;
        std::set<Node *> result;
        for(std::vector<Edge *>::iterator it=root->Incoming.begin();it!=root->Incoming.end();it++){
            Edge *e=*it;
            if(e->Children.size() > 1){
                for(std::vector<Node *>::iterator it2=e->Children.begin();it2!=e->Children.end();it2++){
                    Node* sibling=*it2;
                    if(sibling != root){
                        if(result.find(sibling) == result.end()){
                            result.insert(sibling);
                        }
                    }
                }
            }
            if(visitedParents.find(e->Parent) == visitedParents.end()){
                visitedParents.insert(e->Parent);
                std::set<Node *> conjunctionSiblings=this->collectConjunctionSiblingsRec(e->Parent);
                for(std::set<Node *>::iterator it3=conjunctionSiblings.begin();it3!=conjunctionSiblings.end();it3++){
                    Node *possibleReslut=*it3;
                    if(result.find(possibleReslut) == result.end()){
                        result.insert(possibleReslut);
                    }
                }
            }
        }
        return result;
    
    }
    std::set<Node *> Duality::DerivationDAGShara::collectConjunctionNodes(Node * root){
        std::set<Node *> conjunctionSiblings=this->collectConjunctionSiblingsRec(root);
        return this->tree->collectDependencies(conjunctionSiblings);
    }
    std::set<Node *> Duality::DerivationDAGShara::SmartcollectConjunctionNodes(Node * root){
        //std::cout<<"collect conjunction siblings rec\n";
        std::set<Node *> conjunctionSiblings=this->collectConjunctionSiblingsRec(root);
        //std::cout<<"after collect conjunction siblings rec\n";
        return this->tree->collectDependencies(conjunctionSiblings);
    }
    std::set<int> Duality::DerivationDAGShara::getPossibleColorSet(){
        std::set<int> result;
        for(int i=1;i<= this->colorCount;i++){
            result.insert(i);
        }
        return result;
    }
    void Duality::DerivationDAGShara::getColorResultRec(std::vector<colorNode*> & graph, int currentNode){
        //base case
        //std::cout<<"current node: "<<currentNode<<"\n";
          if(currentNode == 0){
            colorNode *c1=graph.at(currentNode);
            c1->color = 1;
            graph[currentNode] = c1;
        }
       else{
           this->getColorResultRec(graph,currentNode-1);
            colorNode *c1=graph.at(currentNode);
            std::set<colorNode*> edges=c1->edges;
            std::set<int> currentPossibleColor=this->getPossibleColorSet();
           //std::cout<<"number of possible color:"<<currentPossibleColor.size()<<"\n";
           //std::cout<<"edge's size: "<<edges.size()<<"\n";
            for(std::set<colorNode*>::iterator it=edges.begin(); it !=edges.end(); it++){
                colorNode* edgeNode = * it;
                if(edgeNode->nodeSort < currentNode){
                    if(currentPossibleColor.find(edgeNode->color) != currentPossibleColor.end()){
                        currentPossibleColor.erase(edgeNode->color);
                    }
                }
            }
           if(currentPossibleColor.size() == 0){
               this->colorCount=this->colorCount+1;
               c1->color=this->colorCount;
           }
           else{
               //std::cout<<"before this";
              c1->color  = * currentPossibleColor.begin();
               //std::cout<<"after this";
           }
           graph[currentNode] = c1;
        }
        //std::cout<<"finish color\n";
    }
    void  Duality::DerivationDAGShara::splitNode(Node * root){
        this->colorCount = 1;
        std::vector<colorNode *> colorNodes;
        std::map<int, colorNode *> colorNodesMap;
        std::vector<Edge *> theIncomingEdges=root->Incoming;
        //std::cout<<"before here is fine1\n";
        for(unsigned int i=0;i<theIncomingEdges.size();i++){
            Edge *incomingEdge=theIncomingEdges.at(i);
            std::vector<Node *> children=incomingEdge->Children;
            if(children.size()>1){
                //std::cout<<"there are multiple child\n";
            }
            for(unsigned int j=0;j<children.size();j++){
                Node *child=children.at(j);
                if(child == root){
                    colorNode *c = new colorNode();
                    c->color= 0 ;
                    c->edge = incomingEdge;
                    c->position = j;
                    colorNodesMap[i]=c;
                    colorNodes.push_back(c);
                }
            }
        }
        if(colorNodes.size() <= 1){
            return;
        }
        int graphsize=colorNodes.size();
        int **graph = new int*[graphsize];
        for(int i = 0; i <graphsize; ++i) {
            graph[i] = new int[graphsize];
        }
        //std::cout<<"before construct graph\n";
        // construct the graph
        for(unsigned int i=0;i<colorNodes.size();i++){
            for(unsigned int j=i+1;j<colorNodes.size();j++){
                colorNode* nodes1=colorNodes.at(i);
                colorNode* nodes2=colorNodes.at(j);
                //std::cout<<"before access edge\n";
                /* if(keyToEdge.find(nodes1) == keyToEdge.end()){
                    std::cout<<nodes1<<"\n";
                    std::cout<<i<<"\n";
                    std::cout<<"what is inside nodesInColorGrph\n";
                    for(std::string it :nodesInColorGraph){
                        std::cout<<it<<"\n";
                    }
                } */
                Edge* edge1=nodes1->edge;
                Edge* edge2=nodes2->edge;
                //std::cout<<"after access edge\n";
                if(edge1 == edge2){
                    graph[i][j]=1;
                    //std::cout<<"it is one\n";
                }
                else{
                    //std::cout<<"before collect nodes\n";
                    //std::cout<<"before collect nodes2\n";
                    //std::cout<<edge1->Parent->Name.name()<<"\n";
                    //std::cout<<"before collect nodes3\n";
                    std::set<Node *> conjunctionNodes1=this->SmartcollectConjunctionNodes(edge1->Parent);
                    //std::cout<<"after collect nodes1\n";
                    std::set<Node *> conjunctionNodes2=this->SmartcollectConjunctionNodes(edge2->Parent);
                    //std::cout<<"after collect nodes2\n";
                    if( (conjunctionNodes1.find(root) != conjunctionNodes1.end()) || (conjunctionNodes2.find(root) != conjunctionNodes2.end())){
                        graph[i][j]=1;
                    }
                    else{
                        graph[i][j]=0;
                    }
                }
            }
        }
        for(unsigned int i=0;i<colorNodes.size();i++){
            for(unsigned int j=0;j<i;j++){
                graph[i][j]=graph[j][i];
            }
        }
        //std::cout<<"after create color nodes\n";
         for(unsigned int i=0;i<colorNodes.size();i++){
            for(unsigned int j=0;j<colorNodes.size();j++){
                colorNode* c1=colorNodes[i];
                if( (graph[i][j] == 1) &&( i != j)){
                    //std::cout<<"there are edges\n";
                    c1->edges.insert((colorNodes[j]));
                }
            }
        }
        
        //std::cout<<"after add color nodes as edges\n";
       std::sort(colorNodes.begin(), colorNodes.end(), colorNode_cmp);
        for(unsigned int i=0;i<colorNodes.size();i++){
            colorNodes.at(i)->nodeSort = i ;
        }
        //std::cout<<"before get color result\n";
        //std::cout<<"color nodes number: "<<colorNodes.size()<<"\n";
        this->getColorResultRec(colorNodes,colorNodes.size() - 1);
        //std::cout<<"after get color result\n";
        std::map<int, std::vector<colorNode*> > colorToGroups;
        for(unsigned int i=0; i<colorNodes.size(); i++){
            colorNode *c=colorNodes.at(i);
            if(colorToGroups.find(c->color) == colorToGroups.end()){
                std::vector<colorNode*> group;
                group.push_back(c);
                colorToGroups[c->color]=group;
            }
            else{
                std::vector<colorNode*> group = colorToGroups[c->color];
                group.push_back(c);
                colorToGroups[c->color]=group;
            }
        }
        //std::cout<<"here is fine2 \n";
        // To do : base on the color graph result, split nodes
       for(std::map<int, std::vector<colorNode*> >::iterator it2=colorToGroups.begin(); it2 != colorToGroups.end(); it2++){
            int value=it2->first;
            std::vector<colorNode*> group = it2 -> second;
            if (value != 1){
                //std::cout<<"before here is fine2 \n";
                Node *cp_root=this->tree->CloneNode(root);
                this->CopyNodes.insert(cp_root);
                cp_root->Annotation.Formula=this->ctx.bool_val(true);
                cp_root->level=root->level;
                CopyToOriginal[cp_root]=CopyToOriginal[root];
                cp_root->map=root->map;
                std::vector<Edge *> newOutgoingEdge;
                //std::cout<<"after here is fine2 \n";
                for(std::vector<Edge *>::iterator it3=root->Outgoing.begin();it3!=root->Outgoing.end();it3++){
                    Edge *originalEdge =*it3;
                    Edge *newEdge=this->tree->CreateEdge(cp_root,originalEdge->F,originalEdge->Children);
                    newOutgoingEdge.push_back(newEdge);
                }
                //std::cout<<"after here is fine3 \n";
                cp_root->Outgoing=newOutgoingEdge;
                std::vector<Edge *> newIncomingEdges;
                for (std::vector<colorNode*>::iterator it4=group.begin(); it4 != group.end(); it4++){
                    colorNode* c=*it4;
                    if(std::find(newIncomingEdges.begin(), newIncomingEdges.end(), c->edge) == newIncomingEdges.end()){
                        newIncomingEdges.push_back(c->edge);
                    }
                    //std::cout<<"replace the child\n";
                    //std::cout<<c->position<<"\n";
                    c->edge->Children[c->position] = cp_root;
                    if(std::find(c->edge->Children.begin(), c->edge->Children.end(), root) == c->edge->Children.end()){
                        std::vector<Edge *> rootIncoming=root->Incoming;
                        std::vector<Edge *> rootNewIncoming;
                        for(std::vector<Edge *>::iterator oldIncomingIt=rootIncoming.begin();oldIncomingIt!=rootIncoming.end();oldIncomingIt++){
                            Edge *oldIncoming = *oldIncomingIt;
                            if( (oldIncoming != c->edge) && (std::find(rootNewIncoming.begin(), rootNewIncoming.end(), oldIncoming) == rootNewIncoming.end()) ){
                                rootNewIncoming.push_back(oldIncoming);
                            }
                        }
                        root->Incoming=rootNewIncoming;
                    }
                    //std::cout<<"after replace the child\n";
                }
                //std::cout<<"after here is fine4 \n";
                cp_root->Incoming=newIncomingEdges;
            }
        }
        
    }
    void Duality::DerivationDAGShara::buildCDD2(){
        std::set<Node *> root;
        root.insert(this->virtualTop);
        std::set<Node *> allRelatedNode = RPFP::collectDependencies(root);
        std::vector<Edge *> e=this->virtualTop->Outgoing;
        std::vector<Node *> sortedNode;
        for(std::set<Node *>::const_iterator it=allRelatedNode.begin(); it!=allRelatedNode.end();++it){
            Node *n = *it;
            sortedNode.push_back(n);
        }
        //std::cout<<"before sort\n";
        std::sort(sortedNode.begin(), sortedNode.end(), dep_cmp2);
        //std::cout<<"finish sort\n";
        for(unsigned int i=0;i<sortedNode.size();i++){
            //std::cout<<"split node is:"<<sortedNode.at(i)->Name.name()<<"\n";
            //std::cout<<"before split nodes\n";
            this->splitNode(sortedNode.at(i));
            //std::cout<<"after split nodes\n";
        }
    
    }
    /* buildCDD: updates tree to be CDD, returns correspondence. */
    void Duality::DerivationDAGShara::buildCDDRec(Node *n,std::set<Node *> visited){
        std::vector<Edge *> OutgoingEdges=n->Outgoing;
        if(this->buildVisitedNodes.find(n) == this->buildVisitedNodes.end()){
            this->buildVisitedNodes.insert(n);
        }
        for(std::vector<Edge *>::iterator it=OutgoingEdges.begin();it!=OutgoingEdges.end();it++){
            Edge *theEdge=*it;
            std::vector<Node *> Children=theEdge->Children;
            std::vector<Node *> newChildren;
            std::set<Node *> newVisited;
            for(std::set<Node *>::iterator nodeVisited=visited.begin();nodeVisited!=visited.end();nodeVisited++){
                Node *theNode=*nodeVisited;
                if(newVisited.find(theNode) == newVisited.end()){
                    newVisited.insert(theNode);
                }
            }
            for(std::vector<Node *>::iterator child=Children.begin();child!=Children.end();child++){
                Node *theChild=*child;
                if(newVisited.find(theChild) != newVisited.end()){
                    Node *cp_theChild=this->tree->CloneNode(theChild);
                    this->CopyNodes.insert(cp_theChild);
                    if(this->buildVisitedNodes.find(cp_theChild) == this->buildVisitedNodes.end()){
                        this->buildVisitedNodes.insert(cp_theChild);
                    }
                    if(this->buildVisitedNodes.find(theChild) == this->buildVisitedNodes.end()){
                        this->buildVisitedNodes.insert(theChild);
                    }
                    cp_theChild->Annotation.Formula=this->ctx.bool_val(true);
                    //std::cout<<"if this being called\n";
                    //std::cout<<theChild->Name.name()<<"#"<<theChild->number<<"\n";
                    cp_theChild->level=theChild->level;
                    CopyToOriginal[cp_theChild]=CopyToOriginal[theChild];
                    cp_theChild->map=theChild->map;
                    std::vector<Edge *> newOutgoingEdge;
                    for(std::vector<Edge *>::iterator it2=theChild->Outgoing.begin();it2!=theChild->Outgoing.end();it2++){
                        Edge *originalEdge =*it2;
                        Edge *newEdge=this->tree->CreateEdge(cp_theChild,originalEdge->F,originalEdge->Children);
                        newOutgoingEdge.push_back(newEdge);
                    }
                    cp_theChild->Outgoing=newOutgoingEdge;
                    cp_theChild->Incoming.push_back(theEdge);
                    newChildren.push_back(cp_theChild);
                    std::set<Node *> seed;
                    seed.insert(cp_theChild);
                    buildCDDRec(cp_theChild,newVisited);
                    std::set<Edge *> removeEdges;
                    for(std::vector<Edge *>::iterator possibleChangeEdge=theChild->Incoming.begin();possibleChangeEdge!=theChild->Incoming.end();possibleChangeEdge++){
                        Edge *possbileEdge=*possibleChangeEdge;
                        bool move=false;
                        if(this->buildVisitedNodes.find(possbileEdge->Parent) == this->buildVisitedNodes.end()){
                            //std::cout<<"before collect conjunction nodes\n";
                            std::set<Node *> conjunctionNodes=this->collectConjunctionNodes(possbileEdge->Parent);
                            //std::cout<<"after collect conjunction nodes\n";
                            if( conjunctionNodes.find(theEdge->Parent) == conjunctionNodes.end() ){
                                move=true;
                            }
                        }
                        if(move){
                            cp_theChild->Incoming.push_back(possbileEdge);
                            if(removeEdges.find(possbileEdge) == removeEdges.end()){
                                removeEdges.insert(possbileEdge);
                            }
                            //std::cout<<"there is a move\n";
                            //std::cout<<cp_theChild->Name.name()<<"#"<<cp_theChild->number<<"\n";
                            std::vector<Node *> allNewChildren;
                            for(unsigned int index=0;index<possbileEdge->Children.size();index++){
                                if(possbileEdge->Children.at(index) == theChild){
                                    allNewChildren.push_back(cp_theChild);
                                    //std::cout<<"here it works\n";
                                }
                                else{
                                    allNewChildren.push_back(possbileEdge->Children.at(index));
                                }
                            }
                            possbileEdge->Children=allNewChildren;
                        }
                        
                    }
                    std::vector<Edge *> newIncomingEdges2;
                    for(std::vector<Edge *>::iterator it15=theChild->Incoming.begin();it15!=theChild->Incoming.end();it15++){
                        Edge* potentialRemoveEdge = *it15;
                        if(removeEdges.find(potentialRemoveEdge) == removeEdges.end()){
                            if(std::find(newIncomingEdges2.begin(), newIncomingEdges2.end(), potentialRemoveEdge) ==newIncomingEdges2.end()){
                                newIncomingEdges2.push_back(potentialRemoveEdge);
                            }
                        }
                    }
                    theChild->Incoming=newIncomingEdges2;
                    std::set<Node *> allDepends=RPFP::collectDependencies(seed);
                    for(std::set<Node *>::iterator deps=allDepends.begin();deps!=allDepends.end();deps++){
                        Node* depNode=*deps;
                        if(newVisited.find(depNode) == newVisited.end()){
                            newVisited.insert(depNode);
                        }
                    }
                }
                else{
                    if(this->buildVisitedNodes.find(theChild) == this->buildVisitedNodes.end()){
                        this->buildVisitedNodes.insert(theChild);
                    }
                    newChildren.push_back(theChild);
                    std::set<Node *> seed;
                    seed.insert(theChild);
                    buildCDDRec(theChild,newVisited);
                    std::set<Node *> allDepends=RPFP::collectDependencies(seed);
                    //std::cout<<"all depens size is "<<allDepends.size()<<"\n";
                    for(std::set<Node *>::iterator deps=allDepends.begin();deps!=allDepends.end();deps++){
                        Node* depNode=*deps;
                        if(newVisited.find(depNode) == newVisited.end()){
                            newVisited.insert(depNode);
                        }
                    }
                }
            }
            for(std::vector<Node *>::iterator oldChild=Children.begin();oldChild!=Children.end();oldChild++){
                Node* oldChildNode=*oldChild;
                if(std::find(newChildren.begin(), newChildren.end(), oldChildNode) == newChildren.end()){
                    std::vector<Edge *> IncomingEdges=oldChildNode->Incoming;
                    std::vector<Edge *> newIncomingEdges;
                    for(std::vector<Edge *>::iterator oldIncomEdge=IncomingEdges.begin();oldIncomEdge!=IncomingEdges.end();oldIncomEdge++){
                        Edge *theOldeEdge=*oldIncomEdge;
                        if(theOldeEdge !=theEdge){
                            newIncomingEdges.push_back(theOldeEdge);
                        }
                    }
                    oldChildNode->Incoming=newIncomingEdges;
                }
            }
            theEdge->Children=newChildren;
            
        }
    }
  void Duality::DerivationDAGShara::buildCDD() {
      /* std::ofstream outputfile1;
      outputfile1.open("buildCDDTime.txt", std::ios_base::app);
      output_time(outputfile1,current_time());
      outputfile1<<"\n"; */
      std::set<Node *> visited;
      collectAllEdge(top,visited);
      Copy();
      std::set<Node *> visited2;
      //std::cout<<"before build CDD2\n";
      //this->buildCDD2();
      //std::cout<<"after build CDD2\n";
      this->buildVisitedNodes.clear();
      buildCDDRec(this->virtualTop,visited2);
      /* output_time(outputfile1,current_time());
      outputfile1<<"\n";
      outputfile1.close(); */
      /*std::ofstream outputfile2;
      outputfile2.open("numberOfNodes", std::ios_base::app);
      outputfile2<<originalNodes.size()<<"\n";
      outputfile2<<newNodes.size()<<"\n";
      outputfile2.close(); */
  }
    std::set<Node *> Duality::DerivationDAGShara::collectDependenciesAndSiblings(Node* n,std::set<Node *> &siblings){
        if(this->siblings.find(n) != this->siblings.end()){
            siblings=this->siblings[n];
            return this->underDependencies[n];
        }
        std::vector<Edge *> IncomingEdges=n->Incoming;
        //std::cout<<"the incoming edge size:"<<IncomingEdges.size()<<"\n";
        std::set<Node *> dependencies;
        std::set<Node *> directDependencies;
        std::set<Node *> directSiblings;
        for(std::vector<Edge *>::const_iterator it=IncomingEdges.begin(); it!=IncomingEdges.end();++it){
           Edge* IncomingEdge = * it;
           Node* parent=IncomingEdge->Parent;
           // directDependencies doesn't have this Node
           if(directDependencies.find(parent) == directDependencies.end()){
               directDependencies.insert(parent);
               std::vector<Node *> Children=IncomingEdge->Children;
               for(std::vector<Node *>::const_iterator it2=Children.begin(); it2!=Children.end();++it2){
                   Node* child = *it2;
                   if((child != n) && (directSiblings.find(child) == directSiblings.end())){
                       directSiblings.insert(child);
                   }
               }
           }
       }
        for(std::set<Node *>::const_iterator it=directDependencies.begin(); it!=directDependencies.end();++it){
           Node *directDependency = *it;
           std::set<Node *> side_siblings;
           std::set<Node *> underDependencies;
            if(this->siblings.find(directDependency) != this->siblings.end()){
                side_siblings=this->siblings[directDependency];
                underDependencies=this->underDependencies[directDependency];
            }
            else{
            underDependencies=collectDependenciesAndSiblings(directDependency,side_siblings);
            }
           for(std::set<Node *>::const_iterator it2=underDependencies.begin(); it2!=underDependencies.end();++it2){
               Node * underDependency =  *it2;
               if(dependencies.find(underDependency) == dependencies.end()){
                   dependencies.insert(underDependency);
               }
           }
           for(std::set<Node *>::const_iterator it2=side_siblings.begin(); it2!=side_siblings.end();++it2){
               Node* side_sibling = *it2;
               if(siblings.find(side_sibling) == siblings.end()){
                   siblings.insert(side_sibling);
               }
           }
       }
       for(std::set<Node *>::const_iterator it=directDependencies.begin(); it!=directDependencies.end();++it){
           Node *directDependency = *it;
           if(dependencies.find(directDependency) == dependencies.end()){
               dependencies.insert(directDependency);
           }
       }
       for(std::set<Node *>::const_iterator it=directSiblings.begin(); it!=directSiblings.end();++it){
           Node *directSibling = * it;
           if(siblings.find(directSibling) == siblings.end()){
               siblings.insert(directSibling);
           }
       }
       return dependencies;
       
    }
    std::set<Node *> Duality::DerivationDAGShara::specialCollectDependencies2(Node * root){
        std::set<Node*> deps;
        std::set<Node*> worklist;
        worklist.insert(root);
        
        // wrharris: lookup names of all std methods
        // replace with: = worklist.is_empty() in loop;
        while (!worklist.empty()) {
            // choose an element, remove it from the worklist, add it to the deps
            Node* dep= * worklist.begin(); // wrharris: = worklist.choose();
            //std::cout<<dep->Name.name()<<"#"<<dep->number<<"\n";
            worklist.erase(dep);
            if(deps.find(dep) ==deps.end()){
                deps.insert(dep);
            }
            if(this->currentInterpolants.find(dep) != this->currentInterpolants.end()){
                //std::cout<<"it is being called\n";
                //std::cout<<dep->Name.name()<<"#"<<dep->number<<"\n";
                continue;
            }
            // for each edge going into dep,
            for (std::vector<Edge*>::iterator clause_it = dep->Outgoing.begin();
                 clause_it != dep->Outgoing.end();
                 clause_it++) {
                Edge* clause = *clause_it;
                // for each node in the clause body,
                for (std::vector<Node*>::iterator body_it = clause->Children.begin();
                     body_it != clause->Children.end();
                     body_it++) {
                    Node* n = *body_it;
                    // if the node isn't a dep,
                    
                    if (deps.find(n) == deps.end()){
                        worklist.insert(n);}
                }
            }
        }
        
        return deps;
    }

    
    std::set<Node *> Duality::DerivationDAGShara::specialCollectDependencies(std::set<Node *> roots){
        std::set<Node*> deps;
        std::set<Node*> worklist = roots;
        
        // wrharris: lookup names of all std methods
        // replace with: = worklist.is_empty() in loop;
        while (!worklist.empty()) {
            // choose an element, remove it from the worklist, add it to the deps
            Node* dep= * worklist.begin(); // wrharris: = worklist.choose();
            worklist.erase(dep);
            if(deps.find(dep) ==deps.end()){
                deps.insert(dep);
            }
            if(this->currentInterpolants.find(dep) != this->currentInterpolants.end()){
                //std::cout<<"it is being called\n";
                continue;
            }
            // for each edge going into dep,
            for (std::vector<Edge*>::iterator clause_it = dep->Outgoing.begin();
                 clause_it != dep->Outgoing.end();
                 clause_it++) {
                Edge* clause = *clause_it;
                // for each node in the clause body,
                for (std::vector<Node*>::iterator body_it = clause->Children.begin();
                     body_it != clause->Children.end();
                     body_it++) {
                    Node* n = *body_it;
                    // if the node isn't a dep,
                    
                    if (deps.find(n) == deps.end()) worklist.insert(n);
                }
            }
        }
        
        return deps;
    }
    std::set<Node *> Duality::DerivationDAGShara::collectAllContextNodes(Node* n){
        std::set<Node *> siblings;
        std::set<Node *> allDependencies=collectDependenciesAndSiblings(n,siblings);
         /* if(n->number == 11){
            //std::cout<<"node 11 siblings are:"<<"\n";
            for(Node* n1:siblings){
                if(n1->number == 3){
                //std::cout<<n1->Name.name()<<"#"<<n1->number<<"\n";
                std::set<Node *> theseSiblingCollects=this->specialCollectDependencies2(n1);
                //std::cout<<"this sibling's collections:\n";
                for(Node* sb1 : theseSiblingCollects){
                    //std::cout<<sb1->Name.name()<<"#"<<sb1->number<<"\n";
                }
                }
                
            }
        }
        if(n->number == 12){
            //std::cout<<"node 12 siblings are:"<<"\n";
            for(Node * n1:siblings){
                if(n1->number == 3){
                //std::cout<<n1->Name.name()<<"#"<<n1->number<<"\n";
                std::set<Node *> theseSiblingCollects=this->specialCollectDependencies2(n1);
                //std::cout<<"this sibling's collections:\n";
                for(Node* sb1: theseSiblingCollects){
                //std::cout<<sb1->Name.name()<<"#"<<sb1->number<<"\n";
                }
                }
            }
        } */
        //std::cout<<"size of allDependencies node is"<<allDependencies.size()<<"\n";
        std::set<Node *> dependents =this->specialCollectDependencies(siblings);

        //std::cout<<"size of original siblings node is"<<dependents.size()<<"\n";
        //std::set<Node *> specialDependents=this->specialCollectDependencies(siblings);
        //std::cout<<"size of new siblings node is"<<specialDependents.size()<<"\n";
        std::set<Node *> allContextNodes;
        for(std::set<Node *>::const_iterator it=siblings.begin(); it!=siblings.end();++it){
            Node *sibling = *it;
            if(allContextNodes.find(sibling) == allContextNodes.end()){
                allContextNodes.insert(sibling);
            }
        }
        for(std::set<Node *>::const_iterator it=allDependencies.begin(); it!=allDependencies.end();++it){
            Node *allDependency = * it;
            if(allContextNodes.find(allDependency)==allContextNodes.end()){
                allContextNodes.insert(allDependency);
            }
        }
         for(std::set<Node *>::const_iterator it=dependents.begin(); it!=dependents.end();++it){
             Node *dependent = * it;
            if(allContextNodes.find(dependent) == allContextNodes.end()){
                allContextNodes.insert(dependent);
            }
        }
        //std::cout<<"size of allContextNodes node is"<<allContextNodes.size()<<"\n";
        return allContextNodes;
    }
  TermTree* Duality::DerivationDAGShara::buildPreFormula(Node* n){
      //std::cout<<"enter buildPreFormula\n";
      std::vector<Edge *> OutgoingEdges=n->Outgoing;
      std::vector<expr> allExpr;
      allExpr.push_back(this->ctx.bool_val(false));
      for(std::vector<Edge *>::const_iterator it=OutgoingEdges.begin(); it!=OutgoingEdges.end();++it){
          //std::cout<<"this is the first loop1\n";
          Edge *OutgoingEdge = *it;
          std::vector<Node *> Children=OutgoingEdge->Children;
          expr singlePreFormula=this->ctx.bool_val(true);
          for(std::vector<Node *>::const_iterator it2=Children.begin(); it2!=Children.end();++it2){
              //std::cout<<"this is the second loop1\n";
              Node* child = *it2;
              /* if(currentInterpolants.find(child) == currentInterpolants.end()){
                  std::cout<<"it is a serious error\n";
                  std::cout<<child->Name.name();
                  std::cout<<"\n";
              } */
              expr annotation=this->currentInterpolants[child];
              singlePreFormula=singlePreFormula && annotation;
              //std::cout<<"this is the second loop2\n";
          }
          this->tree->SetEdgeMaps(OutgoingEdge,true);
          expr res = this->tree->Localize(OutgoingEdge,OutgoingEdge->F.Formula,true);
          //std::cout<<res<<"\n";
          singlePreFormula=singlePreFormula && res;
          allExpr.push_back(singlePreFormula);
          /* if(n->number == 11){
              std::cout<<singlePreFormula.simplify()<<"\n";
          } */
          //std::cout<<"this is the first loop2\n";

      }
      expr theWholeFormula=this->ctx.make(Or,allExpr);
      std::vector<TermTree *> children;
      TermTree *res=new TermTree(theWholeFormula,children);
      //std::cout<<"exit buildPreFormula\n";
      return res;
  }
  
  TermTree* Duality::DerivationDAGShara::buildContextFormula(Node* n){
      //std::cout<<"before collect all context nodes\n";
      std::set<Node *> allContextNodes = collectAllContextNodes(n);
       //std::cout<<"after collect all context nodes\n";
      //std::cout<<"the size of all context nodes:"<<allContextNodes.size()<<"\n";
      /* std::cout<<"--------------------------\n";
      std::cout<<"The n node is: "<<n->Name.name()<<"#"<<n->number<<"\n";
      std::cout<<"all contextNodes size:"<<allContextNodes.size()<<"\n";
      for(Node *n:allContextNodes){
          std::cout<<n->Name.name()<<"#"<<n->number<<"\n";
      }
      std::cout<<"--------------------------\n"; */
      //std::cout<<n->Name.name()<<"#"<<n->number<<"\n";
      /* if(n->number == 12 || n->number == 11){
          std::cout<<"the current node is:"<<n->Name.name()<<"#"<<n->number<<"\n";
          std::cout<<"the size of context formula is "<<allContextNodes.size()<<"\n";
          for(Node * n1:allContextNodes){
              std::cout<<n1->Name.name()<<"#"<<n1->number<<"\n";
          }
      } */
      std::map<Node *,expr> NodesToBoolean;
      int count=1;
      for(std::set<Node *>::const_iterator it=allContextNodes.begin(); it!=allContextNodes.end();++it){
          Node *ContextNode = *it;
          char string_of_int_buffer[20];
          sprintf(string_of_int_buffer,"%d",count);
          std::string name=std::string("boolean")+string_of_int_buffer;
          expr booleanConst=this->ctx.bool_const(name.c_str());
          NodesToBoolean[ContextNode]=booleanConst;
          count++;
      }
      char string_of_int_buffer[20];
      sprintf(string_of_int_buffer,"%d",count);
      std::string name=std::string("boolean")+string_of_int_buffer;
      expr booleanConst=this->ctx.bool_const(name.c_str());
      NodesToBoolean[n]=booleanConst;
      std::vector<expr> allFormulas;
      allFormulas.push_back(NodesToBoolean[this->virtualTop]);
      //std::cout<<"here is fine\n";
      //std::cout<<"size of allContext nodes: "<<allContextNodes.size()<<"\n";
      for(std::set<Node *>::const_iterator it=allContextNodes.begin(); it!=allContextNodes.end();++it){
          Node* n= *it;
          if(this->currentInterpolants.find(n) != this->currentInterpolants.end()){
              expr formula= this->ctx.make(Implies,NodesToBoolean[n],this->currentInterpolants[n]);
              allFormulas.push_back(formula);
              continue;
          }
          
          //std::cout<<"the nod is being build\n";
          //std::cout<<n->Name.name()<<"#"<<n->number<<"\n";
          std::vector<Edge *> OutgoingEdges=n->Outgoing;
          //std::cout<<OutgoingEdges.size()<<"\n";
          expr ContextFormula=this->ctx.bool_val(false);
          //std::cout<<ContextFormula<<"\n";
          //std::cout<<OutgoingEdges.size()<<"\n";
          for(std::vector<Edge *>::const_iterator it2=OutgoingEdges.begin(); it2!=OutgoingEdges.end();++it2){
              Edge *OutgoingEdge = *it2;
              //std::cout<<"before get Children\n";
              std::vector<Node *> Children=OutgoingEdge->Children;
              //std::cout<<"Children size:"<<Children.size()<<"\n";
              //std::cout<<"after get Children\n";
              bool ifChildIn=false;
              for(std::vector<Node *>::const_iterator it4=Children.begin(); it4!=Children.end();++it4){
                  Node *thechild = *it4;
                  if(NodesToBoolean.find(thechild) != NodesToBoolean.end()){
                      ifChildIn=true;
                      break;
                  }
              }
              if(Children.size() == 0){
                  ifChildIn=true;
                  //std::cout<<"the children size is zero\n";
              }
              if(ifChildIn){
                  //std::cout<<"the child is in\n";
              expr e=this->ctx.bool_val(true);
              for(std::vector<Node *>::const_iterator it3=Children.begin(); it3!=Children.end();++it3){
                  Node *child = *it3;
                  expr correspondBoolean=NodesToBoolean[child];
                  e= e && correspondBoolean;
              }
              //std::cout<<"before this operation\n";
              this->tree->SetEdgeMaps(OutgoingEdge,true);
              //std::cout<<"after this operation1\n";
              expr res = this->tree->Localize(OutgoingEdge,OutgoingEdge->F.Formula,true);
              //std::cout<<"after this operation2\n";
              e= (e && res);
              /* if(!OutgoingEdge->dual.null()){
                  //std::cout<<OutgoingEdge->dual;
              } */
              ContextFormula= (ContextFormula || e);
              }
          //std::cout<<"the nod is after build\n";
          }
      //std::cout<<ContextFormula<<"\n";
      ContextFormula = this->ctx.make(Implies,NodesToBoolean[n],ContextFormula);
      allFormulas.push_back(ContextFormula);
    }
      //std::cout<<"here is fine2\n";
      //std::cout<<"size of all fourmulas: "<<allFormulas.size()<<"\n";
      expr theWholeFormula = this->ctx.make(And,allFormulas);
      //std::cout<<"the whole formula\n";
      std::vector<TermTree *> children;
      TermTree *res=new TermTree(theWholeFormula,children);;
      return res;
  }
  
  /* solveCDD: given a CDD roots, tries to annotate it with a
     solution. Returns whether or not it succeeded. */
  bool Duality::DerivationDAGShara::solveCDD() {
      /* std::ofstream outputfile1;
      outputfile1.open("solveCDDTime.txt", std::ios_base::app);
      output_time(outputfile1,current_time());
      outputfile1<<"\n";
      std::ofstream outputfile2;
      outputfile2.open("realSolveCDDTime.txt", std::ios_base::app);*/
      /** sortedOrder is vector based on the toplogical order */
      std::set<Node *> root;
      root.insert(this->virtualTop);
      std::set<Node *> allRelatedNode = RPFP::collectDependencies(root);
      std::vector<Edge *> e=this->virtualTop->Outgoing;
      std::vector<Node *> sortedNode;
      for(std::set<Node *>::const_iterator it=allRelatedNode.begin(); it!=allRelatedNode.end();++it){
          Node *n = *it;
          sortedNode.push_back(n);
      }
      std::sort(sortedNode.begin(), sortedNode.end(), dep_cmp);
      bool isSat=false;
      //std::cout<<"before here is fine\n";
       /* for(int i=0;i<sortedNode.size();i++){
          Node* n= sortedNode.at(i);
          std::cout<<n->Name.name()<<"#"<<n->number<<"\n";
          //std::cout<<"level:"<<n->level<<"\n";
          //std::cout<<"topo sort value:"<<n->TopoSort<<"\n";
      }*/
      //std::cout<<sortedNode.size()<<"\n";
      for(unsigned int i=0;i<sortedNode.size();i++){
          //std::cout<<"here is the cases"<<i<<"\n";
          Node* n= sortedNode.at(i);
          //std::cout<<"before build formula\n";
        //std::cout<<n->Name.name()<<"#"<<n->number<<"\n";
        TermTree *tree = buildContextFormula(n);
          //std::cout<<"after build formula1\n";
          tree->getChildren().push_back(buildPreFormula(n));
          //std::cout<<"after build formula2\n";
          TermTree *interpolant = NULL;
          //this->slvr.add(tree->getTerm() && tree->getChildren()[0]->getTerm());
          /*std::cout<<"the double check result is\n";
          std::cout<<slvr.check(); */
          //std::cout<<"contextFormula is: "<<tree->getTerm()<<"\n";
          this->slvr.add(tree->getChildren()[0]->getTerm());
          //std::cout<<"preFormula is: "<<tree->getChildren()[0]->getTerm()<<"\n";
          interpolating_solver *iZ3Solver = new interpolating_solver(this->ctx);
          iZ3Solver->add(tree->getTerm());
          iZ3Solver->add(tree->getChildren()[0]->getTerm());
          literals _labels;
          //output_time(outputfile2,current_time());
          //outputfile2<<"\n";
          lbool res = iZ3Solver->interpolate_tree(tree, interpolant, this->tree->dualModel,_labels,true);
          //output_time(outputfile2,current_time());
          //outputfile2<<"\n";
          //std::cout<<"my own solver result is "<<res<<"\n";
          if (res == l_false){
              //std::cout<<n->Name.name()<<"\n";
              //std::cout<<"the interpolant is\n";
              //std::cout<<interpolant->getChildren()[0]->getTerm()<<"\n";
              this->currentInterpolants[n]=interpolant->getChildren()[0]->getTerm().simplify();
              //std::cout<<"correct begin\n";
               //sanity check
              
              /*  expr firstExpr=interpolant->getChildren()[0]->getTerm();
              expr second=tree->getTerm();
              expr finalExpr = firstExpr && second;
              solver *thesolver=new solver(this->ctx);
              thesolver->add(finalExpr);
              if( !(thesolver->check()== unsat)){
                  std::cout<<"there are some serious error\n";
              } */

          }
          else{
              //std::cout<<"what is the node be here\n";
              //std::cout<<n->Name.name()<<"#"<<n->number<<"\n";
              isSat=true;
              break;
          }
        delete tree;
        delete iZ3Solver;
      }
      for(std::map<Node *,expr>::const_iterator iterator = this->currentInterpolants.begin(); iterator != this->currentInterpolants.end(); iterator++) {
          Node *theNode=iterator->first;
          expr theInterpolant=iterator->second;
          hash_map<ast, expr> memo;
          expr b;
          std::vector<expr> v;
          this->tree->RedVars(theNode, b, v,true);
          memo[b] = this->ctx.bool_val(true);
          for (unsigned i = 0; i < v.size(); i++){
              memo[v[i]] = theNode->Annotation.IndParams[i];
          }
          expr annot = this->tree->SubstRec(memo, theInterpolant);
          //std::cout<<"after replace\n";
          //std::cout<<"the node name "<<theNode->Name.name()<<"\n";
          //std::cout<<annot<<"\n";
          theNode->Annotation.Formula=theNode->Annotation.Formula && annot;
          //std::cout<<theNode->Annotation.Formula<<"\n";
      }
    //std::exit(0);
    /* output_time(outputfile1,current_time());
    outputfile1<<"\n";
    outputfile2.close();
    outputfile1.close(); */
    return isSat;
  }

  /* restore: given an RPFP, solved the copied CDD expansion, and
     correspondence, annotated RPFP with solution as collapsing of the
     solution of the expansion. */
  void Duality::DerivationDAGShara::restore()
  {
      std::set<Node *> originalNodes;
      for(std::map<Node*,Node*>::iterator it=CopyToOriginal.begin();it != CopyToOriginal.end();it++){
          Node *copy=it->first;
          Node *original=it->second;
          //std::cout<<"it is once\n";
          //std::cout<<copy->Name.name()<<"#"<<copy->number<<"\n";
          original->Annotation.Formula=original->Annotation.Formula && copy->Annotation.Formula;
          if(originalNodes.find(original) == originalNodes.end()){
              originalNodes.insert(original);
          }
      }
      for(std::set<Node*>::iterator it=originalNodes.begin(); it != originalNodes.end();it++){
          Node *n= * it;
          n->Annotation.Formula=n->Annotation.Formula.simplify();
      }
  }
    
 bool Duality::DerivationDAGShara::Derive(RPFP *rpfp, RPFP::Node *root, bool _underapprox, bool _constrained, RPFP *_tree){
        //std::cout<<"Derive2 is being called\n";
        underapprox = _underapprox;
        constrained = _constrained;
        false_approx = true;
        timer_start("Derive");
        tree = _tree ? _tree : new RPFP(rpfp->ls);
        tree->HornClauses = rpfp->HornClauses;
        tree->Push(); // so we can clear out the solver later when finished
        top = root;
        //tree->AssertNode(top); // assert the negation of the top-level spec
        timer_start("Build");
        bool res = this->Build();
        heuristic->Done();
        timer_stop("Build");
        timer_start("Pop");
        tree->Pop(1);
        timer_stop("Pop");
        timer_stop("Derive");
        //std::cout<<"Derive2 finished being called\n";
        return res;
    }
// Build: entry point into the solver.
  bool Duality::DerivationDAGShara::Build() {
      //std::cout<<"before build cdd\n";
      //std::set<Node *> visited;
      //prettyPrint(top,visited);
      buildCDD();
      //std::set<Node *> visited2;
      //std::cout<<"after build cdd1\n";
      //std::set<Node *> visited3;
      //prettyPrint(virtualTop,visited3);
     //exit(0);
    //std::cout<<"after build cdd2\n";
    //try to solve it:
    bool solved = true;
    if (!solveCDD()) {
       //std::cout<<"before collapse\n";
      // if CDD expansion has a solution, collapse to get it:
        restore();
        //std::cout<<"after collapse\n";
      solved = false;
    }
    //std::cout<<"the result is"<<solved<<"\n";
    //std::cout<<"finish build2\n";
    return solved;
  }
}
