#include <chrono>
#include <cstdio>
#include <utility>
#include <vector>
#include <set>
#include <map>
#include <limits>
#include <tuple>

#include "matrix.h"

double INF = std::numeric_limits<double>::infinity();

/* Global variables holding the matrix data. To complete this assignment
 * you are requested to only use arrays and access these arrays with
 * subscripts. Do not use pointers.
 */

const int max_n_elements = 100000000; //100 million
const int max_n_rows = 10000000; //10 million
const int test_vector_count = 5;

static double values[max_n_elements];

static int col_ind[max_n_elements];
static int row_ptr_begin[max_n_rows];
static int row_ptr_end[max_n_rows];

typedef unsigned int Node;  // Node identifier
typedef std::pair<Node, Node> Edge;  // Edge (Node, Node) used in MST calculation
typedef std::set<Node> NodeList;  // Vector of node identifiers
typedef std::map<Node, NodeList> EdgeMap;  // Map of edges from key Node to each of values in NodeList
typedef std::vector<std::set<Node>> ComponentList;  // Vector of component sets 
typedef std::vector<std::vector<Node>> LayerList; //List of layers with nodes


/**
 * @brief Find the value at row, column in the global CRF weight matrix.
 * 
 * @param row The row of the desired element.
 * @param col The column of the desired element.
 * 
 * @returns The value of the element (assumed to be 0 if not in CRF matrix).
*/
double get_weight(int row, int col) {
  for (int i = row_ptr_begin[row]; i <= row_ptr_end[row]; ++i) {
    if (col_ind[i] == col) {
      return values[i];
    }
  }
  return 0.0;
}


/**
 * @brief Counts edges in input EdgeMap
 * 
 * @param E Edge map, where key is a node and its value is a vector of adjacent nodes
 * 
 * @returns Number (int) of edges in EdgeMap E
*/
inline int count_edges(EdgeMap E) {
  int count = 0;

  for (const auto& node : E) {
    count += node.second.size();
  }

  return count;
}

int find_first(const bool array[], unsigned int len, bool value) {
  for (unsigned int i = 0; i < len; ++i) {
    if (array[i] == value) {
      return i;
    }
  }
  return -1;
}

bool all_set(const bool array[], unsigned int len, bool value) {
  for (unsigned int i = 0; i < len; ++i) {
    if (array[i] != value) {
      return false;
    }
  }
  return true;
}

int compute_disjoints(EdgeMap edgeMap, bool print) {
unsigned int n_nodes = edgeMap.size();
  Node unmarked; //Index of node we are finding neighbors of
  unsigned int layerIndex; //Layer whose nodes we are finding neighbors of
  bool marked[n_nodes] = {false}; //Nodes added to the BFS tree(s)
  std::vector<Node> nextLayer; //Contains node numbers of next layer
  LayerList layerList;  //Vector of vectors containing node numbers of layer
  int disjoints = 0; //List containing all disjoint BFS trees

  int total_edge_count;
  double total_tree_weight, weight;
  std::vector<std::tuple<Node, Node, double>> tree_edges;

  while (!all_set(marked, n_nodes, true)) {
    total_edge_count = 0;
    total_tree_weight = 0.0;
    tree_edges.clear();

    layerList.clear();
    nextLayer.clear();

    //Find first unmarked node to start BFS from
    unmarked = find_first(marked, n_nodes, false);
    nextLayer.push_back(unmarked);
    marked[unmarked] = true;

    //Do until nextLayer comes up empty (BFS is finished)
    layerIndex = 0;
    do {
      layerList.push_back(nextLayer);
      nextLayer.clear();
      //For every node in current layer...
      for (Node nodeIndex : layerList[layerIndex]) {
        //...Add neighbors of this node to next layer
        for (Node neighborIndex : edgeMap[nodeIndex]) {
          if (!marked[neighborIndex]) {
            nextLayer.push_back(neighborIndex);
            marked[neighborIndex] = true;
            weight = get_weight(nodeIndex, neighborIndex);
            tree_edges.push_back(std::make_tuple(nodeIndex, neighborIndex, weight));
          }
        }
      }
      ++layerIndex;
    } while (!nextLayer.empty());

    //Add this LayerList to list of disjoints
    ++disjoints;

    // Print results
    if (print) {
      total_edge_count = tree_edges.size();
      fprintf(stdout, "%d\n", total_edge_count);
      
      for (auto edge : tree_edges) {
        fprintf(stdout, "%d %d %.20f\n", std::get<0>(edge), std::get<1>(edge), std::get<2>(edge));
        total_tree_weight += std::get<2>(edge);
      }

      fprintf(stdout, "%.20f\n\n", total_tree_weight);
    }
  }

  return disjoints;
}


void print_matrix(char title[], EdgeMap E) {
  puts(title);
  for (const auto& node : E) {
      for (const auto& nibba : node.second) {
        printf("Weight for (%i,%i): %f\n", node.first, nibba, get_weight(node.first, nibba));
      }
    }
  printf("Disjoints: %d\n", compute_disjoints(E, false));
}

/**
 * @brief Approximately distributes edges of input EdgeMap over number of processes.
 * 
 * @param E Edge map, where key is a node and its value is a vector of adjacent nodes
 * @param C Vector of sets of components
 * @param C_index Array of node index pointers in ComponentList C
 * @param size Amount of elements in C_index array
 * @param num_procs Amount of processes to divide edges over
 * 
 * @returns Vector of NodeLists where the edges are approximately equally distributed over sets
*/
std::vector<NodeList> distribute_edges(EdgeMap E, ComponentList C, 
unsigned int * C_index, unsigned int size, unsigned int num_procs) {
  std::vector<NodeList> N;  // Vector of node sets
  NodeList n;  // Vector of nodes to be assgined to a node set
  int num_edges = count_edges(E);
  int target =  num_edges / num_procs;

  // TODO: optimize for more equal distribution
  int count = 0;
  for (const auto& component : C) {
    for (const auto& node : component) {
      n.insert(node);
      count += E.at(node).size();
    }

    if (count > target) {
        N.push_back(n);
        n.clear();
        count = 0;
    }
  }

  // Push remaining edges to final set
  if (count && N.size() < num_procs) {
    N.push_back(n);
  }

  return N;
}


/**
 * @brief Computes the minimal edges for each component in input NodeList.
 * 
 * @param E Edge map, where key is a node and its value is a vector of adjacent nodes
 * @param C Vector of sets of components
 * @param n Node vector
 * 
 * @returns Returns vector of minimal edges for components in input NodeList
*/
std::set<Edge> get_minimum_edges(EdgeMap E, ComponentList C, NodeList n,
unsigned int * C_index, unsigned int size) {
  std::set<Edge> E_min;
  Edge min_edge;
  double min_weight, weight;
  bool found;

  for (const auto& component : C) {
    found = false;
    if (!component.empty()) {
      min_weight = INF;
      for (const auto& node : component) {
        for (const auto& adjacent : E[node]) {

          weight = get_weight(node, adjacent);
          if (weight < min_weight && node != adjacent) {
            // Add minimal edge from component to adjacent component using component indexes
            min_edge = std::make_pair(node, adjacent);
            min_weight = weight;

            found = true;
          }
        }
      }
      if (found) {
        E_min.insert(min_edge);
      }
    }
  }

  return E_min;
}


inline unsigned int count_non_empty(ComponentList C) {
  unsigned int count = 0;
  
  for (ComponentList::iterator it = C.begin(); it < C.end(); it++) {
    if (!(it->empty())) {
      count++;
    }
  }

  return count;
}


/**
 * @brief Adds Edge edge to EdgeMap E
 * 
 * @param E EdgeMap
 * @param edge Edge to be added to E
 * 
 * @returns void
*/
inline void add_edge(EdgeMap & E, Edge edge) {
  if (E.find(edge.first) != E.end()) {
      E[edge.first].insert(edge.second);
  } else {
      if (edge.first == edge.second) {
        fprintf(stderr, "WRN: Found edge (%u,%u)\n", edge.first, edge.second);
        fprintf(stderr, "Skipping edge (%u,%u)\n", edge.first, edge.second);
      } else {
        E[edge.first] = NodeList({edge.second});
      }
      // E[edge.first] = NodeList({edge.second});
  }
}


/**
 * @brief
 * 
 * @param E EdgeMap
 * @param edge Edge to be removed from E
 * 
 * @returns void
*/
inline void delete_edge(EdgeMap & E, Edge edge) {
  auto nodelist_it = E.find(edge.first);
  if (nodelist_it != E.end()) {
    auto neighbor_it = nodelist_it->second.find(edge.second);
    if (neighbor_it != nodelist_it->second.end()) {
      nodelist_it->second.erase(neighbor_it);
    }
  }
}


Edge mirror(Edge edge) {
  return std::make_pair(edge.second, edge.first);
}


/**
 * @brief Contracts nodes using minimal edges from E_min
 * 
 * @param E EdgeMap representation of undirrected graph
 * @param E_min Vector of Edge pairs with minimal weight
 * @param C Vector of Node sets, components
 * @param C_index Array to index component from nodes
 * @param size Size of C_index array
 * 
 * @returns
*/
EdgeMap contract(EdgeMap & E, std::set<Edge> E_min, ComponentList & C, 
unsigned int * C_index, unsigned int size) {
  EdgeMap mst_p; //Partial MST computed in this processor
  Edge edge_temp;
  Edge current_edge;
  std::vector<Edge> markedForDelete;
  std::map<unsigned int, Edge> C_connected; //Saves min-weight to foreign comp.
  unsigned int c_current, c_foreign;

  // Perform contraction using minimal weight edges
  // Update EdgeMap
  // Update mst_p with contracted edges
  while (!E_min.empty()) {
    current_edge = *(E_min.begin());

    //Remove edge from min-edges
    E_min.erase(current_edge);
    E_min.erase(mirror(current_edge));

    //Remove edge from edgelist
    delete_edge(E, current_edge);
    delete_edge(E, mirror(current_edge));

    //Add edge to MST
    add_edge(mst_p, current_edge);
    add_edge(mst_p, mirror(current_edge));

    //Merge components of vertices connected by edge: Add every vertex in
    //current to foreign component, and set component indices of these nodes
    //to 1. Also clear component 2.
    c_current = C_index[current_edge.first];
    c_foreign = C_index[current_edge.second];
    for (const auto& node : C[c_foreign]) {
      //Add every vertex in c2 to c1
      C[c_current].insert(node);
      C_index[node] = c_current;
    }
    C[c_foreign].clear();

    //Compare weights of 'double' edges to component and only keep minimal ones.
    //Iterate over the neighbors of all nodes in component; if multiple nodes
    //have neighbors in the same foreign component, only keep cheapest edge.
    markedForDelete.clear(); 
    C_connected.clear();
    for (const auto& node : C[c_current]) {
      for (auto it = E[node].begin(); it != E[node].end(); ++it) {
        if (C_connected.find(C_index[*it]) != C_connected.end()) {
          //Foreign component encountered earlier; choose which edge to keep
          edge_temp = C_connected.at(C_index[*it]);
          if (get_weight(node, *it) < get_weight(edge_temp.first, edge_temp.second)) {
            //New edge cheaper than previously encountered; DELETE existing
            markedForDelete.push_back(edge_temp);
            markedForDelete.push_back(mirror(edge_temp));
            //REPLACE cheapest edge to foreign component with newly found.
            C_connected.at(C_index[*it]) = std::make_pair(node, *it);
          } else {
            //Newly found edge not cheaper than existing; DELETE newly found
            markedForDelete.push_back(std::make_pair(*it, node));
            markedForDelete.push_back(std::make_pair(node, *it));
          }
        } else {
          //Foreign component not encountered yet; REMEMBER
          C_connected[C_index[*it]] = std::make_pair(node, *it);
        }
      }
    }
    for (const auto& edge : markedForDelete) {
      delete_edge(E, edge);
    }
    
  }

  return mst_p;
}


/**
 * @brief Sequential implemtation of merge
 * 
 * @param mst EdgeMap reference to save MST in
 * @param mst_P Vector of partial MSTs to be merged
 * 
 * @returns void
*/
inline void merge_sequential(EdgeMap &mst, std::vector<EdgeMap> mst_P) {
  for (const auto &mst_p : mst_P) {
    for (const auto &node_edges : mst_p) {
      for (const auto &adjacent : node_edges.second) {
        add_edge(mst, std::make_pair(node_edges.first, adjacent));
      }
    }
  }
}


EdgeMap initialize_mst(const EdgeMap &E) {
  EdgeMap mst;
  for (const auto &elem : E) {
    mst[elem.first] = {};
  }
  return mst;
}

/**
 * @brief Compute the minimum spanning tree (MST) of the input EdgeMap.
 * 
 * @param E Edge map, where key is a node and its value is a vector of adjacent nodes
 * @param C Vector of sets of components
 * @param C_index Array of node index pointers in ComponentList C
 * @param size Amount of elements in C_index array
 * 
 * @returns EdgeMap containing the MST of the input EdgeMap
*/
EdgeMap compute_mst(EdgeMap E, ComponentList C, unsigned int *C_index, unsigned int size) {
  EdgeMap mst = initialize_mst(E);
  std::vector<EdgeMap> mst_P;
  std::vector<NodeList> N;  // Node sets to assign to processes
  std::set<Edge> E_min;  // Minimum edges between nodes from a node set
  unsigned int num_procs = 1;  // TODO: change to real |P|

  unsigned int old_components = C.size()+1;
  unsigned int num_components = C.size();
  while (old_components > num_components) {
    old_components = num_components;

    //Distribute vertices over processors, with approx. equal number of edges.
    N.clear();
    N = distribute_edges(E, C, C_index, size, num_procs);

    //Have every processor compute partial MST
    mst_P.clear();
    for (unsigned int p = 0; p < N.size(); p++) {
      E_min = get_minimum_edges(E, C, N[p], C_index, size);
      mst_P.push_back(contract(E, E_min, C, C_index, size));
    }
    
    merge_sequential(mst, mst_P);
    num_components = count_non_empty(C);
  }

  return mst;
}


/**
 * @brief Initializes every node from edge map as a component.
 * 
 * @param E Edge map, where key is node and its value is a vector of adjacent nodes.
 * 
 * @returns Vector of component sets. At start, every node is its own component.
*/
inline ComponentList init_components(EdgeMap E) {
  ComponentList C;

  for (const auto& node : E) {
    C.push_back({node.first});
  }

  return C;
}


/**
 * @brief Initializes component index array.
 * 
 * @param C_index Array of indexes of node in component list (e.g. Node i is in Component j)
 * @param size Size of the C_index array
 * 
 * @returns Array of component index pointers.
*/
inline void init_component_indexes(unsigned int * C_index, unsigned int size) {
  for (unsigned int i = 0; i < size; i++) {
    C_index[i] = i;
  }
}


/**
 * @brief Transforms a matrix in compressed-row format into an edge map.
 * 
 * @param n_rows Amount of rows in the matrix
 * 
 * @returns map of edges, with as key a node number and value a vector of adjacent nodes
*/
EdgeMap crf_to_edge_map(int n_rows) {
  EdgeMap E;
  NodeList N_adjacents;
  int column;

  for (int row = 0; row < n_rows; ++row) {
    N_adjacents.clear();

    for (int row_ptr = row_ptr_begin[row]; row_ptr <= row_ptr_end[row]; ++row_ptr) {
      column = col_ind[row_ptr];
      if (column != row){
        N_adjacents.insert(column);
      }
    }

    E[row] = N_adjacents;
  }

  return E;
}


int
main(int argc, char **argv)
{
  if (argc != 2)
    {
      fprintf(stderr, "usage: %s <filename>\n", argv[0]);
      return -1;
    }

  int nnz, n_rows, n_cols;
  bool ok(false);

  ok = load_matrix_market(argv[1], max_n_elements, max_n_rows,
                          nnz, n_rows, n_cols,
                          values, col_ind, row_ptr_begin, row_ptr_end);
  if (!ok)
    {
      fprintf(stderr, "failed to load matrix.\n");
      return -1;
    }
  
  /* Init */
  EdgeMap E = crf_to_edge_map(n_rows);  // Convert matrix into edgelist
  ComponentList C = init_components(E);  // Initialize component list using edge map
  int num_components = C.size();
  unsigned int C_index[num_components];  // Array used for fast component indexing
  init_component_indexes(C_index, num_components);  // Initialize component index array

  auto mst_start_time = std::chrono::high_resolution_clock::now();

  /* Perform MST algorithm here */
  EdgeMap mst = compute_mst(E, C, C_index, num_components);

  auto mst_end_time = std::chrono::high_resolution_clock::now();
  
  std::chrono::duration<double> mst_elapsed_time = mst_end_time - mst_start_time;  
  
  /* Print results */

  printf("Printing results...\n");
  fprintf(stdout, "%.20f\n", mst_elapsed_time.count());
  compute_disjoints(mst, true);

  return 0;
}
