#include <iostream>
#include <fstream>
#include <map>
#include <algorithm>
#include <cstdlib>
#include <time.h>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/vf3_sub_graph_iso.hpp>
#include <boost/graph/random.hpp>
#include <boost/property_map/property_map.hpp>
#include <boost/random.hpp>
#include <boost/random/variate_generator.hpp>
#include <boost/random/uniform_real.hpp>
#include <boost/random/uniform_int.hpp>
#include <boost/random/mersenne_twister.hpp>
#include <boost/lexical_cast.hpp>
#include <boost/graph/graphviz.hpp>

struct VertexProps {
    std::string label;
    std::string color;
};

struct EdgeProps {
    double weight;
};

typedef boost::adjacency_list<
        boost::vecS,
        boost::vecS,
        boost::bidirectionalS,
        VertexProps,
        EdgeProps> graph;

typedef boost::graph_traits<graph>::vertex_descriptor vertex_type;
typedef boost::graph_traits<graph>::edge_descriptor edge_type;

using namespace boost;

int main(int argc, char* argv[])
{
    
    boost::adjacency_list<
        boost::vecS,
        boost::vecS,
        boost::bidirectionalS,
        VertexProps,
        EdgeProps> target_graph;

    auto vertex_propmap = boost::get(boost::vertex_bundle, target_graph);
    auto edge_propmap = boost::get(boost::edge_bundle, target_graph);

    for(int i=0; i<13; ++i) {
        vertex_type v = boost::add_vertex(target_graph);
        if (i+1 == 1 || i+1 == 6 || i+1 == 12) {
            vertex_propmap[v].label = "lc";
        } else if (i+1 == 2 || i+1 == 8 || i+1 == 10 || i+1 == 4) {
            vertex_propmap[v].label = "la";
        } else if (i+1 == 3 || i+1 == 9) {
            vertex_propmap[v].label = "lb";
        } else if (i+1 == 5 || i+1 == 7 || i+1 == 11 || i+1 == 13) {
            vertex_propmap[v].label = "ld";
        }
    }
    std::vector<std::pair<int, int>> edges = { {1,2}, {2,1}, {2,12}, {2,13}, {3,2}, {3,13}, {3,4}, {4,13}, {4,6}, {5,4}, {6,5}, {6,7}, {7,8}, {8,7}, {8,13}, {9,10}, {9,13}, {9,8}, {10,12}, {11, 10}, {12,1}, {12,11}, {13,12}, {13,3}, {13,6}, {13,9}};
    for(const auto& edge : edges) {
        boost::add_edge(edge.first - 1, edge.second - 1, target_graph);
    }

    boost::adjacency_list<
        boost::vecS,
        boost::vecS,
        boost::bidirectionalS,
        VertexProps,
        EdgeProps> pattern_graph;
    
    auto vertex_propmap_pattern = boost::get(boost::vertex_bundle, pattern_graph);
    auto edge_propmap_pattern = boost::get(boost::edge_bundle, pattern_graph);
    for(int i=0; i<5; ++i)
    {
        vertex_type v = boost::add_vertex(pattern_graph);
        if (i+1 == 2) {
            vertex_propmap_pattern[v].label = "la";
        } else if (i+1 == 3) {
            vertex_propmap_pattern[v].label = "lb";
        } else if (i+1 == 5) {
            vertex_propmap_pattern[v].label = "lc";
        } else {
            vertex_propmap_pattern[v].label = "ld";
        }
    }

    std::vector<std::pair<int,int>> pattern_edges = {{1,2}, {2,4}, {2,5}, {3,2}, {3,4}, {4,3}, {4,5}, {5,1}};
    for(const auto& edge : pattern_edges) {
        boost::add_edge(edge.first - 1, edge.second - 1, pattern_graph);
    }
    typedef boost::adjacency_list<
        boost::vecS,
        boost::vecS,
        boost::bidirectionalS,
        VertexProps,
        EdgeProps> graph;
    auto target_label_map = boost::get(&VertexProps::label, target_graph);
    auto pattern_label_map = boost::get(&VertexProps::label, pattern_graph);

    auto small_node_classification_func = [&pattern_label_map](vertex_type v, const graph& g) {
        return pattern_label_map[v];
    };

    auto large_node_classification_func = [&target_label_map](vertex_type v, const graph& g) {
        return target_label_map[v];
    };

    detail::matcher<graph, graph, decltype(target_label_map), decltype(pattern_label_map)> engine(target_graph, pattern_graph, target_label_map, pattern_label_map, large_node_classification_func, small_node_classification_func);
    std::vector<std::unordered_map<vertex_type, vertex_type>> res{};
    engine.match(res);
    for(const auto& mapping: res)
    {
        for(const auto& p: mapping) {
            std::cout << "Large graph node: " << p.second+1 << " Mapped to: " << p.first+1 << std::endl;
        }
    }
    std::cout << std::endl;
    return 1;
}