#ifndef BOOST_VF3_SUB_GRAPH_ISO_HPP
#define BOOST_VF3_SUB_GRAPH_ISO_HPP

#include <iostream>
#include <iomanip>
#include <iterator>
#include <vector>
#include <utility>

#include <boost/assert.hpp>
#include <boost/concept/assert.hpp>
#include <boost/concept_check.hpp>
#include <boost/graph/graph_utility.hpp>
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/mcgregor_common_subgraphs.hpp> // for always_equivalent
#include <boost/graph/named_function_params.hpp>
#include <boost/type_traits/has_less.hpp>
#include <boost/mpl/int.hpp>
#include <boost/range/algorithm/sort.hpp>
#include <boost/tuple/tuple.hpp>
#include <boost/utility/enable_if.hpp>

#ifndef BOOST_GRAPH_ITERATION_MACROS_HPP
#define BOOST_ISO_INCLUDED_ITER_MACROS // local macro, see bottom of file
#include <boost/graph/iteration_macros.hpp>
#endif

namespace boost
{

namespace detail 
{
    template < typename GraphLarge, typename GraphSmall, 
               typename NodeAttrPropertyMapLarge, typename NodeAttrPropertyMapSmall,
               typename NodeClassificationType = std::string >
    class matcher;

    template < typename GraphLarge_, typename GraphSmall_, 
               typename NodeAttrPropertyMapLarge_, typename NodeAttrPropertyMapSmall_,
               typename NodeClassificationType_ >
    class state
    {
        typedef typename graph_traits<GraphLarge_>::vertex_descriptor VertexLargeType;
        typedef typename graph_traits<GraphSmall_>::vertex_descriptor VertexSmallType;

        public:
        state(): matcher_ptr(nullptr) {}
        state(matcher<GraphLarge_, GraphSmall_, NodeAttrPropertyMapLarge_, NodeAttrPropertyMapSmall_, NodeClassificationType_>* m, 
                VertexLargeType v_large = graph_traits<GraphLarge_>::null_vertex(), VertexSmallType v_small = graph_traits<GraphSmall_>::null_vertex())
        : v_large_(v_large)
        , v_small_(v_small)
        , matcher_ptr(m)
        {
            auto& matcher_ = *matcher_ptr;
            depth_ = matcher_.core_large_.size();
            if (v_large_ != graph_traits<GraphLarge_>::null_vertex() && 
                v_small_ != graph_traits<GraphSmall_>::null_vertex())
            {
                matcher_.core_large_[v_large_] = v_small_;
                matcher_.core_small_[v_small_] = v_large_;
                depth_ = matcher_.core_large_.size();
                if (matcher_.large_predecessors_.find(v_large_) == matcher_.large_predecessors_.end())
                {
                    matcher_.large_predecessors_[v_large_] = depth_;
                }
                if (matcher_.large_successors_.find(v_large_) == matcher_.large_successors_.end())
                {
                    matcher_.large_successors_[v_large_] = depth_;
                }
                std::unordered_set<VertexLargeType> new_nodes;
                for(const auto& p: matcher_.core_large_)
                {
                    auto node = p.first;
                    auto in_edge_it = boost::in_edges(node, matcher_.graph_large_);
                    for(auto it = in_edge_it.first; it != in_edge_it.second; ++it)
                    {
                        VertexLargeType pred = boost::source(*it, matcher_.graph_large_);
                        if (matcher_.core_large_.find(pred) == matcher_.core_large_.end())
                        {
                            new_nodes.insert(pred);
                        }
                    }
                }
                for(VertexLargeType node: new_nodes)
                {
                    if (matcher_.large_predecessors_.find(node) == matcher_.large_predecessors_.end())
                    {
                        matcher_.large_predecessors_[node] = depth_;
                    }
                }
                new_nodes.clear();
                for(const auto& p: matcher_.core_large_)
                {
                    auto node = p.first;
                    auto out_edge_it = boost::out_edges(node, matcher_.graph_large_);
                    for(auto it = out_edge_it.first; it != out_edge_it.second; ++it)
                    {
                        VertexLargeType succ = boost::target(*it, matcher_.graph_large_);
                        if(matcher_.core_large_.find(succ) == matcher_.core_large_.end())
                        {
                            new_nodes.insert(succ);
                        }
                    }
                }
                for(VertexLargeType node: new_nodes)
                {
                    if(matcher_.large_successors_.find(node) == matcher_.large_successors_.end())
                    {
                        matcher_.large_successors_[node] = depth_;
                    }
                }

            } else if (v_large_ == graph_traits<GraphLarge_>::null_vertex() && 
                        v_small_ == graph_traits<GraphSmall_>::null_vertex()) {
                std::cout << "HERE" << std::endl;
                matcher_.core_small_.clear();
                matcher_.core_large_.clear();
                matcher_.large_successors_.clear();
                matcher_.large_predecessors_.clear();
            }
            std::cout << "New state with: Depth:" << depth_ << std::endl;
            for(const auto& p: matcher_.core_large_)
            {
                std::cout << p.first+1 << " mapped to " << p.second+1 << "|";
            }
            std::cout << std::endl;
            std::cout << "Preds in new_state: " << std::endl;
            for(const auto& p: matcher_.large_predecessors_)
            {
                std::cout << p.first+1 << ":" << p.second << " ";
            }
            std::cout << std::endl;
            std::cout << "Succs in new_state: " << std::endl;
            for(const auto& p: matcher_.large_successors_)
            {
                std::cout << p.first+1 << ":" << p.second << " ";
            }
            std::cout << std::endl;
        }

        std::unordered_set<VertexLargeType> get_class_nodes(NodeClassificationType_ cls, char code)
        {
            auto& matcher_ = *matcher_ptr;
            std::unordered_set<VertexLargeType> nodes;
            if (code == 'p')
            {
                for(const auto &p: matcher_.large_predecessors_)
                {
                    auto n = p.first;
                    if(matcher_.graph_large_classes_[n] == cls)
                    {
                        nodes.insert(n);
                    }
                }
            } else if (code == 's')
            {
                for(const auto &p: matcher_.large_successors_)
                {
                    auto n = p.first;
                    if(matcher_.graph_large_classes_[n] == cls)
                    {
                        nodes.insert(n);
                    }
                }
            } else if (code == 'v')
            {
                for(const VertexLargeType& n: matcher_.graph_large_vertices_)
                {
                    if (matcher_.large_predecessors_.find(n) == matcher_.large_predecessors_.end() &&
                        matcher_.large_successors_.find(n) == matcher_.large_successors_.end() &&
                        matcher_.core_large_.find(n) == matcher_.core_large_.end() &&
                        matcher_.graph_large_classes_[n] == cls)
                    {
                        nodes.insert(n);
                    }
                }
            } else {
                BOOST_ASSERT_MSG(false, "Invalid code for class nodes retrieval");
            }
            return nodes;
        }

        void restore()
        {
            auto& matcher_ = *matcher_ptr;
            if (v_large_ != graph_traits<GraphLarge_>::null_vertex() && 
                v_small_ != graph_traits<GraphSmall_>::null_vertex())
            {
                matcher_.core_large_.erase(v_large_);
                matcher_.core_small_.erase(v_small_);
            }
            std::cout << "Restore with depth: " << depth_ << std::endl;
            std::vector<VertexLargeType> nodes_to_remove;
            for(const auto &p: matcher_.large_predecessors_)
            {
                auto& n = p.first;
                if(p.second == depth_)
                {
                    nodes_to_remove.push_back(n);
                }
            }
            for(VertexLargeType node: nodes_to_remove)
            {
                matcher_.large_predecessors_.erase(node);
            }
            nodes_to_remove.clear();
            for(const auto &p: matcher_.large_successors_)
            {
                auto& n = p.first;
                if(p.second == depth_)
                {
                    nodes_to_remove.push_back(n);
                }
            }
            for(VertexLargeType node: nodes_to_remove)
            {
                matcher_.large_successors_.erase(node);
            }
            std::cout << "Preds after restore: " << std::endl;
            for(const auto& p: matcher_.large_predecessors_)
            {
                std::cout << p.first+1 << ":" << p.second << " ";
            }
            std::cout << std::endl;
            std::cout << "Succs after restore: " << std::endl;
            for(const auto& p: matcher_.large_successors_)
            {
                std::cout << p.first+1 << ":" << p.second << " ";
            }
            std::cout << std::endl;
        }

        matcher<GraphLarge_, GraphSmall_, NodeAttrPropertyMapLarge_, NodeAttrPropertyMapSmall_, NodeClassificationType_>* matcher_ptr;
        VertexLargeType v_large_;
        VertexSmallType v_small_;
        size_t depth_;
    }; // Class state

    // TODO: Comment that the TYPES of the property maps must be the same
    template < typename GraphLarge, typename GraphSmall, 
               typename NodeAttrPropertyMapLarge, typename NodeAttrPropertyMapSmall,
               typename NodeClassificationType >
    class matcher
    {   
        public:
        
        typedef typename property_traits<NodeAttrPropertyMapLarge>::value_type
            NodeAttrValueType;

        typedef typename graph_traits< GraphLarge >::vertex_descriptor
            VertexLargeType;
        
        typedef typename graph_traits< GraphLarge >::vertex_iterator
            VertexLargeIterator;

        typedef typename graph_traits< GraphSmall >::vertex_descriptor
            VertexSmallType;
        
        typedef typename graph_traits< GraphSmall >::vertex_iterator
            VertexSmallIterator;

        typedef typename graph_traits< GraphLarge >::edge_descriptor
            EdgeLargeType;
        
        typedef typename graph_traits< GraphSmall >::edge_descriptor
            EdgeSmallType;
        
        using NodePropertyTypeLarge = typename boost::property_traits<NodeAttrPropertyMapLarge>::value_type;
        using NodePropertyTypeSmall = typename boost::property_traits<NodeAttrPropertyMapSmall>::value_type;
        
        using LargeNodeClassificationFunc = std::function<NodeClassificationType(VertexLargeType, const GraphLarge&)>;
        using SmallNodeClassificationFunc = std::function<NodeClassificationType(VertexSmallType, const GraphSmall&)>;
        
        
        public:
        matcher(const GraphLarge& graph_large,
                const GraphSmall& graph_small,
                NodeAttrPropertyMapLarge node_attr_map_large,
                NodeAttrPropertyMapSmall node_attr_map_small,
                LargeNodeClassificationFunc large_node_classification_func = nullptr,
                SmallNodeClassificationFunc small_node_classification_func = nullptr
            )
        : graph_large_(graph_large)
        , graph_small_(graph_small)
        , node_attr_map_large_(node_attr_map_large)
        , node_attr_map_small_(node_attr_map_small)
        , large_node_classification_func_(large_node_classification_func)
        , small_node_classification_func_(small_node_classification_func)
        , state_(this)
        {
            
            BOOST_ASSERT_MSG((std::is_same<NodePropertyTypeLarge, NodePropertyTypeSmall>::value), 
                                "Node property types must be the same for both graphs");

            BOOST_ASSERT(num_vertices(graph_small) <= num_vertices(graph_large));
            BOOST_ASSERT(num_edges(graph_small) <= num_edges(graph_large));

            graph_small_vertices_.insert(vertices(graph_small).first,
                vertices(graph_small).second);
            graph_large_vertices_.insert(vertices(graph_large).first,
                vertices(graph_large).second);
            num_small_vertices_ = graph_small_vertices_.size();
            num_large_vertices_ = graph_large_vertices_.size();
            initialize();
        }

        
        void initialize()
        {
            // Initialize the matcher state, e.g., set up data structures
            // to track matched vertices, edges, etc.
            order_graph_small_vertices();
            classify_nodes();
            preprocess();
        }

        void match(std::vector<std::unordered_map<VertexLargeType, VertexSmallType>>& res)
        {
            std::cout << "Match called with" << std::endl << "{" << std::endl;
            for(const auto& p: core_large_)
            {
                std::cout << p.first+1 << ":" << p.second+1 << " ";
            }
            std::cout << "}" << std::endl;
            if(core_small_.size() == graph_small_vertices_.size())
            {
                std::cout << "Found the following mapping: " << std::endl;
                for(const auto& m: core_large_)
                {
                    std::cout << m.first+1 << ":" << m.second+1 << std::endl;
                }
                res.push_back(core_small_);
            } else {
                auto pairs = candidate_pairs();
                std::cout << "Candidate Pairs are: [";
                for(const auto& [v_large_next, v_small_next]: pairs)
                {
                    std::cout << "(" << v_large_next+1 << ", " << v_small_next+1 << "),";
                }
                std::cout << "]" << std::endl;
                for(const auto& [v_large_next, v_small_next]: candidate_pairs())
                {
                    if (syntactic_feasibility(v_large_next, v_small_next))
                    {
                        state<GraphLarge, GraphSmall, NodeAttrPropertyMapLarge, NodeAttrPropertyMapSmall, NodeClassificationType> new_state(this, v_large_next, v_small_next);
                        match(res);
                        new_state.restore();
                    } else {
                        std::cout << "NOT FEASIBLE" << std::endl;
                    }
                }
            }
            return;
        }

        std::vector<std::pair<VertexLargeType, VertexSmallType>> candidate_pairs()
        {
            size_t depth = core_small_.size();
            std::vector<std::pair<VertexLargeType, VertexSmallType>> pairs;
            VertexSmallType v_small_next;
            VertexLargeType v_large_next;
            if (state_.v_small_ != graph_traits<GraphSmall>::null_vertex() || depth < graph_small_vertices_.size())
            {
                if(state_.v_small_ == graph_traits<GraphSmall>::null_vertex())
                {
                    v_small_next = node_order_[depth];
                } else {
                    v_small_next = state_.v_small_;
                }
                NodeClassificationType v_small_next_class = graph_small_classes_[v_small_next];
                if (parents_[v_small_next] == NULL)
                {
                    for(const VertexLargeType& v_large_next: graph_large_vertices_)
                    {
                        if(core_large_.find(v_large_next) == core_large_.end() && graph_large_classes_[v_large_next] == v_small_next_class) {
                            pairs.emplace_back(v_large_next, v_small_next);
                        }
                    }
                } else {
                    VertexSmallType v_small_parent = parents_[v_small_next];
                    VertexLargeType v_large_parent = core_small_[v_small_parent];
                    if (boost::edge(v_small_next, v_small_parent, graph_small_).second && !boost::edge(v_small_parent, v_small_next, graph_small_).second)
                    {
                        auto in_edge_it = boost::in_edges(v_large_parent, graph_large_);
                        for(auto it = in_edge_it.first; it != in_edge_it.second; ++it){
                            auto e = *it;
                            VertexLargeType v_large_next = boost::source(e, graph_large_);
                            if(core_large_.find(v_large_next) == core_large_.end() && graph_large_classes_[v_large_next] == v_small_next_class) {
                                pairs.emplace_back(v_large_next, v_small_next);
                            }
                        }
                    } else if (boost::edge(v_small_parent, v_small_next, graph_small_).second && !boost::edge(v_small_next, v_small_parent, graph_small_).second)
                    {
                        auto out_edge_it = boost::out_edges(v_large_parent, graph_large_);
                        for(auto it = out_edge_it.first; it != out_edge_it.second; ++it)
                        {
                            auto e = *it;
                            VertexLargeType v_large_next = boost::target(e, graph_large_);
                            if (core_large_.find(v_large_next) == core_large_.end() && graph_large_classes_[v_large_next] == v_small_next_class)
                            {
                                pairs.emplace_back(v_large_next, v_small_next);
                            }
                        }
                    } else if (boost::edge(v_small_parent, v_small_next, graph_small_).second && boost::edge(v_small_next, v_small_parent, graph_small_).second)
                    {
                        auto in_edge_it = boost::in_edges(v_large_parent, graph_large_);
                        for(auto it = in_edge_it.first; it != in_edge_it.second; ++it)
                        {
                            auto e = *it;
                            VertexLargeType v_large_next = boost::source(e, graph_large_);
                            if (core_large_.find(v_large_next) == core_large_.end() && boost::edge(v_large_parent, v_large_next, graph_large_).second && graph_large_classes_[v_large_next] == v_small_next_class)
                            {
                                pairs.emplace_back(v_large_next, v_small_next);
                            }
                        }
                    }
                }
            }
            return pairs;
        }

        bool syntactic_feasibility(VertexLargeType v_large, VertexSmallType v_small)
        {
            if (graph_small_classes_[v_small] != graph_large_classes_[v_large])
            {
                return false;
            }
            return fc(v_large, v_small) && fla1(v_large, v_small) && fla2(v_large, v_small);
        }

        bool fc(VertexLargeType v_large, VertexSmallType v_small)
        {
            auto out_edge_it = boost::out_edges(v_small, graph_small_);
            for(auto it = out_edge_it.first; it != out_edge_it.second; ++it)
            {
                auto e = *it;
                VertexSmallType target = boost::target(e, graph_small_);
                if(core_small_.find(target) != core_small_.end())
                {
                    VertexLargeType mapped_node = core_small_[target];
                    std::pair<EdgeLargeType, bool> edge = boost::edge(v_large, mapped_node, graph_large_);
                    if (!edge.second)
                    {
                        std::cout << "FC value for (" << v_large+1 << ", " << v_small+1 << ") pair is: False" << std::endl;
                        return false;
                    }
                }
            }
            auto in_edge_it = boost::in_edges(v_small, graph_small_);
            for(auto it = in_edge_it.first; it != in_edge_it.second; ++it)
            {
                auto e = *it;
                VertexSmallType source = boost::source(e, graph_small_);
                if(core_small_.find(source) != core_small_.end())
                {
                    VertexLargeType mapped_node = core_small_[source];
                    std::pair<EdgeLargeType, bool> edge = boost::edge(mapped_node, v_large, graph_large_);
                    if (!edge.second)
                    {
                        std::cout << "FC value for (" << v_large+1 << ", " << v_small+1 << ") pair is: False" << std::endl;
                        return false;
                    }
                }
            }
            out_edge_it = boost::out_edges(v_large, graph_large_);
            for(auto it = out_edge_it.first; it != out_edge_it.second; ++it)
            {
                auto e = *it;
                VertexLargeType target = boost::target(e, graph_large_);
                if(core_large_.find(target) != core_large_.end())
                {
                    VertexSmallType mapped_node = core_large_[target];
                    std::pair<EdgeSmallType, bool> edge = boost::edge(v_small, mapped_node, graph_small_);
                    if (!edge.second)
                    {
                        std::cout << "FC value for (" << v_large+1 << ", " << v_small+1 << ") pair is: False" << std::endl;
                        return false;
                    }
                }
            }
            in_edge_it = boost::in_edges(v_large, graph_large_);
            for(auto it = in_edge_it.first; it != in_edge_it.second; ++it)
            {
                auto e = *it;
                VertexLargeType source = boost::source(e, graph_large_);
                if(core_large_.find(source) != core_large_.end())
                {
                    VertexSmallType mapped_node = core_large_[source];
                    std::pair<EdgeSmallType, bool> edge = boost::edge(mapped_node, v_small, graph_small_);
                    if (!edge.second)
                    {
                        std::cout << "FC value for (" << v_large+1 << ", " << v_small+1 << ") pair is: False" << std::endl;
                        return false;
                    }
                }
            }
            
            std::cout << "FC value for (" << v_large+1 << ", " << v_small+1 << ") pair is: True" << std::endl;
            return true;
        }

        bool fla1(VertexLargeType v_large, VertexSmallType v_small)
        {
            auto curr_depth = core_small_.size();
            std::bitset<num_small_vertices_> all_small_predecessors;
            auto in_edge_it = boost::in_edges(v_small, graph_small_);
            for(auto it = in_edge_it.first; it != in_edge_it.second; ++it)
            {
                auto e = *it;
                VertexSmallType pred = boost::source(e, graph_small_);
                all_small_predecessors.set(pred);
            }
            std::bitset<num_large_vertices_> all_large_predecessors;
            auto large_in_edge_it = boost::in_edges(v_large, graph_large_);
            for(auto it = large_in_edge_it.first; it != large_in_edge_it.second; ++it)
            {
                auto e = *it;
                VertexLargeType pred = boost::source(e, graph_large_);
                all_large_predecessors.set(pred);
            }
            std::bitset<num_small_vertices_> all_small_successors;
            auto out_edge_it = boost::out_edges(v_small, graph_small_);
            for(auto it = out_edge_it.first; it != out_edge_it.second; ++it)
            {
                auto e = *it;
                VertexSmallType succ = boost::target(e, graph_small_);
                all_small_successors.set(succ);
            }
            std::bitset<num_large_vertices_> all_large_successors;
            auto large_out_edge_it = boost::out_edges(v_large, graph_large_);
            for(auto it = large_out_edge_it.first; it != large_out_edge_it.second; ++it)
            {
                auto e = *it;
                VertexLargeType succ = boost::target(e, graph_large_);
                all_large_successors.set(succ);
            }
            for(auto cls: all_classes_)
            {
                std::bitset<num_small_vertices_> small_p_cls_nodes;

                std::unordered_set<VertexSmallType> small_p_cls_nodes;
                std::set_intersection(
                    p_small_sets_[curr_depth].begin(), p_small_sets_[curr_depth].end(),
                    graph_small_class_nodes_[cls].begin(), graph_small_class_nodes_[cls].end(),
                    std::inserter(small_p_cls_nodes, small_p_cls_nodes.begin())
                );
                std::unordered_set<VertexSmallType> left_set;
                std::set_intersection(
                    small_p_cls_nodes.begin(), small_p_cls_nodes.end(),
                    all_small_predecessors.begin(), all_small_predecessors.end(),
                    std::inserter(left_set, left_set.begin())
                );
                std::unordered_set<VertexLargeType> large_p_cls_nodes = state_.get_class_nodes(cls, 'p');
                std::unordered_set<VertexLargeType> right_set;
                std::set_intersection(
                    large_p_cls_nodes.begin(), large_p_cls_nodes.end(),
                    all_large_predecessors.begin(), all_large_predecessors.end(),
                    std::inserter(right_set, right_set.begin())
                );
                if (left_set.size() > right_set.size())
                {
                    std::cout << "FLA1 value for (" << v_large+1 << ", " << v_small+1 << ") pair is: False." << std::endl;
                    return false;
                }
                std::unordered_set<VertexSmallType> small_s_cls_nodes;
                std::set_intersection(
                    s_small_sets_[curr_depth].begin(), s_small_sets_[curr_depth].end(),
                    graph_small_class_nodes_[cls].begin(), graph_small_class_nodes_[cls].end(),
                    std::inserter(small_s_cls_nodes, small_s_cls_nodes.begin())
                );
                left_set.clear();
                std::set_intersection(
                    small_s_cls_nodes.begin(), small_s_cls_nodes.end(),
                    all_small_predecessors.begin(), all_small_predecessors.end(),
                    std::inserter(left_set, left_set.begin())
                );
                std::unordered_set<VertexSmallType> large_s_cls_nodes = state_.get_class_nodes(cls, 's');
                right_set.clear();
                std::set_intersection(
                    large_s_cls_nodes.begin(), large_s_cls_nodes.end(),
                    all_large_predecessors.begin(), all_large_predecessors.end(),
                    std::inserter(right_set, right_set.begin())
                );
                if (left_set.size() > right_set.size())
                {
                    std::cout << "FLA1 value for (" << v_large+1 << ", " << v_small+1 << ") pair is: False." << std::endl;
                    return false;
                }
                left_set.clear();
                std::set_intersection(
                    small_p_cls_nodes.begin(), small_p_cls_nodes.end(),
                    all_small_successors.begin(), all_small_successors.end(),
                    std::inserter(left_set, left_set.begin())
                );
                right_set.clear();
                std::set_intersection(
                    large_p_cls_nodes.begin(), large_p_cls_nodes.end(),
                    all_large_successors.begin(), all_large_successors.end(),
                    std::inserter(right_set, right_set.begin())
                );
                if (left_set.size() > right_set.size())
                {
                    std::cout << "FLA1 value for (" << v_large+1 << ", " << v_small+1 << ") pair is: False." << std::endl;
                    return false;
                }
                left_set.clear();
                std::set_intersection(
                    small_s_cls_nodes.begin(), small_s_cls_nodes.end(),
                    all_small_successors.begin(), all_small_successors.end(),
                    std::inserter(left_set, left_set.begin())
                );
                right_set.clear();
                std::set_intersection(
                    large_s_cls_nodes.begin(), large_s_cls_nodes.end(),
                    all_large_successors.begin(), all_large_successors.end(),
                    std::inserter(right_set, right_set.begin())
                );
                if (left_set.size() > right_set.size())
                {
                    std::cout << "FLA1 value for (" << v_large+1 << ", " << v_small+1 << ") pair is: False." << std::endl;
                    return false;
                }
            }
            std::cout << "FLA1 value for (" << v_large+1 << ", " << v_small+1 << ") pair is: True." << std::endl;
            return true;
            /*
            auto curr_depth = core_small_.size();
            std::unordered_set<VertexSmallType> all_small_predecessors;
            auto in_edge_it = boost::in_edges(v_small, graph_small_);
            for(auto it = in_edge_it.first; it != in_edge_it.second; ++it)
            {
                auto e = *it;
                VertexSmallType pred = boost::source(e, graph_small_);
                all_small_predecessors.insert(pred);
            }
            std::unordered_set<VertexLargeType> all_large_predecessors;
            auto large_in_edge_it = boost::in_edges(v_large, graph_large_);
            for(auto it = large_in_edge_it.first; it != large_in_edge_it.second; ++it)
            {
                auto e = *it;
                VertexLargeType pred = boost::source(e, graph_large_);
                all_large_predecessors.insert(pred);
            }
            std::unordered_set<VertexSmallType> all_small_successors;
            auto out_edge_it = boost::out_edges(v_small, graph_small_);
            for(auto it = out_edge_it.first; it != out_edge_it.second; ++it)
            {
                auto e = *it;
                VertexSmallType succ = boost::target(e, graph_small_);
                all_small_successors.insert(succ);
            }
            std::unordered_set<VertexLargeType> all_large_successors;
            auto large_out_edge_it = boost::out_edges(v_large, graph_large_);
            for(auto it = large_out_edge_it.first; it != large_out_edge_it.second; ++it)
            {
                auto e = *it;
                VertexLargeType succ = boost::target(e, graph_large_);
                all_large_successors.insert(succ);
            }
            for(auto cls: all_classes_)
            {
                std::unordered_set<VertexSmallType> small_p_cls_nodes;
                std::set_intersection(
                    p_small_sets_[curr_depth].begin(), p_small_sets_[curr_depth].end(),
                    graph_small_class_nodes_[cls].begin(), graph_small_class_nodes_[cls].end(),
                    std::inserter(small_p_cls_nodes, small_p_cls_nodes.begin())
                );
                std::unordered_set<VertexSmallType> left_set;
                std::set_intersection(
                    small_p_cls_nodes.begin(), small_p_cls_nodes.end(),
                    all_small_predecessors.begin(), all_small_predecessors.end(),
                    std::inserter(left_set, left_set.begin())
                );
                std::unordered_set<VertexLargeType> large_p_cls_nodes = state_.get_class_nodes(cls, 'p');
                std::unordered_set<VertexLargeType> right_set;
                std::set_intersection(
                    large_p_cls_nodes.begin(), large_p_cls_nodes.end(),
                    all_large_predecessors.begin(), all_large_predecessors.end(),
                    std::inserter(right_set, right_set.begin())
                );
                if (left_set.size() > right_set.size())
                {
                    std::cout << "FLA1 value for (" << v_large+1 << ", " << v_small+1 << ") pair is: False." << std::endl;
                    return false;
                }
                std::unordered_set<VertexSmallType> small_s_cls_nodes;
                std::set_intersection(
                    s_small_sets_[curr_depth].begin(), s_small_sets_[curr_depth].end(),
                    graph_small_class_nodes_[cls].begin(), graph_small_class_nodes_[cls].end(),
                    std::inserter(small_s_cls_nodes, small_s_cls_nodes.begin())
                );
                left_set.clear();
                std::set_intersection(
                    small_s_cls_nodes.begin(), small_s_cls_nodes.end(),
                    all_small_predecessors.begin(), all_small_predecessors.end(),
                    std::inserter(left_set, left_set.begin())
                );
                std::unordered_set<VertexSmallType> large_s_cls_nodes = state_.get_class_nodes(cls, 's');
                right_set.clear();
                std::set_intersection(
                    large_s_cls_nodes.begin(), large_s_cls_nodes.end(),
                    all_large_predecessors.begin(), all_large_predecessors.end(),
                    std::inserter(right_set, right_set.begin())
                );
                if (left_set.size() > right_set.size())
                {
                    std::cout << "FLA1 value for (" << v_large+1 << ", " << v_small+1 << ") pair is: False." << std::endl;
                    return false;
                }
                left_set.clear();
                std::set_intersection(
                    small_p_cls_nodes.begin(), small_p_cls_nodes.end(),
                    all_small_successors.begin(), all_small_successors.end(),
                    std::inserter(left_set, left_set.begin())
                );
                right_set.clear();
                std::set_intersection(
                    large_p_cls_nodes.begin(), large_p_cls_nodes.end(),
                    all_large_successors.begin(), all_large_successors.end(),
                    std::inserter(right_set, right_set.begin())
                );
                if (left_set.size() > right_set.size())
                {
                    std::cout << "FLA1 value for (" << v_large+1 << ", " << v_small+1 << ") pair is: False." << std::endl;
                    return false;
                }
                left_set.clear();
                std::set_intersection(
                    small_s_cls_nodes.begin(), small_s_cls_nodes.end(),
                    all_small_successors.begin(), all_small_successors.end(),
                    std::inserter(left_set, left_set.begin())
                );
                right_set.clear();
                std::set_intersection(
                    large_s_cls_nodes.begin(), large_s_cls_nodes.end(),
                    all_large_successors.begin(), all_large_successors.end(),
                    std::inserter(right_set, right_set.begin())
                );
                if (left_set.size() > right_set.size())
                {
                    std::cout << "FLA1 value for (" << v_large+1 << ", " << v_small+1 << ") pair is: False." << std::endl;
                    return false;
                }
            }
            std::cout << "FLA1 value for (" << v_large+1 << ", " << v_small+1 << ") pair is: True." << std::endl;
            return true;
            */
        }

        bool fla2(VertexLargeType v_large, VertexSmallType v_small)
        {
            auto curr_depth = core_small_.size();
            std::unordered_set<VertexSmallType> all_small_predecessors;
            auto in_edge_it = boost::in_edges(v_small, graph_small_);
            for(auto it = in_edge_it.first; it != in_edge_it.second; ++it)
            {
                auto e = *it;
                VertexSmallType source = boost::source(e, graph_small_);
                all_small_predecessors.insert(source);
            }

            std::unordered_set<VertexLargeType> all_large_predecessors;
            auto large_in_edge_it = boost::in_edges(v_large, graph_large_);
            for(auto it = large_in_edge_it.first; it != large_in_edge_it.second; ++it)
            {
                auto e = *it;
                VertexLargeType source = boost::source(e, graph_large_);
                all_large_predecessors.insert(source);
            }

            std::unordered_set<VertexSmallType> all_small_successors;
            auto out_edge_it = boost::out_edges(v_small, graph_small_);
            for(auto it = out_edge_it.first; it != out_edge_it.second; ++it)
            {
                auto e = *it;
                VertexSmallType target = boost::target(e, graph_small_);
                all_small_successors.insert(target);
            }
            std::unordered_set<VertexLargeType> all_large_successors;
            auto large_out_edge_it = boost::out_edges(v_large, graph_large_);
            for(auto it = large_out_edge_it.first; it != large_out_edge_it.second; ++it)
            {
                auto e = *it;
                VertexLargeType target = boost::target(e, graph_large_);
                all_large_successors.insert(target);
            }
            for(const auto& cls: all_classes_)
            {
                std::unordered_set<VertexSmallType> v_small_cls_nodes;
                std::set_intersection(
                    v_small_sets_[curr_depth].begin(), v_small_sets_[curr_depth].end(),
                    graph_small_class_nodes_[cls].begin(), graph_small_class_nodes_[cls].end(),
                    std::inserter(v_small_cls_nodes, v_small_cls_nodes.begin()));
                std::unordered_set<VertexSmallType> temp_set;
                std::set_intersection(
                    all_small_predecessors.begin(), all_small_predecessors.end(),
                    v_small_cls_nodes.begin(), v_small_cls_nodes.end(),
                    std::inserter(temp_set, temp_set.begin()));
                auto left_cardinality = temp_set.size();
                std::unordered_set<VertexLargeType> v_large_cls_nodes = state_.get_class_nodes(cls,'v');
                std::unordered_set<VertexLargeType> temp_set2;
                std::set_intersection(
                    all_large_predecessors.begin(), all_large_predecessors.end(),
                    v_large_cls_nodes.begin(), v_large_cls_nodes.end(),
                    std::inserter(temp_set2, temp_set2.begin()));
                auto right_cardinality = temp_set2.size();
                if (left_cardinality > right_cardinality)
                {
                    return false;
                }
                temp_set.clear();
                std::set_intersection(
                    v_small_cls_nodes.begin(), v_small_cls_nodes.end(),
                    all_small_successors.begin(), all_small_successors.end(),
                    std::inserter(temp_set, temp_set.begin()));
                left_cardinality = temp_set.size();
                temp_set2.clear();
                std::set_intersection(
                    v_large_cls_nodes.begin(), v_large_cls_nodes.end(),
                    all_large_successors.begin(), all_large_successors.end(),
                    std::inserter(temp_set2, temp_set2.begin()));
                right_cardinality = temp_set2.size();
                if (left_cardinality > right_cardinality)
                {
                    return false;
                }
            }
            return true;
        }
        
        void preprocess()
        {
            size_t max_depth = node_order_.size();
            core_small_sets_.assign(max_depth+1, std::unordered_set<VertexSmallType>());
            p_small_sets_.assign(max_depth+1, std::unordered_set<VertexSmallType>());
            s_small_sets_.assign(max_depth+1, std::unordered_set<VertexSmallType>());
            v_small_sets_.assign(max_depth+1, std::unordered_set<VertexSmallType>());

            auto p_small_cls_sets_map_ = std::unordered_map<NodeClassificationType,std::vector<std::unordered_set<VertexSmallType>>>();
            auto s_small_cls_sets_map_ = std::unordered_map<NodeClassificationType,std::vector<std::unordered_set<VertexSmallType>>>();
            auto v_small_cls_sets_map_ = std::unordered_map<NodeClassificationType,std::vector<std::unordered_set<VertexSmallType>>>();

            for(const auto& cls: all_classes_)
            {
                p_small_cls_sets_map_[cls].assign(max_depth+1, std::unordered_set<VertexSmallType>());
                s_small_cls_sets_map_[cls].assign(max_depth+1, std::unordered_set<VertexSmallType>());
                v_small_cls_sets_map_[cls].assign(max_depth+1, std::unordered_set<VertexSmallType>());
            }
            v_small_sets_[0] = graph_small_vertices_;
            for(size_t depth=1; depth <= max_depth; ++depth)
            {
                auto mapped_nodes = std::unordered_set<VertexSmallType>();
                mapped_nodes.insert(node_order_.begin(), node_order_.begin() + depth);
                core_small_sets_[depth] = mapped_nodes;
                std::unordered_set<VertexSmallType> all_predecessors;
                std::unordered_set<VertexSmallType> all_successors;
                for(const auto& v: mapped_nodes)
                {
                    auto in_edges = boost::in_edges(v, graph_small_);
                    for(auto edge_it = in_edges.first; edge_it != in_edges.second; ++edge_it)
                    {
                        VertexSmallType source = boost::source(*edge_it, graph_small_);
                        all_predecessors.insert(source);
                    }
                    auto out_edges = boost::out_edges(v, graph_small_);
                    for(auto edge_it = out_edges.first; edge_it != out_edges.second; ++edge_it)
                    {
                        VertexSmallType target = boost::target(*edge_it, graph_small_);
                        all_successors.insert(target);
                    }
                }
                for(const auto& v: graph_small_vertices_)
                {
                    if(mapped_nodes.find(v) == mapped_nodes.end() && all_predecessors.find(v) != all_predecessors.end())
                    {
                        p_small_sets_[depth].insert(v);
                    }
                    if(mapped_nodes.find(v) == mapped_nodes.end() && all_successors.find(v) != all_successors.end())
                    {
                        s_small_sets_[depth].insert(v);
                    }
                }
                for(const auto& v: graph_small_vertices_)
                {
                    if(mapped_nodes.find(v) == mapped_nodes.end() && all_predecessors.find(v) == all_predecessors.end() && all_successors.find(v) == all_successors.end())
                    {
                        v_small_sets_[depth].insert(v);
                    }
                }
            }
            for(const VertexSmallType& v: graph_small_vertices_)
            {
                parents_[v] = NULL;
            }
            for(size_t depth=0; depth <= max_depth; ++depth)
            {
                std::unordered_set<VertexSmallType> union_set;
                std::set_union(
                    p_small_sets_[depth].begin(), p_small_sets_[depth].end(),
                    s_small_sets_[depth].begin(), s_small_sets_[depth].end(),
                    std::inserter(union_set, union_set.begin()));
                for(const VertexSmallType& v: union_set)
                {
                    auto cls = graph_small_classes_[v];
                    if (p_small_sets_[depth].find(v) != p_small_sets_[depth].end())
                    {
                        if(p_small_cls_sets_map_[cls][depth].find(v) == p_small_cls_sets_map_[cls][depth].end())
                        {
                            p_small_cls_sets_map_[cls][depth].insert(v);
                            if(parents_[v] == NULL)
                            {
                                parents_[v] = node_order_[depth-1];
                            }
                        }
                    } else {
                        if(s_small_cls_sets_map_[cls][depth].find(v) == s_small_cls_sets_map_[cls][depth].end())
                        {
                            s_small_cls_sets_map_[cls][depth].insert(v);
                            if(parents_[v] == NULL)
                            {
                                parents_[v] = node_order_[depth-1];
                            }
                        }
                    }
                }
            }
        }

        void classify_nodes()
        {
            std::pair<VertexLargeIterator, VertexLargeIterator> vp = boost::vertices(graph_large_);
            for(VertexLargeIterator it = vp.first; it != vp.second; ++it)
            {
                // TODO: The default_node_class should be a parameter
                graph_large_classes_[*it] = NodeClassificationType();
            }
            std::pair<VertexSmallIterator, VertexSmallIterator> vp_small = boost::vertices(graph_small_);
            for(VertexSmallIterator it = vp_small.first; it != vp_small.second; ++it)
            {
                graph_small_classes_[*it] = NodeClassificationType();  
            }
            if (large_node_classification_func_ != nullptr && small_node_classification_func_ != nullptr) 
            {
                vp = boost::vertices(graph_large_);
                for(VertexLargeIterator it = vp.first; it != vp.second; ++it)
                {
                    VertexLargeType v = *it;
                    NodeClassificationType label = large_node_classification_func_(v, graph_large_);
                    graph_large_classes_[v] = label;
                    graph_large_class_nodes_[label].insert(v);
                    all_classes_.insert(label);
                }
                vp_small = boost::vertices(graph_small_);
                for(VertexSmallIterator it = vp_small.first; it != vp_small.second; ++it)
                {
                    VertexSmallType v = *it;
                    NodeClassificationType label = small_node_classification_func_(v, graph_small_);
                    graph_small_classes_[v] = label;
                    graph_small_class_nodes_[label].insert(v);
                    all_classes_.insert(label);
                }
            } else {
                vp = boost::vertices(graph_large_);
                for(VertexLargeIterator it = vp.first; it != vp.second; ++it)
                {
                    graph_large_class_nodes_[NodeClassificationType()].insert(*it);
                }
                vp_small = boost::vertices(graph_small_);
                for(VertexSmallIterator it = vp_small.first; it != vp_small.second; ++it)
                {
                    graph_small_class_nodes_[NodeClassificationType()].insert(*it); 
                }
                all_classes_.insert(NodeClassificationType());
            }

        }

        void print_node_order()
        {
            std::cout << "Node order: ";
            for (const auto& node : node_order_) {
                std::cout << node << " ";
            }
            std::cout << std::endl;
        }

        void order_graph_small_vertices()
        {
            std::unordered_map< VertexSmallType, double > node_probabilities = compute_vertex_probabilities();
            std::unordered_map< VertexSmallType, double > dM_values;
            std::unordered_map< VertexSmallType, int > nodes_total_degree;
            std::pair<VertexSmallIterator, VertexSmallIterator> vp = boost::vertices(graph_small_);
            for (VertexSmallIterator it = vp.first; it != vp.second; ++it)
            {
                VertexSmallType v = *it;
                dM_values[v] = 0.0;
                nodes_total_degree[v] = boost::in_degree(v, graph_small_) + boost::out_degree(v, graph_small_);
            }
            std::vector< VertexSmallType > node_order;
            node_order.reserve(boost::num_vertices(graph_small_));

            std::vector< VertexSmallType > remaining_nodes_candidates;
            for (auto const& [node, val] : dM_values) {
                remaining_nodes_candidates.push_back(node);
            }
            while(node_order.size() < boost::num_vertices(graph_small_))
            {
                VertexSmallType next_node;
                if (node_order.empty())
                {
                    // At the beginning, only the node_probabilities matter
                    next_node = *std::min_element(
                    remaining_nodes_candidates.begin(), remaining_nodes_candidates.end(),
                        [&](VertexSmallType a, VertexSmallType b) {
                            return node_probabilities[a] < node_probabilities[b];
                        }
                    );
                }
                else 
                {
                    std::vector<VertexSmallType> current_candidates = remaining_nodes_candidates;
                    std::sort(current_candidates.begin(), current_candidates.end(),
                        [&](VertexSmallType a, VertexSmallType b) {
                            if (dM_values[a] != dM_values[b])
                            {
                                return dM_values[a] > dM_values[b];
                            }
                            if (node_probabilities[a] != node_probabilities[b])
                            {
                                return node_probabilities[a] < node_probabilities[b];
                            }
                            if (nodes_total_degree[a] != nodes_total_degree[b])
                            {
                                return nodes_total_degree[a] > nodes_total_degree[b];
                            }
                            return false; // Random tie-breaking.
                        });
                    next_node = current_candidates[0];
                }
                node_order.push_back(next_node);
                remaining_nodes_candidates.erase(
                    std::remove(remaining_nodes_candidates.begin(), remaining_nodes_candidates.end(), next_node),
                    remaining_nodes_candidates.end()
                );
                dM_values.erase(next_node);
                auto out_edges = boost::out_edges(next_node, graph_small_);
                for(auto edge_it = out_edges.first; edge_it != out_edges.second; ++edge_it)
                {
                    VertexSmallType target = boost::target(*edge_it, graph_small_);
                    if (dM_values.find(target) != dM_values.end())
                    {
                        dM_values[target] += 1;
                    }
                }
                auto in_edges = boost::in_edges(next_node, graph_small_);
                for(auto edge_it = in_edges.first; edge_it != in_edges.second; ++edge_it)
                {
                    VertexSmallType source = boost::source(*edge_it, graph_small_);
                    if (dM_values.find(source) != dM_values.end())
                    {
                        dM_values[source] += 1;
                    }
                }
            }
            this->node_order_ = node_order;
        }

        std::unordered_map< VertexSmallType, double > compute_vertex_probabilities()
        {
            typedef typename graph_traits< GraphLarge >::vertices_size_type large_num_vertices_type;
            
            typedef typename graph_traits< GraphSmall >::degree_size_type DegreeSizeType;

            std::unordered_map< NodeAttrValueType, int > label_counts_ = label_counts();
            std::vector<int> cumulative_in_degrees = cumulative_degrees(true);
            std::vector<int> cumulative_out_degrees = cumulative_degrees(false);
            std::unordered_map< VertexSmallType, double > probabilities;
            large_num_vertices_type num_large_vertices = num_vertices(graph_large_);
            std::pair<VertexSmallIterator, VertexSmallIterator> vp = boost::vertices(graph_small_);

            for (VertexSmallIterator it = vp.first; it != vp.second; ++it)
            {
                VertexSmallType v = *it;
                double label_probability = 1.0;
                NodeAttrValueType label = node_attr_map_small_[v];
                if (label_counts_.find(label) == label_counts_.end())
                {
                    label_probability = 0.0; // No such label in the large graph
                    probabilities[v] = 0.0;
                    continue;
                }
                else
                {
                    int label_count = label_counts_[label];
                    label_probability *= static_cast<double>(label_count) / num_large_vertices;
                }
                DegreeSizeType in_degree_v = boost::in_degree(v, graph_small_);
                double in_degree_probability = 0.0;
                if (in_degree_v < cumulative_in_degrees.size())
                {
                    in_degree_probability = static_cast<double>(cumulative_in_degrees[in_degree_v]) / num_large_vertices;
                }
                else
                {
                    in_degree_probability = 0.0; // No such in-degree in the large graph
                    probabilities[v] = 0.0;
                    continue;
                }
                DegreeSizeType out_degree_v = boost::out_degree(v, graph_small_);
                double out_degree_probability = 0.0;
                if (out_degree_v < cumulative_out_degrees.size())
                {
                    out_degree_probability = static_cast<double>(cumulative_out_degrees[out_degree_v]) / num_large_vertices;
                }
                else
                {
                    out_degree_probability = 0.0; // No such out-degree in the large graph
                    probabilities[v] = 0.0;
                    continue;
                }
                probabilities[v] = label_probability * in_degree_probability * out_degree_probability;
            }
            return probabilities;
            
        }

        std::unordered_map< NodeAttrValueType, int > label_counts() const
        {   
            std::unordered_map< NodeAttrValueType, int > label_counts;
            auto vp = boost::vertices(graph_large_);
            for(VertexLargeIterator it = vp.first; it != vp.second; ++it)
            {
                VertexLargeType v = *it;
                NodeAttrValueType label = get(node_attr_map_large_, v);
                label_counts[label]++;
            }
            return label_counts;
        }


        std::vector<int> cumulative_degrees(bool is_in_degree)
        {
            typedef typename graph_traits< GraphLarge >::degree_size_type DegreeSizeType;
            std::vector<DegreeSizeType> degrees;
            degrees.reserve(boost::num_vertices(graph_large_));
            std::pair<VertexLargeIterator, VertexLargeIterator> vp = boost::vertices(graph_large_);
            for (VertexLargeIterator it = vp.first; it != vp.second; ++it) {
                VertexLargeType v = *it;
                if (is_in_degree) {
                    degrees.push_back(boost::in_degree(v, graph_large_));
                } else {
                    degrees.push_back(boost::out_degree(v, graph_large_));
                }
            }
            DegreeSizeType max_degree = 0;
            if (!degrees.empty()) {
                // Using std::max_element to find the maximum degree
                max_degree = *std::max_element(degrees.begin(), degrees.end());
            }
            std::vector<int> hist(max_degree + 1, 0);
            for (DegreeSizeType d : degrees) {
                hist[d]++;
            }
            std::vector<int> ge(max_degree + 1, 0);
            int running_sum = 0;
            for (int d = max_degree; d >= 0; --d) {
                running_sum += hist[d];
                ge[d] = running_sum;
            }
            return ge;
        }

        // TODO: Make the following private

        const GraphSmall& graph_small_;
        const GraphLarge& graph_large_;
        std::unordered_set< VertexSmallType > graph_small_vertices_;
        std::unordered_set< VertexLargeType > graph_large_vertices_;
        std::unordered_map< VertexSmallType, VertexLargeType > core_large_;
        std::unordered_map< VertexLargeType, VertexSmallType > core_small_;
        state<GraphLarge, GraphSmall, NodeAttrPropertyMapLarge, NodeAttrPropertyMapSmall, NodeClassificationType> state_;
        NodeAttrPropertyMapLarge node_attr_map_large_;
        NodeAttrPropertyMapSmall node_attr_map_small_;
        std::vector<VertexSmallType> node_order_;
        std::unordered_map< VertexLargeType, NodeClassificationType > graph_large_classes_;
        std::unordered_map< VertexSmallType, NodeClassificationType > graph_small_classes_;
        std::unordered_map< NodeClassificationType, std::unordered_set< VertexLargeType > > graph_large_class_nodes_;
        std::unordered_map< NodeClassificationType, std::unordered_set< VertexSmallType > > graph_small_class_nodes_;
        std::unordered_set< NodeClassificationType > all_classes_;
        LargeNodeClassificationFunc large_node_classification_func_;
        SmallNodeClassificationFunc small_node_classification_func_;
        std::vector<std::unordered_set<VertexSmallType>> core_small_sets_;
        std::vector<std::unordered_set<VertexSmallType>> p_small_sets_;
        std::vector<std::unordered_set<VertexSmallType>> s_small_sets_;
        std::vector<std::unordered_set<VertexSmallType>> v_small_sets_;
        std::unordered_map<VertexSmallType, VertexSmallType> parents_;
        std::unordered_map<VertexLargeType, int> large_predecessors_;
        std::unordered_map<VertexLargeType, int> large_successors_;
        uint64_t num_small_vertices_;
        uint64_t num_large_vertices_;

    }; // Class matcher
    

} // namespace detail

} // namespace boost


#ifdef BOOST_ISO_INCLUDED_ITER_MACROS
#undef BOOST_ISO_INCLUDED_ITER_MACROS
#include <boost/graph/iteration_macros_undef.hpp>
#endif

#endif // BOOST_VF2_SUB_GRAPH_ISO_HPP