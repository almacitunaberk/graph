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
#include <boost/dynamic_bitset.hpp>
#include <memory>

#ifndef BOOST_GRAPH_ITERATION_MACROS_HPP
#define BOOST_ISO_INCLUDED_ITER_MACROS // local macro, see bottom of file
#include <boost/graph/iteration_macros.hpp>
#endif

namespace std
{
    template<typename T, typename... Args>
    std::unique_ptr<T> make_unique(Args&&... args) {
        return std::unique_ptr<T>(new T(std::forward<Args>(args)...));
    }
}

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
    class vf3_state
    {
        typedef typename graph_traits<GraphLarge_>::vertex_descriptor VertexLargeType;
        typedef typename graph_traits<GraphSmall_>::vertex_descriptor VertexSmallType;

        public:
        vf3_state(): matcher_ptr(nullptr) {}
        vf3_state(matcher<GraphLarge_, GraphSmall_, NodeAttrPropertyMapLarge_, NodeAttrPropertyMapSmall_, NodeClassificationType_>* m, 
                VertexLargeType v_large = graph_traits<GraphLarge_>::null_vertex(), VertexSmallType v_small = graph_traits<GraphSmall_>::null_vertex())
        : v_large_(v_large)
        , v_small_(v_small)
        , matcher_ptr(m)
        {
            ////std::cout << "State init started" << std::endl;
            auto& matcher_ = *matcher_ptr;
            depth_ = matcher_.core_large_.size();
            if (v_large_ != graph_traits<GraphLarge_>::null_vertex() && 
                v_small_ != graph_traits<GraphSmall_>::null_vertex())
            {
                matcher_.core_large_[v_large_] = v_small_;
                matcher_.core_small_[v_small_] = v_large_;
                depth_ = matcher_.core_large_.size();
                auto v_large_index = matcher_.large_vertices_indices_[v_large_];
                if (!matcher_.large_predecessors_[v_large_index])
                {
                    matcher_.large_predecessors_.set(v_large_index);
                    new_predecessors_.push_back(v_large_index);
                }
                if (!matcher_.large_successors_[v_large_index])
                {
                    matcher_.large_successors_.set(v_large_index);
                    new_successors_.push_back(v_large_index);
                }
                auto in_edge_it = boost::in_edges(v_large_, matcher_.graph_large_);
                for(auto it = in_edge_it.first; it != in_edge_it.second; ++it)
                {
                    VertexLargeType pred = boost::source(*it, matcher_.graph_large_);
                    auto pred_index = matcher_.large_vertices_indices_[pred];
                    if(matcher_.core_large_.find(pred) == matcher_.core_large_.end() &&
                        !matcher_.large_predecessors_[pred_index])
                    {
                        matcher_.large_predecessors_.set(pred_index);
                        new_predecessors_.push_back(pred_index);
                    }
                }
                auto out_edge_it = boost::out_edges(v_large_, matcher_.graph_large_);
                for(auto it = out_edge_it.first; it != out_edge_it.second; ++it)
                {
                    VertexLargeType succ = boost::target(*it, matcher_.graph_large_);
                    auto succ_index = matcher_.large_vertices_indices_[succ];
                    if(matcher_.core_large_.find(succ) == matcher_.core_large_.end() &&
                        !matcher_.large_successors_[succ_index])
                    {
                        matcher_.large_successors_.set(succ_index);
                        new_successors_.push_back(succ_index);
                    }
                }
            } else if (v_large_ == graph_traits<GraphLarge_>::null_vertex() && 
                        v_small_ == graph_traits<GraphSmall_>::null_vertex()) {
                matcher_.core_small_.clear();
                matcher_.core_large_.clear();
                matcher_.large_successors_.reset();
                matcher_.large_predecessors_.reset();
            }
        }

        boost::dynamic_bitset<> get_class_nodes(NodeClassificationType_ cls, char code)
        {
            auto& matcher_ = *matcher_ptr;
            if (code == 'p')
            {
                return (matcher_.large_predecessors_ & matcher_.graph_large_class_nodes_[cls]);
            } else if (code == 's')
            {
                return (matcher_.large_successors_ & matcher_.graph_large_class_nodes_[cls]);
            } else if (code == 'v')
            {
                boost::dynamic_bitset<> large_vertices(matcher_.num_large_vertices_);
                large_vertices.set();
                return (large_vertices & ~(matcher_.large_predecessors_ | matcher_.large_successors_) & matcher_.graph_large_class_nodes_[cls]);
            } else {
                BOOST_ASSERT_MSG(false, "Invalid code for class nodes retrieval");
                return {};
            }
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
            for(const auto &pred: new_predecessors_)
            {
                matcher_.large_predecessors_.reset(pred);
            }
            for(const auto& succ: new_successors_)
            {
                matcher_.large_successors_.reset(succ);
            }
        }
        ~vf3_state() { restore(); }
        vf3_state(const vf3_state&) = delete;

        matcher<GraphLarge_, GraphSmall_, NodeAttrPropertyMapLarge_, NodeAttrPropertyMapSmall_, NodeClassificationType_>* matcher_ptr;
        VertexLargeType v_large_;
        VertexSmallType v_small_;
        size_t depth_;
        std::vector<uint64_t> new_predecessors_;
        std::vector<uint64_t> new_successors_;
    }; // Class state

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
                const NodeAttrPropertyMapLarge& node_attr_map_large,
                const NodeAttrPropertyMapSmall& node_attr_map_small,
                LargeNodeClassificationFunc large_node_classification_func = nullptr,
                SmallNodeClassificationFunc small_node_classification_func = nullptr
            )
        : graph_large_(graph_large)
        , graph_small_(graph_small)
        , node_attr_map_large_(node_attr_map_large)
        , node_attr_map_small_(node_attr_map_small)
        , large_node_classification_func_(large_node_classification_func)
        , small_node_classification_func_(small_node_classification_func)
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
            
            for(const VertexSmallType& node: graph_small_vertices_)
            {
                size_t index = static_cast<size_t>(node);
                small_vertices_indices_[node] = index;
                small_indices_vertices_[index] = node;
            }
            for(const VertexLargeType& node: graph_large_vertices_)
            {
                size_t index = static_cast<size_t>(node);
                large_vertices_indices_[node] = index;
                large_indices_vertices_[index] = node;
            }

            large_predecessors_.resize(num_large_vertices_);
            large_predecessors_.reset();

            large_successors_.resize(num_large_vertices_);
            large_successors_.reset();

            initialize();

            state_ = vf3_state<GraphLarge, GraphSmall, NodeAttrPropertyMapLarge, NodeAttrPropertyMapSmall, NodeClassificationType>(this);
        }

        
        void initialize()
        {
            order_graph_small_vertices();
            classify_nodes();
            preprocess();

        }

        void match(std::vector<std::unordered_map<VertexLargeType, VertexSmallType>>& res)
        {
            if(core_small_.size() == num_small_vertices_)
            {
                res.push_back(core_small_);
            } else {
                std::vector<std::pair<VertexLargeType, VertexSmallType>> pairs{};
                candidate_pairs(pairs);
                for(const auto& [v_large_next, v_small_next]: pairs)
                {
                    if (syntactic_feasibility(v_large_next, v_small_next))
                    {
                        vf3_state<GraphLarge, GraphSmall, NodeAttrPropertyMapLarge, NodeAttrPropertyMapSmall, NodeClassificationType> new_state(this, v_large_next, v_small_next);
                        match(res);
                    }
                }
            }
            return;
        }

        void candidate_pairs(std::vector<std::pair<VertexLargeType, VertexSmallType>>& pairs)
        {
            size_t depth = core_small_.size();
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
                if (parents_[v_small_next] == graph_traits<GraphSmall>::null_vertex())
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
            return;
        }

        bool syntactic_feasibility(VertexLargeType v_large, VertexSmallType v_small)
        {
            if (graph_small_classes_[v_small] != graph_large_classes_[v_large])
            {
                return false;
            }

            boost::dynamic_bitset<> all_small_predecessors;
            boost::dynamic_bitset<> all_small_successors;
            boost::dynamic_bitset<> all_large_predecessors;
            boost::dynamic_bitset<> all_large_successors;

            all_small_predecessors.resize(num_small_vertices_);
            all_small_successors.resize(num_small_vertices_);
            all_large_predecessors.resize(num_large_vertices_);
            all_large_successors.resize(num_large_vertices_);

            auto in_edge_it = boost::in_edges(v_small, graph_small_);
            for(auto it = in_edge_it.first; it != in_edge_it.second; ++it)
            {
                VertexSmallType pred = boost::source(*it, graph_small_);
                if(core_small_.find(pred) != core_small_.end())
                {
                    VertexLargeType mapped_node = core_small_[pred];
                    auto edge = boost::edge(mapped_node, v_large, graph_large_);
                    if(!edge.second)
                    {
                        return false;
                    }
                }
                all_small_predecessors.set(small_vertices_indices_[pred]);
            }
            auto out_edge_it = boost::out_edges(v_small, graph_small_);
            for(auto it = out_edge_it.first; it != out_edge_it.second; ++it)
            {
                VertexSmallType succ = boost::target(*it, graph_small_);
                if(core_small_.find(succ) != core_small_.end())
                {
                    VertexLargeType mapped_node = core_small_[succ];
                    auto edge = boost::edge(v_large, mapped_node, graph_large_);
                    if(!edge.second)
                    {
                        return false;
                    }
                }
                all_small_successors.set(small_vertices_indices_[succ]);
            }
            auto large_in_edge_it = boost::in_edges(v_large, graph_large_);
            for(auto it = large_in_edge_it.first; it != large_in_edge_it.second; ++it)
            {
                VertexLargeType pred = boost::source(*it, graph_large_);
                if(core_large_.find(pred) != core_large_.end())
                {
                    VertexSmallType mapped_node = core_large_[pred];
                    auto edge = boost::edge(mapped_node, v_small, graph_small_);
                    if(!edge.second)
                    {
                        return false;
                    }
                }
                all_large_predecessors.set(large_vertices_indices_[pred]);
            }
            auto large_out_edge_it = boost::out_edges(v_large, graph_large_);
            for(auto it = large_out_edge_it.first; it != large_out_edge_it.second; ++it)
            {
                VertexLargeType succ = boost::target(*it, graph_large_);
                if(core_large_.find(succ) != core_large_.end())
                {
                    VertexSmallType mapped_node = core_large_[succ];
                    auto edge = boost::edge(v_small, mapped_node, graph_small_);
                    if(!edge.second)
                    {
                        return false;
                    }
                }
                all_large_successors.set(large_vertices_indices_[succ]);
            }
            auto curr_depth = core_small_.size();

            boost::dynamic_bitset<> p_small_cls_nodes;
            boost::dynamic_bitset<> s_small_cls_nodes;
            boost::dynamic_bitset<> v_small_cls_nodes;
            p_small_cls_nodes.resize(num_small_vertices_);
            s_small_cls_nodes.resize(num_small_vertices_);
            v_small_cls_nodes.resize(num_small_vertices_);

            boost::dynamic_bitset<> p_large_cls_nodes;
            boost::dynamic_bitset<> s_large_cls_nodes;
            boost::dynamic_bitset<> v_large_cls_nodes;
            p_large_cls_nodes.resize(num_large_vertices_);
            s_large_cls_nodes.resize(num_large_vertices_);
            v_large_cls_nodes.resize(num_large_vertices_);

            int i=0;

            for(const auto& cls: all_classes_)
            {
                p_small_cls_nodes = p_small_sets_[curr_depth] & graph_small_class_nodes_[cls];
                p_large_cls_nodes = state_.get_class_nodes(cls, 'p');
                if((p_small_cls_nodes & all_small_predecessors).count() > (p_large_cls_nodes & all_large_predecessors).count())
                {
                    return false;
                }
                if((p_small_cls_nodes & all_small_successors).count() > (p_large_cls_nodes & all_large_successors).count())
                {
                    return false;
                }
                s_small_cls_nodes = s_small_sets_[curr_depth] & graph_small_class_nodes_[cls];
                s_large_cls_nodes = state_.get_class_nodes(cls, 's');
                if((s_small_cls_nodes & all_small_predecessors).count() > (s_large_cls_nodes & all_large_predecessors).count())
                {
                    return false;
                }
                if((s_small_cls_nodes & all_small_successors).count() > (s_large_cls_nodes & all_large_successors).count())
                {
                    return false;
                }
                v_small_cls_nodes = v_small_sets_[curr_depth] & graph_small_class_nodes_[cls];
                v_large_cls_nodes = state_.get_class_nodes(cls, 'v');
                if((v_small_cls_nodes & all_small_predecessors).count() > (v_large_cls_nodes & all_large_predecessors).count())
                {
                    return false;
                }
                if((v_small_cls_nodes & all_small_successors).count() > (v_large_cls_nodes & all_large_successors).count())
                {
                    return false;
                }

                p_small_cls_nodes.reset();
                s_small_cls_nodes.reset();
                v_small_cls_nodes.reset();

                p_large_cls_nodes.reset();
                s_large_cls_nodes.reset();
                v_large_cls_nodes.reset();
            }

            return true;
        }
        
        void preprocess()
        {
            size_t max_depth = node_order_.size();
            p_small_sets_.assign(max_depth+1, boost::dynamic_bitset<>(num_small_vertices_));
            s_small_sets_.assign(max_depth+1, boost::dynamic_bitset<>(num_small_vertices_));
            v_small_sets_.assign(max_depth+1, boost::dynamic_bitset<>(num_small_vertices_));

            
            std::pair<VertexSmallIterator, VertexSmallIterator> vp = boost::vertices(graph_small_);
            for(VertexSmallIterator it = vp.first; it != vp.second; ++it)
            {
                parents_[*it] = graph_traits<GraphSmall>::null_vertex();
            }

            auto small_vertices = boost::dynamic_bitset<>(num_small_vertices_);
            small_vertices.set();
            v_small_sets_[0] = small_vertices;
            
            boost::dynamic_bitset<> mapped_nodes;
            boost::dynamic_bitset<> all_predecessors;
            boost::dynamic_bitset<> all_successors;
            
            mapped_nodes.resize(num_small_vertices_);
            all_predecessors.resize(num_small_vertices_);
            all_successors.resize(num_small_vertices_);
            
            for(size_t depth=1; depth<=max_depth; ++depth)
            {
                mapped_nodes.set(small_vertices_indices_[node_order_[depth-1]]);
                auto in_edges = boost::in_edges(node_order_[depth-1], graph_small_);
                for(auto it = in_edges.first; it != in_edges.second; ++it)
                {
                    VertexSmallType pred = boost::source(*it, graph_small_);
                    all_predecessors.set(small_vertices_indices_[pred]);
                }
                auto out_edges = boost::out_edges(node_order_[depth-1], graph_small_);
                for(auto it = out_edges.first; it != out_edges.second; ++it)
                {
                    VertexSmallType succ = boost::target(*it, graph_small_);
                    all_successors.set(small_vertices_indices_[succ]);
                }
                p_small_sets_[depth] = (small_vertices & (~mapped_nodes)) & all_predecessors;
                s_small_sets_[depth] = (small_vertices & (~mapped_nodes)) & all_successors;
                v_small_sets_[depth] = (small_vertices & ~(mapped_nodes | p_small_sets_[depth] | v_small_sets_[depth]));
            }

            auto p_small_cls_sets_map_ = std::unordered_map<NodeClassificationType, boost::dynamic_bitset<>>();
            auto s_small_cls_sets_map_ = std::unordered_map<NodeClassificationType, boost::dynamic_bitset<>>();

            for(size_t depth=0; depth<=max_depth; ++depth)
            {
                boost::dynamic_bitset<> p_s_union_set(num_small_vertices_);
                p_s_union_set = p_small_sets_[depth] | s_small_sets_[depth];
                size_t pos = p_s_union_set.find_first();
                while(pos != boost::dynamic_bitset<>::npos)
                {
                    VertexSmallType node = small_indices_vertices_[pos];
                    auto cls = graph_small_classes_[node];
                    if(p_small_sets_[depth][pos])
                    {
                        if(p_small_cls_sets_map_.find(cls) == p_small_cls_sets_map_.end())
                        {
                            p_small_cls_sets_map_[cls] = boost::dynamic_bitset<>(num_small_vertices_);
                        }
                        if(!p_small_cls_sets_map_[cls][pos])
                        {
                            p_small_cls_sets_map_[cls].set(pos);
                            if(parents_[node] == graph_traits<GraphSmall>::null_vertex())
                            {
                                parents_[node] = node_order_[depth-1];
                            }
                        }
                    }
                    else {
                        if(s_small_cls_sets_map_.find(cls) == s_small_cls_sets_map_.end())
                        {
                            s_small_cls_sets_map_[cls] = boost::dynamic_bitset<>(num_small_vertices_);
                        }
                        if(!s_small_cls_sets_map_[cls][pos])
                        {
                            s_small_cls_sets_map_[cls].set(pos);
                            if(parents_[node] == graph_traits<GraphSmall>::null_vertex())
                            {
                                parents_[node] = node_order_[depth-1];
                            }
                        }
                    }
                    pos = p_s_union_set.find_next(pos);
                }
            }
        }

        void classify_nodes()
        {
            std::pair<VertexLargeIterator, VertexLargeIterator> vp = boost::vertices(graph_large_);
            auto default_cls = NodeClassificationType();
            for(VertexLargeIterator it = vp.first; it != vp.second; ++it)
            {
                graph_large_classes_[*it] = default_cls;
            }
            std::pair<VertexSmallIterator, VertexSmallIterator> vp_small = boost::vertices(graph_small_);
            for(VertexSmallIterator it = vp_small.first; it != vp_small.second; ++it)
            {
                graph_small_classes_[*it] = default_cls;
            }
            if (large_node_classification_func_ != nullptr && small_node_classification_func_ != nullptr) 
            {
                vp = boost::vertices(graph_large_);
                for(VertexLargeIterator it = vp.first; it != vp.second; ++it)
                {
                    VertexLargeType v = *it;
                    NodeClassificationType label = large_node_classification_func_(v, graph_large_);
                    graph_large_classes_[v] = label;
                    if(graph_large_class_nodes_.find(label) == graph_large_class_nodes_.end())
                    {
                        graph_large_class_nodes_[label] = boost::dynamic_bitset<>(num_large_vertices_);
                    }
                    graph_large_class_nodes_[label].set(large_vertices_indices_[v]);
                    all_classes_.insert(label);
                }
                vp_small = boost::vertices(graph_small_);
                for(VertexSmallIterator it = vp_small.first; it != vp_small.second; ++it)
                {
                    VertexSmallType v = *it;
                    NodeClassificationType label = small_node_classification_func_(v, graph_small_);
                    graph_small_classes_[v] = label;
                    if(graph_small_class_nodes_.find(label) == graph_small_class_nodes_.end())
                    {
                        graph_small_class_nodes_[label] = boost::dynamic_bitset<>(num_small_vertices_);
                    }
                    graph_small_class_nodes_[label].set(small_vertices_indices_[v]);
                    all_classes_.insert(label);
                }
            } else {
                graph_large_class_nodes_[default_cls] = boost::dynamic_bitset<>(num_large_vertices_);
                graph_large_class_nodes_[default_cls].set();
                graph_small_class_nodes_[default_cls] = boost::dynamic_bitset<>(num_small_vertices_);
                graph_small_class_nodes_[default_cls].set();
                all_classes_.insert(default_cls);
            }

        }

        void order_graph_small_vertices()
        {
            std::unordered_map< VertexSmallType, double > node_probabilities = compute_vertex_probabilities();
            std::unordered_map< VertexSmallType, double > dM_values;
            std::unordered_map< VertexSmallType, int > nodes_total_degree;
            std::pair<VertexSmallIterator, VertexSmallIterator> vp = boost::vertices(graph_small_);
            std::vector< VertexSmallType > remaining_nodes_candidates;
            remaining_nodes_candidates.reserve(num_small_vertices_);
            for (VertexSmallIterator it = vp.first; it != vp.second; ++it)
            {
                VertexSmallType v = *it;
                dM_values[v] = 0.0;
                nodes_total_degree[v] = boost::in_degree(v, graph_small_) + boost::out_degree(v, graph_small_);
                remaining_nodes_candidates.push_back(v);
            }
            std::vector< VertexSmallType > node_order;
            node_order.reserve(num_small_vertices_);

            while(node_order.size() < num_small_vertices_)
            {
                VertexSmallType next_node;
                if (node_order.empty())
                {
                    next_node = *std::min_element(
                    remaining_nodes_candidates.begin(), remaining_nodes_candidates.end(),
                        [&](VertexSmallType a, VertexSmallType b) {
                            return node_probabilities[a] < node_probabilities[b];
                        }
                    );
                }
                else 
                {
                    auto cmp = [&](VertexSmallType a, VertexSmallType b) {
                        if(dM_values[a] != dM_values[b])
                        {
                            return dM_values[a] > dM_values[b];
                        }
                        if(node_probabilities[a] != node_probabilities[b])
                        {
                            return node_probabilities[a] < node_probabilities[b];
                        }
                        if(nodes_total_degree[a] != nodes_total_degree[b])
                        {
                            return nodes_total_degree[a] > nodes_total_degree[b];
                        }
                    };
                    next_node = *std::min_element(remaining_nodes_candidates.begin(), remaining_nodes_candidates.end(), cmp);
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
            node_order_ = node_order;
        }

        std::unordered_map< VertexSmallType, double > compute_vertex_probabilities()
        {   
            typedef typename graph_traits< GraphSmall >::degree_size_type DegreeSizeType;

            std::unordered_map< NodeAttrValueType, int > label_counts_ = label_counts();
            std::vector<int> cumulative_in_degrees(num_small_vertices_+1);
            cumulative_degrees(cumulative_in_degrees, true);
            std::vector<int> cumulative_out_degrees(num_small_vertices_+1);
            cumulative_degrees(cumulative_out_degrees, false);
            std::unordered_map< VertexSmallType, double > probabilities;
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
                    label_probability *= static_cast<double>(label_count) / num_large_vertices_;
                }
                DegreeSizeType in_degree_v = boost::in_degree(v, graph_small_);
                double in_degree_probability = 0.0;
                if (in_degree_v < cumulative_in_degrees.size())
                {
                    in_degree_probability = static_cast<double>(cumulative_in_degrees[in_degree_v]) / num_large_vertices_;
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
                    out_degree_probability = static_cast<double>(cumulative_out_degrees[out_degree_v]) / num_large_vertices_;
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

        std::unordered_map< NodeAttrValueType, int > label_counts()
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


        void cumulative_degrees(std::vector<int>& ge, bool is_in_degree)
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
                max_degree = *std::max_element(degrees.begin(), degrees.end());
            }
            std::vector<int> hist(max_degree + 1, 0);
            for (DegreeSizeType d : degrees) {
                hist[d]++;
            }
            int running_sum = 0;
            for (int d = max_degree; d >= 0; --d) {
                running_sum += hist[d];
                ge[d] = running_sum;
            }
            return;
        }

        const GraphSmall& graph_small_;
        const GraphLarge& graph_large_;
        const NodeAttrPropertyMapLarge& node_attr_map_large_;
        const NodeAttrPropertyMapSmall& node_attr_map_small_;

        std::unordered_set< VertexSmallType > graph_small_vertices_;
        std::unordered_set< VertexLargeType > graph_large_vertices_;

        std::unordered_map< VertexSmallType, VertexLargeType > core_large_;
        std::unordered_map< VertexLargeType, VertexSmallType > core_small_;

        std::unordered_map< size_t, VertexSmallType > small_vertices_indices_;
        std::unordered_map< VertexSmallType, size_t > small_indices_vertices_;
        std::unordered_map< size_t, VertexLargeType > large_vertices_indices_;
        std::unordered_map< VertexLargeType, size_t > large_indices_vertices_;
        vf3_state<GraphLarge, GraphSmall, NodeAttrPropertyMapLarge, NodeAttrPropertyMapSmall, NodeClassificationType> state_;
        std::vector<VertexSmallType> node_order_;
        std::unordered_map< VertexLargeType, NodeClassificationType > graph_large_classes_;
        std::unordered_map< VertexSmallType, NodeClassificationType > graph_small_classes_;
        std::unordered_map< NodeClassificationType, boost::dynamic_bitset<>> graph_large_class_nodes_;
        std::unordered_map< NodeClassificationType, boost::dynamic_bitset<>> graph_small_class_nodes_;
        std::unordered_set< NodeClassificationType > all_classes_;
        LargeNodeClassificationFunc large_node_classification_func_;
        SmallNodeClassificationFunc small_node_classification_func_;
        std::vector<boost::dynamic_bitset<>> p_small_sets_;
        std::vector<boost::dynamic_bitset<>> s_small_sets_;
        std::vector<boost::dynamic_bitset<>> v_small_sets_;
        std::unordered_map<VertexSmallType, VertexSmallType> parents_;
        boost::dynamic_bitset<> large_predecessors_;
        boost::dynamic_bitset<> large_successors_;
        uint64_t num_small_vertices_;
        uint64_t num_large_vertices_;

    }; // Class matcher
    

} // namespace detail

} // namespace boost


#ifdef BOOST_ISO_INCLUDED_ITER_MACROS
#undef BOOST_ISO_INCLUDED_ITER_MACROS
#include <boost/graph/iteration_macros_undef.hpp>
#endif

#endif // BOOST_VF3_SUB_GRAPH_ISO_HPP