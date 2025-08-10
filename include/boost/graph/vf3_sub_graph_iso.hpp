#ifndef BOOST_VF3_SUB_GRAPH_ISO_HPP
#define BOOST_VF3_SUB_GRAPH_ISO_HPP

#include <iostream>
#include <iomanip>
#include <iterator>
#include <vector>
#include <utility>

#include <boost/assert.hpp>
#include <boost/graph/graph_utility.hpp>
#include <boost/graph/graph_traits.hpp>
#include <boost/type_traits/is_same.hpp>
#include <boost/dynamic_bitset.hpp>

#ifndef BOOST_GRAPH_ITERATION_MACROS_HPP
#define BOOST_ISO_INCLUDED_ITER_MACROS // local macro, see bottom of file
#include <boost/graph/iteration_macros.hpp>
#endif

namespace boost
{

namespace detail 
{
    template < typename GraphSmall, typename GraphLarge, 
               typename SmallGraphVertexClassMap, typename LargeGraphVertexClassMap,
               typename Callback, typename VertexCompPred >
    class matcher;

    template < typename GraphSmall_, typename GraphLarge_, 
               typename SmallGraphVertexClassMap_, typename LargeGraphVertexClassMap_,
               typename Callback_, typename VertexCompPred_ >
    class vf3_state
    {

        using LargeVertexType = typename graph_traits<GraphLarge_>::vertex_descriptor;
        using SmallVertexType = typename graph_traits<GraphSmall_>::vertex_descriptor;

        public:
        vf3_state(): matcher_ptr(nullptr) {}
        vf3_state(matcher<GraphSmall_, GraphLarge_, SmallGraphVertexClassMap_, LargeGraphVertexClassMap_, Callback_, VertexCompPred_>* m, 
                SmallVertexType v_small = graph_traits<GraphSmall_>::null_vertex(), LargeVertexType v_large = graph_traits<GraphLarge_>::null_vertex())
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
                auto v_large_index = matcher_.large_vertices_indices_[v_large_];
                if (!matcher_.large_predecessors_[v_large_index])
                {
                    matcher_.large_predecessors_.set(v_large_index);
                    new_preds.push_back(v_large_index);
                }
                if (!matcher_.large_successors_[v_large_index])
                {
                    matcher_.large_successors_.set(v_large_index);
                    new_succes.push_back(v_large_index);
                }

                BGL_FORALL_INEDGES_T(v_large_, e, matcher_.graph_large_, GraphLarge_)
                {
                    LargeVertexType pred = boost::source(e, matcher_.graph_large_);
                    int64_t pred_index = matcher_.large_vertices_indices_[pred];
                    if(matcher_.core_large_.find(pred) == matcher_.core_large_.end()
                        && !matcher_.large_predecessors_[pred_index])
                    {
                        matcher_.large_predecessors_.set(pred_index);
                        new_preds.push_back(pred_index);
                    }
                }

                BGL_FORALL_OUTEDGES_T(v_large_, e, matcher_.graph_large_, GraphLarge_)
                {
                    LargeVertexType succ = boost::target(e, matcher_.graph_large_);
                    int64_t succ_index = matcher_.large_vertices_indices_[succ];
                    if(matcher_.core_large_.find(succ) == matcher_.core_large_.end() &&
                        !matcher_.large_successors_[succ_index])
                    {
                        matcher_.large_successors_.set(succ_index);
                        new_succes.push_back(succ_index);
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

        void restore()
        {
            auto& matcher_ = *matcher_ptr;
            if (v_large_ != graph_traits<GraphLarge_>::null_vertex() && 
                v_small_ != graph_traits<GraphSmall_>::null_vertex())
            {
                matcher_.core_large_.erase(v_large_);
                matcher_.core_small_.erase(v_small_);
            }
            for(const auto& pred: new_preds)
            {
                matcher_.large_predecessors_.reset(pred);
            }
            for(const auto& succ: new_succes)
            {
                matcher_.large_successors_.reset(succ);
            }
        }
        ~vf3_state() { restore(); }
        vf3_state(const vf3_state&) = delete;

        matcher<GraphSmall_, GraphLarge_, SmallGraphVertexClassMap_, LargeGraphVertexClassMap_, Callback_, VertexCompPred_>* matcher_ptr;
        LargeVertexType v_large_;
        SmallVertexType v_small_;
        int64_t depth_;
        std::vector<int64_t> new_preds;
        std::vector<int64_t> new_succes;
    }; // Class state

    struct vertex_always_true {
        template<typename V1, typename V2>
        bool operator()(const V1&, const V2&) const noexcept {
            return true;
        }
    }; // struct vertex_always_true

    template < typename GraphSmall, typename GraphLarge, 
               typename SmallGraphVertexClassMap, typename LargeGraphVertexClassMap,
               typename Callback,
               typename VertexCompPred = vertex_always_true >
    class matcher
    {   
        public:

        using SmallVertexType = typename boost::graph_traits<GraphSmall>::vertex_descriptor;
        using SmallVertexIterator = typename boost::graph_traits<GraphSmall>::vertex_iterator;
        
        using LargeVertexType = typename boost::graph_traits<GraphLarge>::vertex_descriptor;
        using LargeVertexIterator = typename boost::graph_traits<GraphLarge>::vertex_iterator;

        // Separate class types for asserting
        using SmallClassType = typename boost::property_traits<SmallGraphVertexClassMap>::value_type;
        using LargeClassType = typename boost::property_traits<LargeGraphVertexClassMap>::value_type;

        // Common class type
        using ClassType = typename boost::property_traits<SmallGraphVertexClassMap>::value_type;
        
        public:
        matcher(const GraphSmall& graph_small, 
                const GraphLarge& graph_large,
                const SmallGraphVertexClassMap& small_graph_vertex_class_map,
                const LargeGraphVertexClassMap& large_graph_vertex_class_map,
                Callback callback,
                VertexCompPred vertex_comp_pred = VertexCompPred{}
            )
        : graph_small_(graph_small)
        , graph_large_(graph_large)
        , small_graph_vertex_class_map_(small_graph_vertex_class_map)
        , large_graph_vertex_class_map_(large_graph_vertex_class_map)
        , vertex_comp_pred_(vertex_comp_pred)
        , num_small_vertices_(boost::num_vertices(graph_small))
        , num_large_vertices_(boost::num_vertices(graph_large))
        , callback_(callback)
        , large_predecessors_(boost::num_vertices(graph_large))
        , large_successors_(boost::num_vertices(graph_large))
        {
            BOOST_STATIC_ASSERT(( boost::is_same<SmallClassType, LargeClassType>::value ));

            BOOST_ASSERT( num_vertices(graph_small) <= num_vertices(graph_large) );
            BOOST_ASSERT( num_edges(graph_small) <= num_edges(graph_large) );
            
            int64_t small_vertex_index = 0;
            int64_t current_class_index = 0;
            BGL_FORALL_VERTICES_T(node, graph_small_, GraphSmall)
            {
                small_vertices_indices_[node] = small_vertex_index;
                small_indices_vertices_[small_vertex_index] = node;
                parents_[node] = boost::graph_traits<GraphSmall>::null_vertex();
                ++small_vertex_index;
                ClassType c = small_graph_vertex_class_map_[node];
                if(class_index_map_.find(c) == class_index_map_.end())
                {
                    current_class_index = class_index_map_.size();
                    class_index_map_[c] = current_class_index;
                }
            }

            int64_t large_vertex_index = 0;
            BGL_FORALL_VERTICES_T(node, graph_large_, GraphLarge)
            {
                large_vertices_indices_[node] = large_vertex_index;
                large_indices_vertices_[large_vertex_index] = node;
                ++large_vertex_index;
                ClassType c = large_graph_vertex_class_map_[node];
                if(class_index_map_.find(c) == class_index_map_.end())
                {
                    current_class_index = class_index_map_.size();
                    class_index_map_[c] = current_class_index;
                }
            }

            num_classes_ = class_index_map_.size();

            initialize();

            state_ = vf3_state<GraphSmall, GraphLarge, SmallGraphVertexClassMap, LargeGraphVertexClassMap, Callback, VertexCompPred>(this);
            found_match_ = false;
            stop_search_ = false;
        }

        
        void initialize()
        {
            order_graph_small_vertices();
            preprocess();
        }

        bool match()
        {
            if(stop_search_)
            {
                return found_match_;
            }
            if(core_small_.size() == num_small_vertices_)
            {
                found_match_ = true;
                if(!callback_(core_small_, core_large_))
                {
                    stop_search_ = true;
                }
                return true;
            } else {
                std::vector<std::pair<SmallVertexType, LargeVertexType>> pairs{};
                candidate_pairs(pairs);
                for(const auto& [v_small_next, v_large_next]: pairs)
                {
                    if (syntactic_feasibility(v_small_next, v_large_next))
                    {
                        vf3_state<GraphSmall, GraphLarge, SmallGraphVertexClassMap, LargeGraphVertexClassMap, Callback, VertexCompPred> new_state(this, v_small_next, v_large_next);
                        if(match())
                        {
                            if(stop_search_)
                            {
                                return true;
                            }
                        }
                    }
                }
            }
            return found_match_;
        }

        void candidate_pairs(std::vector<std::pair<SmallVertexType, LargeVertexType>>& pairs)
        {
            int64_t depth = core_small_.size();
            SmallVertexType v_small_next;

            if (state_.v_small_ != graph_traits<GraphSmall>::null_vertex() || depth < num_small_vertices_)
            {
                if(state_.v_small_ == graph_traits<GraphSmall>::null_vertex())
                {
                    v_small_next = node_order_[depth];
                } else {
                    v_small_next = state_.v_small_;
                }
                ClassType v_small_next_class = small_graph_vertex_class_map_[v_small_next];
                if (parents_[v_small_next] == graph_traits<GraphSmall>::null_vertex())
                {
                    BGL_FORALL_VERTICES_T(v, graph_large_, GraphLarge)
                    {
                        if(large_graph_vertex_class_map_[v] == v_small_next_class &&
                            core_large_.find(v) == core_large_.end())
                        {
                            pairs.emplace_back(v_small_next, v);
                        }
                    }
                } else {
                    SmallVertexType v_small_parent = parents_[v_small_next];
                    LargeVertexType v_large_parent = core_small_[v_small_parent];
                    if (boost::edge(v_small_next, v_small_parent, graph_small_).second && !boost::edge(v_small_parent, v_small_next, graph_small_).second)
                    {
                        BGL_FORALL_INEDGES_T(v_large_parent, e, graph_large_, GraphLarge)
                        {
                            LargeVertexType v_large_next = boost::source(e, graph_large_);
                            if( large_graph_vertex_class_map_[v_large_next] == v_small_next_class && 
                                core_large_.find(v_large_next) == core_large_.end())
                            {
                                pairs.emplace_back(v_small_next, v_large_next);
                            }
                        }
                    } else if (boost::edge(v_small_parent, v_small_next, graph_small_).second && !boost::edge(v_small_next, v_small_parent, graph_small_).second)
                    {
                        BGL_FORALL_OUTEDGES_T(v_large_parent, e, graph_large_, GraphLarge)
                        {
                            LargeVertexType v_large_next = boost::target(e, graph_large_);
                            if(large_graph_vertex_class_map_[v_large_next] == v_small_next_class &&
                                core_large_.find(v_large_next) == core_large_.end())
                            {
                                pairs.emplace_back(v_small_next, v_large_next);
                            }
                        }
                    } else if (boost::edge(v_small_parent, v_small_next, graph_small_).second && boost::edge(v_small_next, v_small_parent, graph_small_).second)
                    {
                        BGL_FORALL_INEDGES_T(v_large_parent, e, graph_large_, GraphLarge)
                        {
                            LargeVertexType v_large_next = boost::source(e, graph_large_);
                            if(large_graph_vertex_class_map_[v_large_next] == v_small_next_class &&
                                core_large_.find(v_large_next) == core_large_.end() &&
                                boost::edge(v_large_parent, v_large_next, graph_large_).second)
                            {
                                pairs.emplace_back(v_small_next, v_large_next);
                            }
                        }
                    }
                }
            }
            return;
        }

        bool syntactic_feasibility(SmallVertexType v_small, LargeVertexType v_large)
        {
            if(!vertex_comp_pred_(v_small, v_large))
            {
                return false;
            }

            std::vector<int64_t> pp_sizes(num_classes_, 0);
            std::vector<int64_t> ps_sizes(num_classes_, 0);
            std::vector<int64_t> sp_sizes(num_classes_, 0);
            std::vector<int64_t> ss_sizes(num_classes_, 0);
            std::vector<int64_t> pv_sizes(num_classes_, 0);
            std::vector<int64_t> sv_sizes(num_classes_, 0);

            BGL_FORALL_INEDGES_T(v_large, e, graph_large_, GraphLarge)
            {
                LargeVertexType pred = boost::source(e, graph_large_);
                int64_t pred_index = large_vertices_indices_[pred];
                if(core_large_.find(pred) != core_large_.end())
                {
                    SmallVertexType mapped_node = core_large_[pred];
                    if(!boost::edge(mapped_node, v_small, graph_small_).second)
                    {
                        return false;
                    }
                    continue;
                }
                ClassType c = large_graph_vertex_class_map_[pred];
                int64_t c_index = class_index_map_[c];
                if(pred_index >= large_predecessors_.size() ||
                    pred_index >= large_successors_.size())
                {
                    std::cout << "GOTCHA" << std::endl;
                }
                if(large_predecessors_[pred_index])
                {
                    pp_sizes[c_index]++;
                } else {
                    if(!large_successors_[pred_index])
                    {
                        pv_sizes[c_index]++;
                    }
                }
                if(large_successors_[pred_index])
                {
                    ps_sizes[c_index]++;
                }
            }

            BGL_FORALL_OUTEDGES_T(v_large, e, graph_large_, GraphLarge)
            {
                LargeVertexType succ = boost::target(e, graph_large_);
                int64_t succ_index = large_vertices_indices_[succ];

                if(core_large_.find(succ) != core_large_.end())
                {
                    SmallVertexType mapped_node = core_large_[succ];
                    if(!boost::edge(v_small, mapped_node, graph_small_).second)
                    {
                        return false;
                    }
                    continue;
                }
                ClassType c = large_graph_vertex_class_map_[succ];
                int64_t c_index = class_index_map_[c];
                if(succ_index >= large_predecessors_.size() ||
                    succ_index >= large_successors_.size())
                {
                    std::cout << "GOTCHA" << std::endl;
                }
                if(large_predecessors_[succ_index])
                {
                    sp_sizes[c_index]++;
                } else {
                    if(!large_successors_[succ_index])
                    {
                        sv_sizes[c_index]++;
                    }
                }
                if(large_successors_[succ_index])
                {
                    ss_sizes[c_index]++;
                }
            }

            auto curr_depth = core_small_.size();

            for(int64_t c_index = 0; c_index < num_classes_; ++c_index)
            {
                if(pp_sizes_[curr_depth][c_index] > pp_sizes[c_index] ||
                    ps_sizes_[curr_depth][c_index] > ps_sizes[c_index] ||
                    sp_sizes_[curr_depth][c_index] > sp_sizes[c_index] ||
                    ss_sizes_[curr_depth][c_index] > ss_sizes[c_index] ||
                    pv_sizes_[curr_depth][c_index] > pv_sizes[c_index] ||
                    sv_sizes_[curr_depth][c_index] > sv_sizes[c_index])
                {
                    return false;
                }
            }

            return true;
        }

        void preprocess()
        {
            int64_t max_depth = num_small_vertices_;

            pp_sizes_.assign(max_depth+1, std::vector<int64_t>(num_classes_, 0));
            ps_sizes_.assign(max_depth+1, std::vector<int64_t>(num_classes_, 0));
            sp_sizes_.assign(max_depth+1, std::vector<int64_t>(num_classes_, 0));
            ss_sizes_.assign(max_depth+1, std::vector<int64_t>(num_classes_, 0));
            pv_sizes_.assign(max_depth+1, std::vector<int64_t>(num_classes_, 0));
            sv_sizes_.assign(max_depth+1, std::vector<int64_t>(num_classes_, 0));

            boost::dynamic_bitset<> inserted(num_small_vertices_);
            boost::dynamic_bitset<> p_set(num_small_vertices_);
            boost::dynamic_bitset<> s_set(num_small_vertices_);
            boost::dynamic_bitset<> v_set(num_small_vertices_, true);

            boost::dynamic_bitset<> new_preds(num_small_vertices_);
            boost::dynamic_bitset<> new_succes(num_small_vertices_);

            for(int64_t depth=0; depth<=max_depth; ++depth)
            {
                new_preds.reset();
                new_succes.reset();
                SmallVertexType current_node = node_order_[depth];
                int64_t current_node_index = small_vertices_indices_[current_node];

                BGL_FORALL_INEDGES_T(current_node, e, graph_small_, GraphSmall)
                {
                    SmallVertexType pred = boost::source(e, graph_small_);
                    int64_t pred_index = small_vertices_indices_[pred];

                    ClassType c = small_graph_vertex_class_map_[pred];
                    int64_t c_index = class_index_map_[c];

                    if(p_set[pred_index])
                    {
                        pp_sizes_[depth][c_index]+=1;
                    } else {
                        if(!s_set[pred_index] && !inserted[pred])
                        {
                            parents_[pred] = current_node;
                        }
                    }
                    if(s_set[pred_index])
                    {
                        ps_sizes_[depth][c_index]+=1;
                    }
                    if(v_set[pred_index])
                    {
                        pv_sizes_[depth][c_index]+=1;
                    }
                    new_preds.set(pred_index);
                }

                BGL_FORALL_OUTEDGES_T(current_node, e, graph_small_, GraphSmall)
                {
                    SmallVertexType succ = boost::target(e, graph_small_);
                    int64_t succ_index = small_vertices_indices_[succ];

                    ClassType c = small_graph_vertex_class_map_[succ];
                    int64_t c_index = class_index_map_[c];

                    if(p_set[succ_index])
                    {
                        sp_sizes_[depth][c_index] += 1;
                    }
                    if(s_set[succ_index])
                    {
                        ss_sizes_[depth][c_index] += 1;
                    } else {
                        if(!p_set[succ_index] && !inserted[succ_index])
                        {
                            parents_[succ] = current_node;
                        }
                    }
                    if(v_set[succ_index])
                    {
                        sv_sizes_[depth][c_index] += 1;
                    }
                    new_succes.set(succ_index);
                }

                inserted.set(current_node_index);
                p_set = (p_set | new_preds) & ~(inserted);
                s_set = (s_set | new_succes) & ~(inserted);
                v_set = ~(inserted | p_set | s_set);
            }
        }

        void order_graph_small_vertices()
        {
            std::unordered_map< SmallVertexType, double > node_probabilities;
            compute_vertex_probabilities(node_probabilities);
            std::unordered_map< SmallVertexType, double > dM_values;
            std::unordered_map< SmallVertexType, int64_t > nodes_total_degree;
            std::vector< SmallVertexType > remaining_nodes_candidates;
            remaining_nodes_candidates.reserve(num_small_vertices_);
            BGL_FORALL_VERTICES_T(v, graph_small_, GraphSmall)
            {
                dM_values[v] = 0.0;
                nodes_total_degree[v] = boost::in_degree(v, graph_small_) + boost::out_degree(v, graph_small_);
                remaining_nodes_candidates.push_back(v);
            }

            node_order_.reserve(num_small_vertices_);

            while(node_order_.size() < num_small_vertices_)
            {
                SmallVertexType next_node;
                if (node_order_.empty())
                {
                    // At the beginning, only the node_probabilities matter
                    next_node = *std::min_element(
                    remaining_nodes_candidates.begin(), remaining_nodes_candidates.end(),
                        [&](SmallVertexType a, SmallVertexType b) {
                            return node_probabilities[a] < node_probabilities[b];
                        }
                    );
                }
                else 
                {
                    auto cmp = [&](SmallVertexType a, SmallVertexType b) {
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
                node_order_.push_back(next_node);
                remaining_nodes_candidates.erase(
                    std::remove(remaining_nodes_candidates.begin(), remaining_nodes_candidates.end(), next_node),
                    remaining_nodes_candidates.end()
                );
                dM_values.erase(next_node);
                BGL_FORALL_OUTEDGES_T(next_node, e, graph_small_, GraphSmall)
                {
                    SmallVertexType target = boost::target(e, graph_small_);
                    if (dM_values.find(target) != dM_values.end())
                    {
                        dM_values[target] += 1;
                    }
                }

                BGL_FORALL_INEDGES_T(next_node, e, graph_small_, GraphSmall)
                {
                    SmallVertexType source = boost::source(e, graph_small_);
                    if(dM_values.find(source) != dM_values.end())
                    {
                        dM_values[source] += 1;
                    }
                }
            }
        }

        void compute_vertex_probabilities(std::unordered_map< SmallVertexType, double >& probs)
        {   
            std::unordered_map< ClassType, int64_t > label_counts_;
            label_counts(label_counts_);
            std::vector<int64_t> cumulative_in_degrees(num_small_vertices_+1);
            std::vector<int64_t> cumulative_out_degrees(num_small_vertices_+1);
            cumulative_degrees(cumulative_in_degrees, cumulative_out_degrees);
            int64_t label_count;
            
            double label_prop = 1.0;
            double in_deg_prob;
            double out_deg_prob;

            BGL_FORALL_VERTICES_T(v, graph_small_, GraphSmall)
            {
                ClassType c = small_graph_vertex_class_map_[v];
                if(label_counts_.find(c) == label_counts_.end())
                {
                    probs[v] = 0.0;
                    continue;
                } else {
                    label_count = label_counts_[c];
                    label_prop = static_cast<double>(label_count) / num_large_vertices_;
                }

                int64_t in_deg_size = boost::in_degree(v, graph_small_);
                if(in_deg_size >= cumulative_in_degrees.size())
                {
                    probs[v] = 0.0;
                    continue;
                }
                in_deg_prob = static_cast<double>(cumulative_in_degrees[in_deg_size]) / num_large_vertices_;

                int64_t out_deg_size = boost::out_degree(v, graph_small_);
                if(out_deg_size >= cumulative_out_degrees.size())
                {
                    probs[v] = 0.0;
                    continue;
                }
                out_deg_prob = static_cast<double>(cumulative_out_degrees[out_deg_size]) / num_large_vertices_;

                probs[v] = label_prop * in_deg_prob * out_deg_prob;
            }
        }

        void label_counts(std::unordered_map< ClassType, int64_t >& labels)
        {   
            BGL_FORALL_VERTICES_T(v, graph_large_, GraphLarge)
            {
                labels[large_graph_vertex_class_map_[v]]++;
            }
        }


        void cumulative_degrees(std::vector<int64_t>& in_ge, std::vector<int64_t>& out_ge)
        {
            std::vector<int64_t> in_degrees, out_degrees;
            in_degrees.reserve(num_large_vertices_);
            out_degrees.reserve(num_large_vertices_);

            int64_t max_in_degree = 0;
            int64_t max_out_degree = 0;

            BGL_FORALL_VERTICES_T(v, graph_large_, GraphLarge)
            {
                int64_t in_deg = boost::in_degree(v, graph_large_);
                int64_t out_deg = boost::out_degree(v, graph_large_);
                in_degrees.push_back(in_deg);
                out_degrees.push_back(out_deg);
                max_in_degree = std::max(max_in_degree, in_deg);
                max_out_degree = std::max(max_out_degree, out_deg);
            }

            std::vector<int64_t> in_hist(max_in_degree + 1, 0);
            std::vector<int64_t> out_hist(max_out_degree + 1, 0);

            for (auto in_d : in_degrees) {
                in_hist[in_d]++;
            }
            for(auto out_d: out_degrees)
            {
                out_hist[out_d]++;
            }

            int64_t in_running_sum = 0;
            for (int64_t d1 = max_in_degree; d1 >= 0; --d1) {
                in_running_sum += in_hist[d1];
                in_ge[d1] = in_running_sum;
            }
            int64_t out_running_sum = 0;
            for(int64_t d2 = max_out_degree; d2 >= 0; --d2)
            {
                out_running_sum += out_hist[d2];
                out_ge[d2] = out_running_sum;
            }
        }

        const GraphSmall& graph_small_;
        const GraphLarge& graph_large_;
        const SmallGraphVertexClassMap& small_graph_vertex_class_map_;
        const LargeGraphVertexClassMap& large_graph_vertex_class_map_;
        const VertexCompPred& vertex_comp_pred_;

        int64_t num_small_vertices_;
        int64_t num_large_vertices_;

        int64_t num_classes_;

        std::unordered_map< SmallVertexType, LargeVertexType > core_large_;
        std::unordered_map< LargeVertexType, SmallVertexType > core_small_;

        std::unordered_map< int64_t, SmallVertexType > small_vertices_indices_;
        std::unordered_map< SmallVertexType, int64_t > small_indices_vertices_;
        std::unordered_map< int64_t, LargeVertexType > large_vertices_indices_;
        std::unordered_map< LargeVertexType, int64_t > large_indices_vertices_;
        vf3_state<GraphSmall, GraphLarge, SmallGraphVertexClassMap, LargeGraphVertexClassMap, Callback, VertexCompPred> state_;
        
        std::vector<SmallVertexType> node_order_;

        std::vector<std::vector<int64_t>> pp_sizes_;
        std::vector<std::vector<int64_t>> ps_sizes_;
        std::vector<std::vector<int64_t>> sp_sizes_;
        std::vector<std::vector<int64_t>> ss_sizes_;
        std::vector<std::vector<int64_t>> pv_sizes_;
        std::vector<std::vector<int64_t>> sv_sizes_;

        std::unordered_map<SmallVertexType, SmallVertexType> parents_;

        boost::dynamic_bitset<> large_predecessors_;
        boost::dynamic_bitset<> large_successors_;

        std::unordered_map<ClassType, int64_t> class_index_map_;

        Callback callback_;
        bool stop_search_;
        bool found_match_;

    }; // Class matcher

    template < typename Graph >
    struct default_vertex_class_map {
        using vertex_descriptor = typename graph_traits<Graph>::vertex_descriptor;
        using value_type = int;
        using reference = int;
        using key_type = vertex_descriptor;
        using category = boost::readable_property_map_tag;

        int operator[](const vertex_descriptor&) const { return 0; }
    }; // default_vertex_class_map

} // namespace detail

template < typename Graph >
int get(const detail::default_vertex_class_map<Graph>& map,
        const typename graph_traits<Graph>::vertex_descriptor& v)
{
    return map[v];
}

template < typename GraphSmall, typename GraphLarge, typename Callback >
bool vf3_subgraph_iso(const GraphSmall& graph_small,
                      const GraphLarge& graph_large,
                      Callback callback)
{
    using SmallVertexType = typename graph_traits<GraphSmall>::vertex_descriptor;
    using LargeVertexType = typename graph_traits<GraphLarge>::vertex_descriptor;

    detail::default_vertex_class_map<GraphSmall> small_map;
    detail::default_vertex_class_map<GraphLarge> large_map;
    detail::vertex_always_true vertex_comp;

    detail::matcher<GraphSmall, GraphLarge,
                            detail::default_vertex_class_map<GraphSmall>,
                            detail::default_vertex_class_map<GraphLarge>,
                            Callback,
                            detail::vertex_always_true>
        m(graph_small, graph_large, small_map, large_map, callback, vertex_comp);
    return m.match();
}

template < typename GraphSmall, typename GraphLarge,
            typename SmallGraphVertexClassMap,
            typename LargeGraphVertexClassMap,
            typename Callback>
bool vf3_subgraph_iso(const GraphSmall& graph_small,
                      const GraphLarge& graph_large,
                      const SmallGraphVertexClassMap& small_map,
                      const LargeGraphVertexClassMap& large_map,
                      Callback callback)
{

    detail::vertex_always_true vertex_comp;
    detail::matcher<GraphSmall, GraphLarge,
                            SmallGraphVertexClassMap,
                            LargeGraphVertexClassMap,
                            Callback,
                            detail::vertex_always_true>
            m(graph_small, graph_large, small_map, large_map, callback, vertex_comp);
    return m.match();
}

template < typename GraphSmall, typename GraphLarge,
            typename SmallGraphVertexClassMap,
            typename LargeGraphVertexClassMap,
            typename Callback,
            typename VertexCompPred>
bool vf3_subgraph_iso(const GraphSmall& graph_small,
                      const GraphLarge& graph_large,
                      const SmallGraphVertexClassMap& small_map,
                      const LargeGraphVertexClassMap& large_map,
                      Callback callback,
                      VertexCompPred vertex_comp_pred)
{
    detail::vertex_always_true vertex_comp;
    detail::matcher<GraphSmall, GraphLarge,
                            SmallGraphVertexClassMap,
                            LargeGraphVertexClassMap,
                            Callback,
                            VertexCompPred>
            m(graph_small, graph_large, small_map, large_map, callback, vertex_comp_pred);
    return m.match();
}


} // namespace boost


#ifdef BOOST_ISO_INCLUDED_ITER_MACROS
#undef BOOST_ISO_INCLUDED_ITER_MACROS
#include <boost/graph/iteration_macros_undef.hpp>
#endif

#endif // BOOST_VF3_SUB_GRAPH_ISO_HPP