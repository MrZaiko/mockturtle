/*!
  \file aig_algebraic_rewriting.hpp
  \brief AIG algebraric rewriting

  EPFL CS-472 2021 Final Project Option 1
*/

#pragma once

#include "../networks/aig.hpp"
#include "../views/depth_view.hpp"
#include "../views/topo_view.hpp"
#include <cmath>
#include <mockturtle/views/fanout_view.hpp>
#include <queue>
#include <set>

namespace mockturtle
{

namespace detail
{

template<class Ntk>
class aig_algebraic_rewriting_impl
{
  using node = typename Ntk::node;
  using signal = typename Ntk::signal;

public:
  aig_algebraic_rewriting_impl( Ntk& ntk )
    : ntk( ntk ), final_signals(), cache(), distributivity_visited_and_changed(), associativity_visited_and_changed()
  {
    static_assert( has_level_v<Ntk>, "Ntk does not implement depth interface." );
    ntk = fanout_view{ntk};

    update_final_gates();
    //print_tree();
  }

  void run()
  {
    bool cont{true}; /* continue trying */
    while ( cont ) {
      cont = false; /* break the loop if no updates can be made */
      ntk.foreach_gate( [&]( node n ){
        if ( try_algebraic_rules( n ) ) {
          ntk.update_levels();
          update_final_gates();

          cache.clear();
          distributivity_visited_and_changed.clear();

          cont = true;
        }
      });
    }

    //print_tree();
  }

private:
  void update_final_gates() {
    ntk.foreach_po([&](signal const& s) {
        auto n = ntk.get_node(s);
        auto final_gate = std::pair<node, signal>(n, s);
        final_signals.insert(final_gate);
    });
  }

  /* Try various algebraic rules on node n. Return true if the network is updated. */
  bool try_algebraic_rules( node n ) {
    if ( try_associativity( n ) )
      return true;
    if ( try_distributivity( n ) )
      return true;
    if ( try_three_layer_distributivity( n ) )
      return true;

    /* TODO: add more rules here... */

    return false;
  }

  void print_tree() {
    std::cout << "PRINTING TREE\n";
    for(auto elem : final_signals) {
      std::cout << "OUTPUT from " << elem.first << "; Complemented " << ntk.is_complemented(elem.second) << '\n';
      std::unordered_map<node, std::vector<signal>> acc;
      list_signals(elem.second, 100, acc);

      for (auto elem1 : acc) {
        std::cout << "\tNode " << elem1.first << " connected to" << "\n";
        for (auto s : elem1.second) {
          std::cout << "\t\tSignal to " << ntk.get_node(s) << "; Complemented " << ntk.is_complemented(s) << "\n";
        }
      }
    }
    std::cout.flush();
  }

  /* Try the associativity rule on node n. Return true if the network is updated. */
  bool try_associativity( node n ) {
    auto swap_list = std::vector<signal>();

    this->list_nodes(n, swap_list);

    auto current_level = ntk.level(n) - this->max_level_in_list( swap_list );
    auto min_depth = swap_list.empty() ? 0 : ceil(log2(swap_list.size()));

    if (current_level > min_depth) {
      signal final_signal = this->swap( swap_list, true);

      //std::cout << "Circuit modified" << std::endl;
      ntk.substitute_node( n, final_signal );
      associativity_visited_and_changed.insert(std::pair<node, bool>(n, true));
      return true;
    }


    return false;
  }

  bool already_visited(node n, std::unordered_map<node, bool>& map) {
    try {
      map.at(n);
      return true;
    } catch (std::out_of_range& e) {
      return false;
    }
  }

  size_t max_level_in_list(std::vector<signal> swap_list) {
    auto max_level = 0;

    for (size_t i = 0; i < swap_list.size(); ++i) {
      auto node = ntk.get_node(swap_list[i]);
      auto level = ntk.level(node);

      if ( level > max_level) {
        max_level = level;
      }
    }

    return max_level;
  }

  void list_nodes(node n, std::vector<signal>& swap_list) {
    if (ntk.level(n) == 0) {
      return;
    }

    ntk.foreach_fanin(n, [&] (signal const& s) {
       auto node = ntk.get_node(s);

       if (ntk.level(node) == 0 || ntk.is_complemented(s) || already_visited(node, associativity_visited_and_changed)) {
         swap_list.push_back(s);
       } else {
         list_nodes(node, swap_list);
       }
    });
  }

  signal swap(std::vector<signal>& swap_list, bool first) {
    auto critical_matters = swap_list.size() % 2 == 1;
    auto res = std::vector<signal>();
    size_t index;

    if (first && critical_matters) {
      for (auto i = 0; i < swap_list.size(); ++i) {
        auto s = swap_list[i];
        if (i == swap_list.size() || ntk.is_on_critical_path(ntk.get_node(s))) {
          res.push_back(s);
          index = i;
          break;
        }
      }
    } else if (!first && critical_matters) {
      index = swap_list.size()-1;
      res.push_back(swap_list[index]);
    }

    auto hasRight = false;
    signal right;

    for (auto i = 0; i < swap_list.size(); ++i) {
      auto s = swap_list[i];
      if (critical_matters && index == i) {
        continue;
      }

      if (hasRight) {
        auto new_and = ntk.create_and(right, s);
        res.push_back(new_and);
        hasRight = false;
      } else {
        right = s;
        hasRight = true;
      }
    }

    if (res.size() == 1)
      return res[0];
    else
      return swap(res, false);
  }

  bool apply_distributivity(signal s) {
    auto n = ntk.get_node(s);

    std::unordered_map<node, std::vector<signal>> neighbors;
    list_signals(s, 2, neighbors);
    if (neighbors.size() != 6)
      return false;

    auto hasRight = false;
    node right_node, left_node;

    // CHECK AND SAVE LEVEL 1 NODES
    for (auto neighbor : neighbors[n] ) {
      if (!ntk.is_complemented(neighbor))
        return false;

      if (!hasRight){
        right_node = ntk.get_node(neighbor);
        hasRight = true;
      } else {
        left_node = ntk.get_node(neighbor);
      }
    }

    // FIND SHARED NODE
    auto shared_node = find_shared_node(neighbors[left_node], neighbors[right_node]);
    if (!shared_node.second)
      return false;

    // FIND NOT SHARED NODES
    signal left_s, right_s;
    for (auto l_s : neighbors[left_node] ) {
      auto l_n = ntk.get_node(l_s);
      if (l_n != ntk.get_node(shared_node.first)) {
        left_s = l_s;
        break;
      }
    }

    for (auto r_s : neighbors[right_node] ) {
      auto r_n = ntk.get_node(r_s);
      if (r_n != ntk.get_node(shared_node.first)) {
        right_s = r_s;
        break;
      }
    }

    // APPLY OR DISTRIBUTIVITY
    auto final_signal = ntk.create_nand(
        shared_node.first,
        ntk.create_nand(
            !left_s,
            !right_s
        )
    );

    ntk.substitute_node(n, final_signal);
    //std::cout << "Circuit modified \n";
    return true;
  }

  /* Try the distributivity rule on node n. Return true if the network is updated. */
  bool try_distributivity( node n ) {
    //std::cout << "Trying distributivity for " << n << std::endl;

    if (ntk.level(n) < 2 || already_visited(n, distributivity_visited_and_changed)) {
      return false;
    } else {
      distributivity_visited_and_changed.insert(std::pair<node, bool>(n, true));

      try {
        auto s = final_signals.at(n);
        return apply_distributivity(s);

      } catch (std::out_of_range& e) {
        auto modified = false;

        ntk.foreach_fanin(n, [&](signal const& s ) {
           modified |= apply_distributivity(s);
        });

        return modified;
      }
    }
  }

  std::pair<signal, bool> find_shared_node(std::vector<signal> l, std::vector<signal> r) {
    for (auto l_s : l) {
      auto l_node = ntk.get_node(l_s);
      auto l_complemented = ntk.is_complemented(l_s);

      for (auto r_s : r) {
        auto r_node = ntk.get_node(r_s);
        auto r_complemented = ntk.is_complemented(r_s);

        if (l_node == r_node && l_complemented == r_complemented)
          return std::pair<signal, bool>(l_s, true);
      }
    }

    return std::pair<signal, bool>(signal(), false);
  }

  bool apply_three_layer_distributivity(signal s) {
    auto n = ntk.get_node(s);

    std::unordered_map<node, std::vector<signal>> neighbors;
    list_signals(s, 3, neighbors);
    if (neighbors.size() != 7)
      return false;

    signal a, b, c, d;

    auto l1_neighbors = neighbors[n];
    signal l2_s;

    if ( l1_neighbors.size() != 2)
      return false;

    // IDENTIFY D
    auto l1_n1 = ntk.get_node( l1_neighbors[0]), l1_n2 = ntk.get_node( l1_neighbors[1]);
    if (ntk.level(l1_n1) > 2 && ntk.is_complemented( l1_neighbors[0])) {
      d = l1_neighbors[1];
      l2_s = l1_neighbors[0];
    } else if (ntk.level(l1_n2) > 2 && ntk.is_complemented( l1_neighbors[1])) {
      d = l1_neighbors[0];
      l2_s = l1_neighbors[1];
    } else {
      return false;
    }

    //IDENTIFY C
    auto l2_n = ntk.get_node(l2_s);
    auto l2_neighbors = neighbors[l2_n];
    signal l3_s;

    if ( l2_neighbors.size() != 2)
      return false;

    auto l2_n1 = ntk.get_node( l2_neighbors[0]), l2_n2 = ntk.get_node( l2_neighbors[1]);

    if (ntk.level(l2_n1) > 1 && ntk.is_complemented( l2_neighbors[0])) {
      c = l2_neighbors[1];
      l3_s = l2_neighbors[0];
    } else if (ntk.level(l2_n2) > 1 && ntk.is_complemented( l2_neighbors[1])) {
      c = l2_neighbors[0];
      l3_s = l2_neighbors[1];
    } else {
      return false;
    }

    // IDENTIFY A and B
    auto l3_n = ntk.get_node(l3_s);
    auto l3_neighbors = neighbors[l3_n];

    if ( l3_neighbors.size() != 2)
      return false;

    auto l3_n1 = ntk.get_node(l3_neighbors[0]), l3_n2 = ntk.get_node(l3_neighbors[1]);

    if (ntk.level(l3_n1) > ntk.level(l3_n2)) {
      a = l3_neighbors[0];
      b = l3_neighbors[1];
    } else {
      a = l3_neighbors[1];
      b = l3_neighbors[0];
    }


    // APPLY DISTRIBUTIVITY
    auto final_signal = ntk.create_nand(
      ntk.create_nand(
        d,
        !c
      ),
      ntk.create_nand(
        a,
        ntk.create_and(
          b,
          d
        )
      )
    );

    ntk.substitute_node(n, final_signal);
    //std::cout << "Circuit modified \n";
    return true;
  }

  bool try_three_layer_distributivity(node n) {
    if (ntk.level(n) < 3) {
      return false;
    } else {
      try {
        auto s = final_signals.at(n);
        return apply_three_layer_distributivity( s );

      } catch (std::out_of_range& e) {
        auto modified = false;

        ntk.foreach_fanin(n, [&](signal const& s ) {
         modified |= apply_three_layer_distributivity( s );
        });

        return modified;
      }
    }
  }


  void list_signals(signal s, size_t depth, std::unordered_map<node, std::vector<signal>>& acc) {
    auto n = ntk.get_node(s);

    if (depth == 0 || ntk.level(n) == 0) {
      acc.insert(std::pair<node, std::vector<signal>>(n, std::vector<signal>()));
      return;
    }

    std::vector<signal> neighbors;

    try {
      neighbors = cache.at(n);
    } catch (std::out_of_range& e) {
      ntk.foreach_fanin(n, [&](signal const& s) { neighbors.push_back(s); });
      acc.insert(std::pair<node, std::vector<signal>>(n, neighbors));
    }

    for ( int i = 0; i < neighbors.size(); ++i ) {
      auto neighbor = neighbors[i];
      list_signals(neighbor, depth-1, acc);
    }
  }

private:
  Ntk& ntk;
  std::unordered_map<node, signal> final_signals;
  std::unordered_map<node, bool> associativity_visited_and_changed;
  std::unordered_map<node, bool> distributivity_visited_and_changed;
  std::unordered_map<node, std::vector<signal>> cache;
};

} // namespace detail

/* Entry point for users to call */
template<class Ntk>
void aig_algebraic_rewriting( Ntk& ntk )
{
  static_assert( std::is_same_v<typename Ntk::base_type, aig_network>, "Ntk is not an AIG" );

  depth_view dntk{ntk};
  detail::aig_algebraic_rewriting_impl p( dntk );
  p.run();
}

} /* namespace mockturtle */