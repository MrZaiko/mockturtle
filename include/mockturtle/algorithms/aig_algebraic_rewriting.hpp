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
#include <mockturtle/io/write_dot.hpp>
#include <mockturtle/views/fanout_view.hpp>
#include <queue>
#include <set>

namespace mockturtle {

namespace detail {

template <class Ntk> class aig_algebraic_rewriting_impl {
  using node = typename Ntk::node;
  using signal = typename Ntk::signal;

public:
  aig_algebraic_rewriting_impl(Ntk& ntk) : ntk(ntk), final_signals(), cache(), distributivity_visited_and_changed() {
    static_assert(has_level_v<Ntk>, "Ntk does not implement depth interface.");

    update_final_gates();
  }

  void run() {
    bool cont{true}; /* continue trying */
    while (cont) {
      cont = false; /* break the loop if no updates can be made */
      ntk.foreach_gate([&](node n) {
        if (try_algebraic_rules(n)) {
          ntk.update_levels();

          update_final_gates();

          cache.clear();
          distributivity_visited_and_changed.clear();

          cont = true;
        }
      });
    }
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
  bool try_algebraic_rules(node n) {

    if (try_distributivity(n))
      return true;

    if (try_associativity(n))
      return true;

    if (try_three_layer_distributivity(n))
      return true;

    return false;
  }

  void print_tree() {
    std::cout << "PRINTING TREE\n";
    for (auto elem : final_signals) {
      std::cout << "OUTPUT from " << elem.first << "; Complemented " << ntk.is_complemented(elem.second) << '\n';
      std::unordered_map<node, std::vector<signal>> acc;
      list_neighbors(elem.second, 100, acc);

      for (auto elem1 : acc) {
        std::cout << "\tNode " << elem1.first << " connected to"
                  << "\n";
        for (auto s : elem1.second) {
          std::cout << "\t\tSignal to " << ntk.get_node(s) << "; Complemented " << ntk.is_complemented(s) << "\n";
        }
      }
    }
    std::cout.flush();
  }

  /* Try the associativity rule on node n. Return true if the network is updated. */
  bool try_associativity(node n) {
    signal critical_signal;
    bool found = false;

    signal first_level, second_level;
    int children = 0;

    if (ntk.is_on_critical_path(n)) {
      ntk.foreach_fanin(n, [&](signal const& s) {
        auto fanin_node = ntk.get_node(s);
        if (!found && !ntk.is_complemented(s) && ntk.is_on_critical_path(fanin_node)) {
          ntk.foreach_fanin(fanin_node, [&](signal const& critical_s) {
            auto critical_n = ntk.get_node(critical_s);
            if (!found && ntk.is_on_critical_path(critical_n)) {
              critical_signal = critical_s;
              found = true;
            } else {
              second_level = critical_s;
              children++;
            }
          });
        } else {
          first_level = s;
          children++;
        }
      });

      if (found && children == 2 && ntk.level(ntk.get_node(critical_signal)) > ntk.level(ntk.get_node(first_level))) {

        if (ntk.is_pi(ntk.get_node(first_level)) && ntk.is_on_critical_path(ntk.get_node(second_level))) {
          return false;
        }

        auto new_signal = ntk.create_and(critical_signal, ntk.create_and(first_level, second_level));

        ntk.substitute_node(n, new_signal);
        return true;
      }
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

  void list_nodes(node n, std::vector<signal>& swap_list, int depth) {
    if (ntk.level(n) == 0) {
      return;
    }

    ntk.foreach_fanin(n, [&](signal const& s) {
      auto node = ntk.get_node(s);

      if (ntk.level(node) == 0 || ntk.is_complemented(s) || depth == 0) {
        swap_list.push_back(s);
      } else {
        list_nodes(node, swap_list, depth - 1);
      }
    });
  }

  bool apply_distributivity(signal s) {
    auto n = ntk.get_node(s);

    std::unordered_map<node, std::vector<signal>> neighbors;
    list_neighbors(s, 2, neighbors);
    if (neighbors.size() != 6)
      return false;

    auto hasRight = false;
    node right_node, left_node;

    // CHECK AND SAVE LEVEL 1 NODES
    for (auto neighbor : neighbors[n]) {
      if (!ntk.is_complemented(neighbor))
        return false;

      if (!hasRight) {
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
    for (auto l_s : neighbors[left_node]) {
      auto l_n = ntk.get_node(l_s);
      if (l_n != ntk.get_node(shared_node.first)) {
        left_s = l_s;
        break;
      }
    }

    for (auto r_s : neighbors[right_node]) {
      auto r_n = ntk.get_node(r_s);
      if (r_n != ntk.get_node(shared_node.first)) {
        right_s = r_s;
        break;
      }
    }

    // APPLY OR DISTRIBUTIVITY
    auto final_signal = ntk.create_nand(shared_node.first, ntk.create_nand(!left_s, !right_s));

    ntk.substitute_node(n, final_signal);
    return true;
  }

  /* Try the distributivity rule on node n. Return true if the network is updated. */
  bool try_distributivity(node n) {
    if (ntk.level(n) < 2 || already_visited(n, distributivity_visited_and_changed)) {
      return false;
    } else {
      distributivity_visited_and_changed.insert(std::pair<node, bool>(n, true));

      try {
        auto s = final_signals.at(n);
        return apply_distributivity(s);
      } catch (std::out_of_range& e) {
        auto modified = false;

        ntk.foreach_fanin(n, [&](signal const& s) { modified |= apply_distributivity(s); });

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
    list_neighbors(s, 3, neighbors);
    if (neighbors.size() != 7)
      return false;

    signal a, b, c, d;

    auto l1_neighbors = neighbors[n];
    signal l2_s;

    if (l1_neighbors.size() != 2)
      return false;

    // IDENTIFY D
    auto l1_n1 = ntk.get_node(l1_neighbors[0]), l1_n2 = ntk.get_node(l1_neighbors[1]);
    if (ntk.level(l1_n1) > 2 && ntk.is_complemented(l1_neighbors[0]) && ntk.is_on_critical_path(l1_n1)) {
      d = l1_neighbors[1];
      l2_s = l1_neighbors[0];
    } else if (ntk.level(l1_n2) > 2 && ntk.is_complemented(l1_neighbors[1]) && ntk.is_on_critical_path(l1_n2)) {
      d = l1_neighbors[0];
      l2_s = l1_neighbors[1];
    } else {
      return false;
    }

    // IDENTIFY C
    auto l2_n = ntk.get_node(l2_s);
    auto l2_neighbors = neighbors[l2_n];
    signal l3_s;

    if (l2_neighbors.size() != 2)
      return false;

    auto l2_n1 = ntk.get_node(l2_neighbors[0]), l2_n2 = ntk.get_node(l2_neighbors[1]);

    if (ntk.level(l2_n1) > 1 && ntk.is_complemented(l2_neighbors[0])  && ntk.is_on_critical_path(l2_n1)) {
      c = l2_neighbors[1];
      l3_s = l2_neighbors[0];
    } else if (ntk.level(l2_n2) > 1 && ntk.is_complemented(l2_neighbors[1])  && ntk.is_on_critical_path(l2_n2)) {
      c = l2_neighbors[0];
      l3_s = l2_neighbors[1];
    } else {
      return false;
    }

    // IDENTIFY A and B
    auto l3_n = ntk.get_node(l3_s);
    auto l3_neighbors = neighbors[l3_n];

    if (l3_neighbors.size() != 2)
      return false;

    auto l3_n1 = ntk.get_node(l3_neighbors[0]), l3_n2 = ntk.get_node(l3_neighbors[1]);

    if (ntk.level(l3_n1) > ntk.level(l3_n2)) {
      a = l3_neighbors[0];
      b = l3_neighbors[1];
    } else {
      a = l3_neighbors[1];
      b = l3_neighbors[0];
    }

    // APPLY DISTRIBUTIVITY ONLY IF WORTH IT
    if (ntk.level(ntk.get_node(a)) > ntk.level(ntk.get_node(d))) {
      auto final_signal = ntk.create_nand(ntk.create_nand(d, !c), ntk.create_nand(a, ntk.create_and(b, d)));

      ntk.substitute_node(n, final_signal);
      return true;
    }

    return false;
  }

  bool try_three_layer_distributivity(node n) {
    if (ntk.level(n) < 3) {
      return false;
    } else {
      try {
        auto s = final_signals.at(n);
        return apply_three_layer_distributivity(s);
      } catch (std::out_of_range& e) {
        auto modified = false;

        ntk.foreach_fanin(n, [&](signal const& s) { modified |= apply_three_layer_distributivity(s); });

        return modified;
      }
    }
  }

  void list_neighbors(signal s, size_t depth, std::unordered_map<node, std::vector<signal>>& acc) {
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

    for (int i = 0; i < neighbors.size(); ++i) {
      auto neighbor = neighbors[i];
      list_neighbors(neighbor, depth - 1, acc);
    }
  }

private:
  Ntk& ntk;

  std::unordered_map<node, signal> final_signals;
  std::unordered_map<node, bool> distributivity_visited_and_changed;
  std::unordered_map<node, std::vector<signal>> cache;
};

} // namespace detail

/* Entry point for users to call */
template <class Ntk> void aig_algebraic_rewriting(Ntk& ntk) {
  static_assert(std::is_same_v<typename Ntk::base_type, aig_network>, "Ntk is not an AIG");

  depth_view dntk{ntk};
  detail::aig_algebraic_rewriting_impl p(dntk);
  p.run();
}

} /* namespace mockturtle */