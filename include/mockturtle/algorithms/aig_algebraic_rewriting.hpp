/*!
  \file aig_algebraic_rewriting.hpp
  \brief AIG algebraric rewriting

  EPFL CS-472 2021 Final Project Option 1
*/

#pragma once

#include "../networks/aig.hpp"
#include "../views/depth_view.hpp"
#include "../views/topo_view.hpp"

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
    : ntk( ntk )
  {
    static_assert( has_level_v<Ntk>, "Ntk does not implement depth interface." );
  }

  void run()
  {
    bool cont{true}; /* continue trying */
    while ( cont )
    {
      cont = false; /* break the loop if no updates can be made */
      ntk.foreach_gate( [&]( node n ){
        if ( try_algebraic_rules( n ) )
        {
          ntk.update_levels();
          cont = true;
        }
      });
    }
  }

private:
  /* Try various algebraic rules on node n. Return true if the network is updated. */
  bool try_algebraic_rules( node n )
  {
    if ( try_associativity( n ) )
      return true;
    if ( try_distributivity( n ) )
      return true;
    /* TODO: add more rules here... */

    return false;
  }

  /* Try the associativity rule on node n. Return true if the network is updated. */
  bool try_associativity( node n )
  {
    /* TODO */
    return false;
  }

  void list_nodes(node n, std::vector<node> swap_list, std::vector<node> remaining) {
    if (ntk.level(&n) == 0) {
      return;
    }

    ntk.foreach_fanin(n, [&] (signal const& s) {
       auto node = ntk.get_node(s);

       if (ntk.is_complemented(s)) {
         swap_list.insert(node);
         remaining.insert(node);
       } else if (ntk.level(&n) == 0) {
         swap_list.insert(node);
       } else {
         list_nodes(node, swap_list, remaining);
       }
    });

    
  }

  node swap(std::vector<node> swap_list) {
    node critical_node, final_node;
    bool has_critical = false;

    for ( auto i = 0; i < swap_list.size(); ++i ) {
      auto node = swap_list[i];
      if (ntk.is_on_critical_path(node)) {
        critical_node = node;
        has_critical = true;
      } else if (i == 0 || (i == 1 && has_critical)) {
        final_node = node;
      } else {
        final_node = ntk.get_node(ntk.create_and(ntk.make_signal(&node), ntk.make_signal(&final_node)));
      }
    }

    if (has_critical) {
      final_node = ntk.get_node(ntk.create_and(ntk.make_signal(&critical_node), ntk.make_signal(&final_node)));
    }

    return final_node;
  }



  /* Try the distributivity rule on node n. Return true if the network is updated. */
  bool try_distributivity( node n )
  {
    /* TODO */
    return false;
  }

private:
  Ntk& ntk;
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