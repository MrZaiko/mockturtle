#include <catch.hpp>

#include <mockturtle/algorithms/aig_algebraic_rewriting.hpp>
#include <mockturtle/networks/aig.hpp>
#include <mockturtle/views/depth_view.hpp>
#include <mockturtle/algorithms/simulation.hpp>
#include <mockturtle/io/aiger_reader.hpp>
#include <mockturtle/algorithms/equivalence_checking.hpp>
#include <mockturtle/algorithms/miter.hpp>
#include <mockturtle/algorithms/functional_reduction.hpp>
#include <kitty/static_truth_table.hpp>
#include <lorina/aiger.hpp>

using namespace mockturtle;

TEST_CASE( "Simple associativity (AND)", "[aig_algebraic_rewriting]" )
{
  /* create the network */
  aig_network aig;
  static const uint32_t num_pis{4};
  std::vector<typename aig_network::signal> pis;
  for ( uint32_t i = 0; i < num_pis; ++i )
    pis.emplace_back( aig.create_pi() );

  const auto f1 = aig.create_and( pis[0], pis[1] );
  const auto f2 = aig.create_and( f1, pis[2] );
  const auto f3 = aig.create_and( f2, pis[3] );
  aig.create_po( f3 );

  /* simulate to get the output truth table(s) */
  auto tts = simulate<kitty::static_truth_table<num_pis>>( aig );

  /* call the algorithm */
  aig_algebraic_rewriting( aig );

  /* check the resulting depth */
  depth_view depth_aig{aig};
  CHECK( depth_aig.depth() == 2 );

  /* check that the output functions remain the same */
  CHECK( tts == simulate<kitty::static_truth_table<num_pis>>( aig ) );
}

TEST_CASE( "Simple associativity (OR)", "[aig_algebraic_rewriting]" )
{
  /* create the network */
  aig_network aig;
  static const uint32_t num_pis{4};
  std::vector<typename aig_network::signal> pis;
  for ( uint32_t i = 0; i < num_pis; ++i )
    pis.emplace_back( aig.create_pi() );

  const auto f1 = aig.create_or( pis[0], pis[1] );
  const auto f2 = aig.create_or( f1, pis[2] );
  const auto f3 = aig.create_or( f2, pis[3] );
  aig.create_po( f3 );

  /* simulate to get the output truth table(s) */
  auto tts = simulate<kitty::static_truth_table<num_pis>>( aig );

  /* call the algorithm */
  aig_algebraic_rewriting( aig );

  /* check the resulting depth */
  depth_view depth_aig{aig};
  CHECK( depth_aig.depth() == 2 );

  /* check that the output functions remain the same */
  CHECK( tts == simulate<kitty::static_truth_table<num_pis>>( aig ) );
}

TEST_CASE( "Simple distributivity (OR on top)", "[aig_algebraic_rewriting]" )
{
  /* create the network */
  aig_network aig;
  static const uint32_t num_pis{4};
  std::vector<typename aig_network::signal> pis;
  for ( uint32_t i = 0; i < num_pis; ++i )
    pis.emplace_back( aig.create_pi() );

  const auto g = aig.create_xor( pis[0], pis[1] );
  const auto f1 = aig.create_and( g, pis[2] );
  const auto f2 = aig.create_and( g, pis[3] );
  const auto f3 = aig.create_or( f1, f2 );
  aig.create_po( f3 );

  /* simulate to get the output truth table(s) */
  auto tts = simulate<kitty::static_truth_table<num_pis>>( aig );

  /* call the algorithm */
  aig_algebraic_rewriting( aig );

  /* check the resulting depth */
  depth_view depth_aig{aig};
  CHECK( depth_aig.depth() == 3 );

  /* check that the output functions remain the same */
  CHECK( tts == simulate<kitty::static_truth_table<num_pis>>( aig ) );
}

TEST_CASE( "Simple distributivity (AND on top)", "[aig_algebraic_rewriting]" )
{
  /* create the network */
  aig_network aig;
  static const uint32_t num_pis{4};
  std::vector<typename aig_network::signal> pis;
  for ( uint32_t i = 0; i < num_pis; ++i )
    pis.emplace_back( aig.create_pi() );

  const auto g = aig.create_xor( pis[0], pis[1] );
  const auto f1 = aig.create_or( g, pis[2] );
  const auto f2 = aig.create_or( g, pis[3] );
  const auto f3 = aig.create_and( f1, f2 );
  aig.create_po( f3 );

  /* simulate to get the output truth table(s) */
  auto tts = simulate<kitty::static_truth_table<num_pis>>( aig );

  /* call the algorithm */
  aig_algebraic_rewriting( aig );

  /* check the resulting depth */
  depth_view depth_aig{aig};
  CHECK( depth_aig.depth() == 3 );

  /* check that the output functions remain the same */
  CHECK( tts == simulate<kitty::static_truth_table<num_pis>>( aig ) );
}

TEST_CASE( "Three-layer distributivity", "[aig_algebraic_rewriting]" )
{
  /* create the network */
  aig_network aig;
  static const uint32_t num_pis{5};
  std::vector<typename aig_network::signal> pis;
  for ( uint32_t i = 0; i < num_pis; ++i )
    pis.emplace_back( aig.create_pi() );

  /* This rule is not in the pdf, but also simple: 
     ((g x2) + x3 ) x4 = (g x2 x4) + (x3 x4) = (g (x2 x4)) + (x3 x4) */
  const auto g = aig.create_xor( pis[0], pis[1] );
  const auto f1 = aig.create_and( g, pis[2] );
  const auto f2 = aig.create_or( f1, pis[3] );
  const auto f3 = aig.create_and( f2, pis[4] );
  aig.create_po( f3 );

  /* simulate to get the output truth table(s) */
  auto tts = simulate<kitty::static_truth_table<num_pis>>( aig );

  /* call the algorithm */
  aig_algebraic_rewriting( aig );

  /* check the resulting depth */
  depth_view depth_aig{aig};
  CHECK( depth_aig.depth() == 4 );

  /* check that the output functions remain the same */
  CHECK( tts == simulate<kitty::static_truth_table<num_pis>>( aig ) );
}

TEST_CASE( "Depth optimization on ISCAS benchmarks", "[aig_algebraic_rewriting]" )
{
  uint32_t benchmark_ids[11] = {17, 432, 499, 880, 1355, 1908, 2670, 3540, 5315, 6288, 7552};
  uint32_t expected_depths[11] = {3, 26, 19, 19, 25, 26, 18, 35, 34, 120, 25};

  for ( uint32_t i = 0u; i < 11; ++i )
  {
    aig_network ntk, ntk_ori;
    auto const result = lorina::read_aiger( fmt::format( "{}/c{}.aig", BENCHMARKS_PATH, benchmark_ids[i] ), aiger_reader( ntk ) );
    if ( result != lorina::return_code::success )
    {
      continue;
    }
    ntk_ori = cleanup_dangling( ntk );

    /* call the algorithm */
    aig_algebraic_rewriting( ntk );

    /* check the resulting depth */
    /* (You should already pass by implementing the rules introduced in the pdf,
        but if you have implemented more rules, better results are possible.) */
    depth_view depth_aig{ntk};
    fmt::print( "[i] On benchmark c{}.aig: Optimized depth = {} (expected at most {})\n", 
                benchmark_ids[i], depth_aig.depth(), expected_depths[i] );
    CHECK( depth_aig.depth() <= expected_depths[i] );

    /* equivalence checking */
    aig_network miter_aig = *miter<aig_network>( ntk_ori, ntk );
    functional_reduction( miter_aig );
    bool cec = *equivalence_checking( miter_aig );
    CHECK( cec == true );
  }
}
