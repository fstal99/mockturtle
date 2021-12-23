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
    if (try_three_level_distributivity(n))
        return true;
    return false;
  }

  /* Try the associativity rule on node n. Return true if the network is updated. */
  bool try_associativity(node n)
  {
      /* TODO */
      
      // Varibale init. to avoid possible actions without assigned values

      uint8_t level_free=0, level_wrost=0;

      uint32_t CNT_critical = 0, CNT_free = 0;
      
      signal C_Signal, Signal_free_1, Signal_free_2;

      if (ntk.level(n) == 1)
          return false;

      if (ntk.is_on_critical_path(n)){
              
        ntk.foreach_fanin(n, [&](signal child)
        {
                if (!ntk.is_complemented(child) && ntk.is_on_critical_path(ntk.get_node(child))){
                          
                    ntk.foreach_fanin(ntk.get_node(child), [&](signal Signal_pointer)
                    {
                            if (ntk.is_on_critical_path(ntk.get_node(Signal_pointer))){
                                // Store 
                                C_Signal = Signal_pointer;
                                level_wrost = ntk.level(ntk.get_node(Signal_pointer));

                                CNT_critical++; // Count the critical path
                            }
                            else{

                                CNT_free++;
                                Signal_free_1 = Signal_pointer;
                            }
                    });
                }
                else{
                    // Store and count the non critical path 
                    Signal_free_2 = child;
                    level_free = ntk.level(ntk.get_node(child));

                    CNT_free++;
                }
        });

      }

      // Condition if is advantageous
      if (level_wrost <= level_free)
          return false;

     if (CNT_critical == 1 && CNT_free == 2 ){
        signal and_gate;
        and_gate = ntk.create_and(C_Signal, ntk.create_and(Signal_free_1, Signal_free_2));
        ntk.substitute_node(n, and_gate);       return true;
     }

     return false;
  }

  /* Try the distributivity rule on node n. Return true if the network is updated. */
  bool try_distributivity(node n)
  {

      bool flag_appl = false, flag_appl_child = false, flag_appl_child1 = false;
      bool ass_signal_CP = false, ass_signal_non_CP = false;

      uint32_t level_alfa, level_beta;
      uint32_t CNT_children = 0;


      std::vector<node> children;
      std::vector<signal> signal_beta_CP, signal_beta_non_CP;

      if (ntk.is_on_critical_path(n)){
          ntk.foreach_fanin(n, [&](signal const& signal_in_n)
              {
                  if (ntk.is_complemented(signal_in_n)){
                      node child = ntk.get_node(signal_in_n);
                      if (ntk.is_on_critical_path(child)){
                          children.push_back(child);
                          CNT_children++;
                      }
                  }
              return;
              });

          if (CNT_children == 2){

              for (auto ith_child = 0; ith_child < children.size(); ith_child++){
                  ntk.foreach_fanin(children.at(ith_child), [&](signal const& signal_in_n)
                      {
                          if (ntk.is_on_critical_path(ntk.get_node(signal_in_n))){
                              ass_signal_CP = true;
                              signal_beta_CP.push_back(signal_in_n);
                          }
                          else{
                              ass_signal_non_CP = true;
                              signal_beta_non_CP.push_back(signal_in_n);
                          }
                          return;
                  });
              }
              if (ass_signal_non_CP && ass_signal_CP) {
                  if ((signal_beta_CP.at(0) == signal_beta_CP.at(1)))
                  {
                      signal new_or = ntk.create_or(signal_beta_non_CP.at(0), signal_beta_non_CP.at(1));
                      signal node_tosub;

                      if (!ntk.is_or(n))
                          node_tosub = ntk.create_nand(signal_beta_CP.at(0), new_or);
                      else
                          node_tosub = ntk.create_and(signal_beta_CP.at(0), new_or);
                      ntk.substitute_node(n, node_tosub);
                      return true;
                  }
              }
          }

      }
  return false;
  }

 /* Try the three level distributivity rule on node n. Return true if the network is updated. */

  bool try_three_level_distributivity(node n)
  {
      
      uint8_t free_level;
      uint8_t level_gate_crit;

      bool critical_flag = false; 
      bool free_flag = false;

      signal C_path_0, C_path_1, C_path_2;
      signal Free_path_0, Free_path_1, Free_path_2;

      ntk.foreach_fanin(n, [&](signal child)
      { 
              if (ntk.is_on_critical_path(ntk.get_node(child)) && ntk.is_complemented(child)){
                  critical_flag = true;                                 //Met critical path
                  C_path_0 = child;
                  level_gate_crit = ntk.level(ntk.get_node(C_path_0));  //Needed for advantageous realization
              }
              
              else {
                  if (!ntk.is_on_critical_path(ntk.get_node(child))) {
                      free_flag = true;                                 //Met non critical path 
                      Free_path_0 = child;
                      free_level = ntk.level(ntk.get_node(Free_path_0));
                  }
              }
              
      });
     
      if ((level_gate_crit <= 2 + free_level) || !critical_flag || !free_flag ) //Basic condition to check the feasibility
          return false;
      
      if (critical_flag && free_flag)
      {
              // Flags reset
              critical_flag = false;
              free_flag = false;

              // Repeat the previous algorithm 
              ntk.foreach_fanin(ntk.get_node(C_path_0), [&](signal child_first)
              {
                  if (ntk.is_on_critical_path(ntk.get_node(child_first)) && ntk.is_complemented(child_first))
                  {
                    
                      critical_flag = true;
                      C_path_1 = child_first;
                  }
                  else if (ntk.is_complemented(child_first))
                  {
                     
                      free_flag = true;
                      Free_path_1 = child_first;
                  }
              });
      }

      else
          return false; 
 
      // Same approach on different layers
      
      if (critical_flag && free_flag)
      { 
          critical_flag = false;
          free_flag = false;

          ntk.foreach_fanin(ntk.get_node(C_path_1), [&](signal child_second)
              {
                  if (ntk.is_on_critical_path(ntk.get_node(child_second)))
                  {

                      critical_flag = true;
                      C_path_2 = child_second;
                  }
                  else
                  {

                      free_flag = true;
                      Free_path_2 = child_second;
                  }
              });
      }

      else
          return false;

      // Check to realize the optimized circuit

      if (critical_flag && free_flag)
      {
              
              signal and_new_0;
              signal and_new_1;
              signal and_new_2;
              signal nand_output;

              and_new_0 = ntk.create_and(Free_path_2, Free_path_0);

              and_new_1 = ntk.create_and(C_path_2, and_new_0);

              and_new_2 = ntk.create_and(Free_path_0, ntk.create_not(Free_path_1));

              nand_output = ntk.create_nand(ntk.create_not(and_new_1), ntk.create_not(and_new_2));

              ntk.substitute_node(n, nand_output);

              return true;
      }
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
