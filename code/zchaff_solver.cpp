// *********************************************************************
// Copyright 2000-2004, Princeton University.  All rights reserved.
// By using this software the USER indicates that he or she has read,
// understood and will comply with the following:
//
// --- Princeton University hereby grants USER nonexclusive permission
// to use, copy and/or modify this software for internal, noncommercial,
// research purposes only. Any distribution, including commercial sale
// or license, of this software, copies of the software, its associated
// documentation and/or modifications of either is strictly prohibited
// without the prior consent of Princeton University.  Title to copyright
// to this software and its associated documentation shall at all times
// remain with Princeton University.  Appropriate copyright notice shall
// be placed on all software copies, and a complete copy of this notice
// shall be included in all copies of the associated documentation.
// No right is  granted to use in advertising, publicity or otherwise
// any trademark, service mark, or the name of Princeton University.
//
//
// --- This software and any associated documentation is provided "as is"
//
// PRINCETON UNIVERSITY MAKES NO REPRESENTATIONS OR WARRANTIES, EXPRESS
// OR IMPLIED, INCLUDING THOSE OF MERCHANTABILITY OR FITNESS FOR A
// PARTICULAR PURPOSE, OR THAT  USE OF THE SOFTWARE, MODIFICATIONS, OR
// ASSOCIATED DOCUMENTATION WILL NOT INFRINGE ANY PATENTS, COPYRIGHTS,
// TRADEMARKS OR OTHER INTELLECTUAL PROPERTY RIGHTS OF A THIRD PARTY.
//
// Princeton University shall not be liable under any circumstances for
// any direct, indirect, special, incidental, or consequential damages
// with respect to any claim by USER or any third party on account of
// or arising from the use, or inability to use, this software or its
// associated documentation, even if Princeton University has been advised
// of the possibility of those damages.
// ********************************************************************

// ****************************************************************************
//
//  The following code was added by Yael Weinberg and Osnal Tal
//  As a research project for the VLSI Lab of the Technion -
//  Israeli Institute of Technology.
//
//  Manipulating Decision Methods of Modern SAT Solvers
//  for Bounded Model Checking.
//
//  We added classes CVariableOrderManager and CCycle to handle the
//  decision method - the next variable to be assigned will be picked not
//  only by its score, but also by the corresponding clock cycle of the
//  logic circuit represented by the formula, and the variable type
//  (state variable, or a variable representing either a logic gate or an input).
//  The cycles are traversed in a DFS order.
// ****************************************************************************

#include <iostream>
#include <algorithm>
#include <fstream>
#include <vector>
#include <map>
#include <set>
#include <queue>

using namespace std;

#include "zchaff_solver.h"

// #define VERIFY_ON

#ifdef VERIFY_ON
ofstream verify_out("resolve_trace");
#endif


const int CVariableOrderManager::NON_STATE_VAR_CYCLE = -1;

// ****************************************************************************
//  Class CCycle Functions
// ****************************************************************************

// add_variable
// Adds the variable var to be one of the variables in the cycle.
// Happens in initialization stage only.
void CCycle::add_variable(CVariable& var) {
    pair<CVariable*, int> pair;
    pair.first = &var;
    pair.second = var.score();
    _ordered_vars.push_back(pair);
    _num_free_variables++;
}

// reset_ordered_var
// The function resets the entry in _ordered_vars for the
// variable currently iterated.
// This function is called for all the vars, and afterwards the
// array of pairs is sorted again, and we get a reset of the 
// order of the variables. 
void CCycle::reset_ordered_var(CVariable* var) {
   _ordered_vars[_ordered_vars_itr].first = var;
   _ordered_vars[_ordered_vars_itr].second = var->score();
   _ordered_vars_itr++;
}

// sort_var_score
// The function sorts the vector _ordered_vars, and updates for all the 
// variables in the cycle their new location in _ordered_vars
void CCycle::sort_var_score(void) {
  ::stable_sort(_ordered_vars.begin(), _ordered_vars.end(), cmp_var_stat);
  unsigned i = 0;
  unsigned sz = _ordered_vars.size();
  for (i = 0; i < sz; ++i)
    _ordered_vars[i].first->set_var_score_pos(i);
  _max_score_pos = 0;
}

// update_var_score
// The function updates the scores in _ordered_vars, to be the 
// scores contained in the variables pointed by _ordered_vars
void CCycle::update_var_score(void) {
  unsigned i = 0;
  unsigned sz = _ordered_vars.size();
  for (i=0; i < sz; ++i) {
    _ordered_vars[i].second = _ordered_vars[i].first->score();
  }
}

// adjust_variable_order
// The function adjusts the order of the variables that belong to this cycle. 
// The function is part of the original adjust_variable_order - and 
// is member of CVariableOrderManager and CCycle, because _ordered_vars
// is handled, and the code is adjusted to its new structure
void CCycle::adjust_variable_order(CVariable& var, int orig_score, int new_score, int bubble_step, CSolverStats* stats) {
    int pos = var.var_score_pos();
    int orig_pos = pos;
    assert(_ordered_vars[pos].first == & var);
    assert(_ordered_vars[pos].second == orig_score);
    for (pos = orig_pos ; pos >= 0; pos -= bubble_step) {
      if (_ordered_vars[pos].second >= new_score)
        break;
    }
    pos += bubble_step;
    for (bubble_step = bubble_step >> 1; bubble_step > 0;
         bubble_step = bubble_step >> 1) {
      if (pos - bubble_step >= 0 &&
          _ordered_vars[pos - bubble_step].second < new_score)
        pos -= bubble_step;
    }
    // now found the position, do a swap
    _ordered_vars[orig_pos] = _ordered_vars[pos];
    _ordered_vars[orig_pos].first->set_var_score_pos(orig_pos);
    _ordered_vars[pos].first = & var;
    _ordered_vars[pos].second = new_score;
    _ordered_vars[pos].first->set_var_score_pos(pos);
    stats->total_bubble_move += orig_pos - pos;
}

// decide_next_var
// The function is the one that CSolver calls (via CVariableOrderManager) 
// in order to decide  what will be the next variable to be assigned.
// Arguments: CSolverParameters* params - CSolver parameters (CSolver::_params)
//            CSolverStats*  stats - CSolver statistics (CSolver::_stats)
// Return value: A point to the CVariable to be assigned.
CVariable * CCycle::decide_next_var(CSolverParameters* params, CSolverStats*  stats){
    unsigned size = _ordered_vars.size() , i =_max_score_pos;
    for (; i < size; ++i) {
        CVariable & var = *_ordered_vars[i].first;
        if (var.value() == UNKNOWN && var.is_branchable()) {
             // move th max score position pointer
             _max_score_pos = i;
             // make some randomness happen
             if (--stats->current_randomness < params->decision.base_randomness)
                 stats->current_randomness = params->decision.base_randomness;
             int randomness = stats->current_randomness;
             if (randomness >= num_free_variables())
                 randomness = num_free_variables() - 1;
             int skip = rand() % (1 + randomness);
             int index = i;
             while (skip > 0) {
                 ++index;
                 if (_ordered_vars[index].first->value() == UNKNOWN && _ordered_vars[index].first->is_branchable())
                     --skip;
             }
             return _ordered_vars[index].first;
         }
     }
     return NULL;
}

// update_available_var_modifications
// The function updates (if needed) the _max_score_pos of the cycle
void CCycle::update_available_var_modifications(CVariable& var){
    if(var.var_score_pos() < _max_score_pos)
        _max_score_pos = var.var_score_pos();
}

// decay_variable_score
// The function divides by 2 the scores of the variables of
// the cycle.
void CCycle::decay_variable_score() {
  unsigned i, sz = _ordered_vars.size();
  for (i = 0; i < sz; ++i) {
    CVariable & var = *_ordered_vars[i].first;
    var.score(0) /= 2;
    var.score(1) /= 2;
  }
}


// ****************************************************************************
//  Class CVariableOrderManager Functions
// ****************************************************************************

// init
// The fucntion initiates the instance of CVariableOrderManager
void CVariableOrderManager::init(CSolver* parent) {
    _state_cycles_num = get_cycles_num(parent);
    _state_cycles.resize(_state_cycles_num);
    _cycles_order_pos = 0;

    if(_state_cycles_num > 0)
        init_cycles_order();

    init_vars_by_cycles(parent);

}

// get_cycles_num
// returns the amount of CCycle instances it holds.
unsigned int CVariableOrderManager::get_cycles_num(CSolver* parent) {
    int cycle = 0, max_cycle = -1;
    unsigned size = parent->num_variables();
    
    for (unsigned i = 1; i <= size; i++) {
        cycle = parent->variable(i).get_cycle();
        if (cycle > max_cycle)
	   max_cycle = cycle;
    }
    return max_cycle+1;
}

// init_vars_by_cycles
// The function takes all the variables stored in the class, and
// seperates them to the different cycles.
void CVariableOrderManager::init_vars_by_cycles(CSolver* parent) {
    int idx = 0;
    unsigned size = parent->num_variables();

    for (unsigned i = 1; i <= size; i++) {
        CVariable& variable = parent->variable(i);
        idx = variable.get_cycle();
        cycle(idx).add_variable(variable);
    }
}

// init_cycles_order
// The function initiates the order of the cycles that the
// instanse contains. The order is as following:
// First come all the cycles that contain state variables. 
// They are ordered in DFS order (For example, if we have 15
// cycles that contain state variables, marked 0,1,..,14,
// their order will be: 7,3,1,0,2,5,4,6,11,9,8,10,13,12,14
void CVariableOrderManager::init_cycles_order() {
    unsigned int left = 0, right = _state_cycles_num-1, index, order;
    int i;

    _cycles_decision_order.resize(_state_cycles_num);
    _cycles_position.resize(_state_cycles_num);

    for(order = 0; order < _state_cycles_num ; ++order) {
	if(right != left) {
	   index = left + (int)((right - left)/2);
	   if(index > left)
		right = index - 1;
	   else
		left = index + 1;
	}
	else {
	   index = right;
	   for(i = order; i >= 0; --i){
		if(_cycles_decision_order[i] > left){
		   left = _cycles_decision_order[i] + 1;
		   break;
		}
	   }
	   right = _state_cycles_num-1;
	   for(i = order; i >= 0; i--){
		if(_cycles_decision_order[i] > left){
		   right = _cycles_decision_order[i] - 1;
		   break;
		}
	   }
	} 
	_cycles_decision_order[order] = index;
    _cycles_position[index] = order;
   }
}

// cycle
// The function gets as input the index of a cycle,
// and returns the relevant one. (The state-variables
// are hold in an array. The non-state-variables cycle
// is stored outside the array and has the index -1).
CCycle& CVariableOrderManager::cycle(int idx) {
     // a state variable
    if (idx != NON_STATE_VAR_CYCLE) {
	return _state_cycles[idx];
     }
     else { // not a state variable
        return _non_state_vars_cycle;
     }
}

// update_var_score
// The function updates the score of all the variables
// in the system, by calling CCycle::update_var_score  
// for all the cycles.
void CVariableOrderManager::update_var_score(void) {
    unsigned i=0;
    for (i=0; i<_state_cycles_num; i++) {
        _state_cycles[i].update_var_score();
    }
    _non_state_vars_cycle.update_var_score();
}

// sort_var_score
// The function sorts the score of all the variables
// in the system, each one in its cycle, by calling 
// CCycle::sort_var_score for all the cycles.
void CVariableOrderManager::sort_var_score(void) {
    unsigned i=0;
    for (i=0; i<_state_cycles_num; i++) {
        _state_cycles[i].sort_var_score();
    }
    _non_state_vars_cycle.sort_var_score();
    _cycles_order_pos = 0;
}

// reset_ordered_var
// The function calls CCycle::reset_ordered_var of the 
// cycle that the argument var belongs to.
void CVariableOrderManager::reset_ordered_var(CVariable* var) {
  cycle(var->get_cycle()).reset_ordered_var(var);
}

// reset_ordered_var_itr
// The function resets the ordered variables itrerators of
// all the cycles, by calling CCycle::reset_ordered_var_itr
// for all the cycles.
void  CVariableOrderManager::reset_ordered_var_itr(void)
{
    unsigned i=0;
    for (i=0; i<_state_cycles_num; i++) {
        _state_cycles[i].reset_ordered_var_itr();
    }
    _non_state_vars_cycle.reset_ordered_var_itr();
}

// decrease_num_free_variables
// The function decreases the number of free variables counter
// of the cycle that the argument var belongs to.
void CVariableOrderManager::decrease_num_free_variables(CVariable& var) {
    int idx = var.get_cycle();
     --(cycle(idx).num_free_variables());
}

// increase_num_free_variables
// The function increases the number of free variables counter
// of the cycle that the argument var belongs to. 
void CVariableOrderManager::increase_num_free_variables(CVariable& var) {
     int idx = var.get_cycle();
     ++(cycle(idx).num_free_variables());
}

// adjust_variable_order
// The function adjusts the variables order in the cycle
// that the argument var belongs to. 
// The function is part of the original adjust_variable_order - and 
// is member of CVariableOrderManager and CCycle, because _ordered_vars
// is handled, and the code is adjusted to its new structure
void CVariableOrderManager::adjust_variable_order(CVariable& var, int orig_score, int new_score, int bubble_step, CSolverStats* stats) {
    int idx = var.get_cycle();
    cycle(idx).adjust_variable_order(var, orig_score, new_score, bubble_step, stats);
}

// decide_next_var
// The function is the one that CSolver calls in order to decide 
// what will be the next variable to be assigned.
// Arguments: CSolverParameters* params - CSolver parameters (CSolver::_params)
//            CSolverStats*  stats - CSolver statistics (CSolver::_stats)
// Return value: A point to the CVariable to be assigned.
CVariable * CVariableOrderManager::decide_next_var(CSolverParameters* params, CSolverStats*  stats){
    for (unsigned i = _cycles_order_pos; i < _state_cycles_num; ++i) {
        CCycle& cycle = _state_cycles[_cycles_decision_order[i]];
        if(cycle.num_free_variables() > 0) {
           _cycles_order_pos = i;
           return cycle.decide_next_var(params, stats);
        }
    }
    _cycles_order_pos = _state_cycles_num; //to avoid re-entering the loop
    return _non_state_vars_cycle.decide_next_var(params, stats);
}

// decay_variable_score
// The function decays the score of the variables of
// the currently manipulated cycle.
void CVariableOrderManager::decay_variable_score() {
    cycle(_cycles_order_pos).decay_variable_score();
}

// update_available_var_modifications
// The function updates (if needed) the _max_score_pos of the cycle that
// the argument var belongs to, by calling CCycle::update_available_var_modifications
// Also, if needed the function updates _cycles_order_pos which points to 
// the cycle which is most front in the line in the order of cycles, 
// and that not all of its variables are assigned.
void CVariableOrderManager::update_available_var_modifications(CVariable& var) {
    int cycle_idx = var.get_cycle();
    cycle(cycle_idx).update_available_var_modifications(var);
    if(cycle_idx != NON_STATE_VAR_CYCLE){
        unsigned int position = _cycles_position[cycle_idx];
        if(position < _cycles_order_pos)
             _cycles_order_pos = position;
    }
}

// ****************************************************************************
//
//       Original ZChaff code starts here, with addition calls to
//       CVariableOrderManager methods.
//
// ****************************************************************************


// ****************************************************************************
//  Class CSolver Functions
// ****************************************************************************

void CSolver::re_init_stats(void) {
  _stats.is_mem_out           = false;
  _stats.outcome              = UNDETERMINED;
  _stats.next_restart         = _params.restart.first_restart;
  _stats.restart_incr         = _params.restart.backtrack_incr;
  _stats.next_cls_deletion    = _params.cls_deletion.interval;
  _stats.next_var_score_decay = _params.decision.decay_period;
  _stats.current_randomness   = _params.decision.base_randomness;

  _stats.total_bubble_move            = 0;
  _stats.num_decisions                = 0;
  _stats.num_decisions_stack_conf     = 0;
  _stats.num_decisions_vsids          = 0;
  _stats.num_decisions_shrinking      = 0;
  _stats.num_backtracks               = 0;
  _stats.max_dlevel                   = 0;
  _stats.num_implications             = 0;
  _stats.num_restarts                 = 0;
  _stats.num_del_orig_cls             = 0;
  _stats.num_shrinkings               = 0;
  _stats.start_cpu_time               = get_cpu_time();
  _stats.finish_cpu_time              = 0;
  _stats.random_seed                  = 0;
}

void CSolver::init_stats(void) {
  re_init_stats();

  _stats.been_reset                   = true;
  _stats.num_free_variables           = 0;
  _stats.num_free_branch_vars         = 0;
}

void CSolver::init_parameters(void) {
  _params.verbosity                           = 0;
  _params.time_limit                          = 3600 * 24;  // a day
  _params.shrinking.size                      = 95;
  _params.shrinking.enable                    = true;
  _params.shrinking.upper_bound               = 800;
  _params.shrinking.lower_bound               = 600;
  _params.shrinking.upper_delta               = -5;
  _params.shrinking.lower_delta               = 10;
  _params.shrinking.window_width              = 20;
  _params.shrinking.bound_update_frequency    = 20;

  _params.decision.base_randomness            = 0;
  _params.decision.decay_period               = 40;
  _params.decision.bubble_init_step           = 0x400;

  _params.cls_deletion.enable                 = true ;
  _params.cls_deletion.head_activity          = 500;
  _params.cls_deletion.tail_activity          = 10;
  _params.cls_deletion.head_num_lits          = 6;
  _params.cls_deletion.tail_num_lits          = 45;
  _params.cls_deletion.tail_vs_head           = 16;
  _params.cls_deletion.interval               = 600;

  _params.restart.enable                      = true;
  _params.restart.interval                    = 700;
  _params.restart.first_restart               = 7000;
  _params.restart.backtrack_incr              = 700;
}

CSolver::CSolver(void) {
  init_parameters();
  init_stats();
  _dlevel                       = 0;
  _force_terminate              = false;
  _implication_id               = 0;
  _num_marked                   = 0;
  _num_in_new_cl                = 0;
  _outside_constraint_hook      = NULL;
  _sat_hook                     = NULL;
}

CSolver::~CSolver(void) {
  while (!_assignment_stack.empty()) {
    delete _assignment_stack.back();
    _assignment_stack.pop_back();
  }
}

void CSolver::set_time_limit(float t) {
  _params.time_limit = t;
}

float CSolver::elapsed_cpu_time(void) {
  return get_cpu_time() - _stats.start_cpu_time;
}

float CSolver::cpu_run_time(void) {
  return (_stats.finish_cpu_time - _stats.start_cpu_time);
}

void CSolver::set_variable_number(int n) {
  assert(num_variables() == 0);
  CDatabase::set_variable_number(n);
  _stats.num_free_variables = num_variables();
  while (_assignment_stack.size() <= num_variables())
    _assignment_stack.push_back(new vector<int>);
  assert(_assignment_stack.size() == num_variables() + 1);
}

void CSolver::set_cycle_idx(vector<pair<int, int> >& variables_cycles) {
  int i=0, size=variables_cycles.size();
  for (i=0; i<size; i++) {
    int f = variables_cycles[i].first;
    int s = variables_cycles[i].second;
    variable(f).set_cycle(s);
  }
}

int CSolver::add_variable(void) {
  int num = CDatabase::add_variable();
  ++_stats.num_free_variables;
  while (_assignment_stack.size() <= num_variables())
    _assignment_stack.push_back(new vector<int>);
  assert(_assignment_stack.size() == num_variables() + 1);
  return num;
}

void CSolver::set_mem_limit(int s) {
  CDatabase::set_mem_limit(s);
}

void CSolver::set_randomness(int n) {
  _params.decision.base_randomness = n;
}

void CSolver::set_random_seed(int seed) {
  srand(seed);
}

void CSolver::enable_cls_deletion(bool allow) {
  _params.cls_deletion.enable = allow;
}

void CSolver::add_hook(HookFunPtrT fun, int interval) {
  pair<HookFunPtrT, int> a(fun, interval);
  _hooks.push_back(pair<int, pair<HookFunPtrT, int> > (0, a));
}

void CSolver::run_periodic_functions(void) {
  // a. restart
  if (_params.restart.enable && _stats.num_backtracks > _stats.next_restart &&
      _shrinking_cls.empty()) {
    _stats.next_restart = _stats.num_backtracks + _stats.restart_incr;
    delete_unrelevant_clauses();
    restart();
    if (_stats.num_restarts % 5 == 1)
      compact_lit_pool();
    cout << "\rDecision: " << _assignment_stack[0]->size() << "/"
         <<num_variables() << "\tTime: " << get_cpu_time() -
           _stats.start_cpu_time << "/" << _params.time_limit << flush;
  }

  // b. decay variable score
  if (_stats.num_backtracks > _stats.next_var_score_decay) {
    _stats.next_var_score_decay = _stats.num_backtracks +
                                  _params.decision.decay_period;
    decay_variable_score();
  }

  // c. run hook functions
  for (unsigned i = 0; i< _hooks.size(); ++i) {
    pair<int, pair<HookFunPtrT, int> > & hook = _hooks[i];
    if (_stats.num_decisions >= hook.first) {
      hook.first += hook.second.second;
      hook.second.first((void *) this);
    }
  }
}

void CSolver::init_solve(void) {
  CDatabase::init_stats();
  re_init_stats();
  _stats.been_reset = false;

  assert(_conflicts.empty());
  assert(_conflict_lits.empty());
  assert(_num_marked == 0);
  assert(_num_in_new_cl == 0);
  assert(_dlevel == 0);

  for (unsigned i = 0, sz = variables()->size(); i < sz; ++i) {
    variable(i).score(0) = variable(i).lits_count(0);
    variable(i).score(1) = variable(i).lits_count(1);
  }
   init_variable_order_manager();

  set_random_seed(_stats.random_seed);

  top_unsat_cls = clauses()->end();
  --top_unsat_cls;

  _stats.shrinking_benefit = 0;
  _shrinking_cls.clear();
  _stats.shrinking_cls_length = 0;
}

void CSolver::init_variable_order_manager(void)
{
   _variable_order_manager.init(this);
   update_sort_var_score();
}

void CSolver::set_var_value(int v, int value, ClauseIdx ante, int dl) {
    assert(value == 0 || value == 1);
    CVariable & var = variable(v);
    assert(var.value() == UNKNOWN);
    assert(dl == dlevel());

    var.set_dlevel(dl);
    var.set_value(value);
    var.antecedent() = ante;
    var.assgn_stack_pos() = _assignment_stack[dl]->size();
    _assignment_stack[dl]->push_back(v * 2 + !value);
    set_var_value_BCP(v, value);

    ++_stats.num_implications ;
    if (var.is_branchable()) {
        --num_free_variables();
        _variable_order_manager.decrease_num_free_variables(var);
    }
}

void CSolver::set_var_value_BCP(int v, int value) {
  vector<CLitPoolElement *> & watchs = variable(v).watched(value);
  for (vector <CLitPoolElement *>::iterator itr = watchs.begin();
       itr != watchs.end(); ++itr) {
    ClauseIdx cl_idx;
    CLitPoolElement * other_watched = *itr;
    CLitPoolElement * watched = *itr;
    int dir = watched->direction();
    CLitPoolElement * ptr = watched;
    while (true) {
      ptr += dir;
      if (ptr->val() <= 0) {  // reached one end of the clause
        if (dir == 1)  // reached the right end, i.e. spacing element is cl_id
          cl_idx = ptr->get_clause_index();
        if (dir == watched->direction()) {  // we haven't go both directions.
          ptr = watched;
          dir = -dir;                     // change direction, go the other way
          continue;
        }
        // otherwise, we have already go through the whole clause
        int the_value = literal_value(*other_watched);
        if (the_value == 0)  // a conflict
          _conflicts.push_back(cl_idx);
        else if (the_value != 1)  // i.e. unknown
          queue_implication(other_watched->s_var(), cl_idx);
        break;
      }
      if (ptr->is_watched()) {  // literal is the other watched lit, skip it.
        other_watched = ptr;
        continue;
      }
      if (literal_value(*ptr) == 0)  // literal value is 0, keep going
        continue;
      // now the literal's value is either 1 or unknown, watch it instead
      int v1 = ptr->var_index();
      int sign = ptr->var_sign();
      variable(v1).watched(sign).push_back(ptr);
      ptr->set_watch(dir);
      // remove the original watched literal from watched list
      watched->unwatch();
      *itr = watchs.back();  // copy the last element in it's place
      watchs.pop_back();     // remove the last element
      --itr;                 // do this so with don't skip one during traversal
      break;
    }
  }
}

void CSolver::unset_var_value(int v) {
  if (v == 0)
    return;
  CVariable & var = variable(v);
  var.set_value(UNKNOWN);
  var.set_antecedent(NULL_CLAUSE);
  var.set_dlevel(-1);
  var.assgn_stack_pos() = -1;

  if (var.is_branchable()) {
    ++num_free_variables();
    _variable_order_manager.increase_num_free_variables(var);
    _variable_order_manager.update_available_var_modifications(var);
  }
}

void CSolver::dump_assignment_stack(ostream & os ) {
  os << "Assignment Stack:  ";
  for (int i = 0; i <= dlevel(); ++i) {
    os << "(" <<i << ":";
    for (unsigned j = 0; j < (*_assignment_stack[i]).size(); ++j) {
      os << ((*_assignment_stack[i])[j]&0x1?"-":"+")
         << ((*_assignment_stack[i])[j] >> 1) << " ";
    }
    os << ") " << endl;
  }
  os << endl;
}

void CSolver::dump_implication_queue(ostream & os) {
  _implication_queue.dump(os);
}

void CSolver::delete_clause_group(int gid) {
  assert(is_gid_allocated(gid));

  if (_stats.been_reset == false)
    reset();  // if delete some clause, then implication queue are invalidated

  for (vector<CClause>::iterator itr = clauses()->begin();
       itr != clauses()->end(); ++itr) {
    CClause & cl = *itr;
    if (cl.status() != DELETED_CL) {
      if (cl.gid(gid) == true) {
        mark_clause_deleted(cl);
      }
    }
  }

  // delete the index from variables
  for (vector<CVariable>::iterator itr = variables()->begin();
         itr != variables()->end(); ++itr) {
    for (unsigned i = 0; i < 2; ++i) {  // for each phase
      // delete the lit index from the vars
#ifdef KEEP_LIT_CLAUSES
      vector<ClauseIdx> & lit_clauses = (*itr).lit_clause(i);
      for (vector<ClauseIdx>::iterator itr1 = lit_clauses.begin();
           itr1 != lit_clauses.end(); ++itr1) {
        if (clause(*itr1).status() == DELETED_CL) {
          *itr1 = lit_clauses.back();
          lit_clauses.pop_back();
          --itr1;
        }
      }
#endif
      // delete the watched index from the vars
      vector<CLitPoolElement *> & watched = (*itr).watched(i);
      for (vector<CLitPoolElement *>::iterator itr1 = watched.begin();
           itr1 != watched.end(); ++itr1) {
        if ((*itr1)->val() <= 0) {
          *itr1 = watched.back();
          watched.pop_back();
          --itr1;
        }
      }
    }
  }
  free_gid(gid);
}

void CSolver::reset(void) {
  if (_stats.been_reset)
    return;
  if (num_variables() == 0)
    return;
  back_track(0);
  _conflicts.clear();
  while (!_implication_queue.empty())
    _implication_queue.pop();

  _stats.outcome = UNDETERMINED;
  _stats.been_reset = true;
}

void CSolver::delete_unrelevant_clauses(void) {
  unsigned original_del_cls = num_deleted_clauses();
  int num_conf_cls = num_clauses() - init_num_clauses() + num_del_orig_cls();
  int head_count = num_conf_cls / _params.cls_deletion.tail_vs_head;
  int count = 0;
  for (vector<CClause>::iterator itr = clauses()->begin();
                                 itr != clauses()->end() - 1; ++itr) {
    CClause & cl = *itr;
    if (cl.status() != CONFLICT_CL) {
      continue;
    }
    bool cls_sat_at_dl_0 = false;
    for (int i = 0, sz = cl.num_lits(); i < sz; ++i) {
      if (literal_value(cl.literal(i)) == 1 &&
          variable(cl.literal(i).var_index()).dlevel() == 0) {
        cls_sat_at_dl_0 = true;
        break;
      }
    }
    if (cls_sat_at_dl_0) {
      int val_0_lits = 0, val_1_lits = 0, unknown_lits = 0;
      for (unsigned i = 0; i < cl.num_lits(); ++i) {
        int lit_value = literal_value(cl.literal(i));
        if (lit_value == 0)
          ++val_0_lits;
        if (lit_value == 1)
          ++val_1_lits;
        if (lit_value == UNKNOWN)
          ++unknown_lits;
        if (unknown_lits + val_1_lits > 1) {
          mark_clause_deleted(cl);
          break;
        }
      }
      continue;
    }

    count++;
    int max_activity = _params.cls_deletion.head_activity -
                       (_params.cls_deletion.head_activity -
                        _params.cls_deletion.tail_activity) *
                       count/num_conf_cls;
    int max_conf_cls_size;

    if (head_count > 0) {
      max_conf_cls_size = _params.cls_deletion.head_num_lits;
      --head_count;
    } else {
      max_conf_cls_size = _params.cls_deletion.tail_num_lits;
    }

    if (cl.activity() > max_activity)
      continue;

    int val_0_lits = 0, val_1_lits = 0, unknown_lits = 0, lit_value;
    for (unsigned i = 0; i < cl.num_lits(); ++i) {
      lit_value = literal_value(cl.literal(i));
      if (lit_value == 0)
        ++val_0_lits;
      else if (lit_value == 1)
        ++val_1_lits;
      else
        ++unknown_lits;
      if ((unknown_lits > max_conf_cls_size)) {
        mark_clause_deleted(cl);
        break;
      }
    }
  }

  // if none were recently marked for deletion...
  if (original_del_cls == num_deleted_clauses())
    return;

  // delete the index from variables
  for (vector<CVariable>::iterator itr = variables()->begin();
       itr != variables()->end(); ++itr) {
    for (unsigned i = 0; i < 2; ++i) {  // for each phase
      // delete the lit index from the vars
#ifdef KEEP_LIT_CLAUSES
      vector<ClauseIdx> & lit_clauses = (*itr).lit_clause(i);
      for (vector<ClauseIdx>::iterator itr1 = lit_clauses.begin();
           itr1 != lit_clauses.end(); ++itr1) {
        if (clause(*itr1).status() == DELETED_CL) {
          *itr1 = lit_clauses.back();
          lit_clauses.pop_back();
          --itr1;
        }
      }
#endif
      // delete the watched index from the vars
      vector<CLitPoolElement *> & watched = (*itr).watched(i);
      for (vector<CLitPoolElement *>::iterator itr1 = watched.begin();
           itr1 != watched.end(); ++itr1) {
        if ((*itr1)->val() <= 0) {
          *itr1 = watched.back();
          watched.pop_back();
          --itr1;
        }
      }
    }
  }

  for (unsigned i = 1, sz = variables()->size(); i < sz; ++i) {
    if (variable(i).dlevel() != 0) {
      variable(i).score(0) = variable(i).lits_count(0);
      variable(i).score(1) = variable(i).lits_count(1);
      if (variable(i).lits_count(0) == 0 && variable(i).value() == UNKNOWN) {
        queue_implication(i * 2 + 1, NULL_CLAUSE);
      }
      else if (variable(i).lits_count(1) == 0 &&
               variable(i).value() == UNKNOWN) {
        queue_implication(i * 2, NULL_CLAUSE);
      }
    } else {
      variable(i).score(0) = 0;
      variable(i).score(1) = 0;
    }
  }
  update_sort_var_score();
}

// update_sort_var_score
// The function resets and sorts from beginning the variables
// in the system. Each cycle is sorted independetly from the 
// other cycles. 
void CSolver::update_sort_var_score(void)
{
  _variable_order_manager.reset_ordered_var_itr();
  for (unsigned i = 1, sz = variables()->size(); i < sz; ++i) {
     _variable_order_manager.reset_ordered_var(& variable(i));
  }
  _variable_order_manager.sort_var_score();
}


bool CSolver::time_out(void) {
  return (get_cpu_time() - _stats.start_cpu_time> _params.time_limit);
}


void CSolver::adjust_variable_order(int * lits, int n_lits) {
  // note lits are signed vars, not CLitPoolElements
  int bubble_step = _params.decision.bubble_init_step;
  for (int i = 0; i < n_lits; ++i) {
    int var_idx = lits[i] >> 1;
    CVariable & var = variable(var_idx);
    assert(var.value() != UNKNOWN);
    int orig_score = var.score();
    ++variable(var_idx).score(lits[i] & 0x1);
    int new_score = var.score();
    if (orig_score == new_score)
      continue;

    _variable_order_manager.adjust_variable_order(var, orig_score, new_score, bubble_step, &_stats);
  }
}

void CSolver::decay_variable_score(void) {
  _variable_order_manager.decay_variable_score();
  _variable_order_manager.update_var_score();
}

bool CSolver::decide_next_branch(void) {
  if (dlevel() > 0)
    assert(_assignment_stack[dlevel()]->size() > 0);
  if (!_implication_queue.empty()) {
    // some hook function did a decision, so skip my own decision making.
    // if the front of implication queue is 0, that means it's finished
    // because var index start from 1, so 2 *vid + sign won't be 0.
    // else it's a valid decision.
    return (_implication_queue.front().lit != 0);
  }
  int s_var = 0;
  if (_params.shrinking.enable) {
    while (!_shrinking_cls.empty()) {
      s_var = _shrinking_cls.begin()->second;
      _shrinking_cls.erase(_shrinking_cls.begin());
      if (variable(s_var >> 1).value() == UNKNOWN) {
        _stats.num_decisions++;
        _stats.num_decisions_shrinking++;
        ++dlevel();
        queue_implication(s_var ^ 0x1, NULL_CLAUSE);
        return true;
      }
    }
  }

  if (_outside_constraint_hook != NULL)
     _outside_constraint_hook(this);

  if (!_implication_queue.empty())
     return (_implication_queue.front().lit != 0);

  ++_stats.num_decisions;
  // the total counter of free variables (for all the cycles)
  if (num_free_variables() == 0)  // no more free vars
     return false;

  bool cls_sat = true;
  int i, sz, var_idx, score, max_score = -1;

  for (; top_unsat_cls->status() != ORIGINAL_CL; --top_unsat_cls) {
    CClause &cl=*top_unsat_cls;
    if (cl.status() != CONFLICT_CL)
      continue;
    cls_sat = false;
    if (cl.sat_lit_idx() < (int)cl.num_lits() &&
        literal_value(cl.literal(cl.sat_lit_idx())) == 1)
      cls_sat = true;
    if (!cls_sat) {
      max_score = -1;
      for (i = 0, sz = cl.num_lits(); i < sz; ++i) {
        var_idx = cl.literal(i).var_index();
        if (literal_value(cl.literal(i)) == 1) {
          cls_sat = true;
          cl.sat_lit_idx() = i;
          break;
        }
        else if (variable(var_idx).value() == UNKNOWN) {
          score = variable(var_idx).score();
          if (score > max_score) {
            max_score = score;
            s_var = var_idx * 2;
          }
        }
      }
    }
    if (!cls_sat)
      break;
  }
  if (!cls_sat && max_score != -1) {
    ++dlevel();
    if (dlevel() > _stats.max_dlevel)
      _stats.max_dlevel = dlevel();
    CVariable& v = variable(s_var >> 1);
    if (v.score(0) < v.score(1))
      s_var += 1;
    else if (v.score(0) == v.score(1)) {
      if (v.two_lits_count(0) > v.two_lits_count(1))
        s_var+=1;
      else if (v.two_lits_count(0) == v.two_lits_count(1))
        s_var+=rand()%2;
    }
    assert(s_var >= 2);
    queue_implication(s_var, NULL_CLAUSE);
    ++_stats.num_decisions_stack_conf;
    return true;
  }
   //call BMC decision method
   // let _variable_order_manager decide which is the next variable to
   // be assigned. It will choose it from currently manipulated cycle. A pointer to 
   // the chosen variable will be returned.
   CVariable * ptr = _variable_order_manager.decide_next_var(&_params, &_stats);
   assert(ptr != NULL);
   assert(ptr->value() == UNKNOWN && ptr->is_branchable());
   int sign = 0;
   if (ptr->score(0) < ptr->score(1))
      sign += 1;
   else if (ptr->score(0) == ptr->score(1)) {
     if (ptr->two_lits_count(0) > ptr->two_lits_count(1))
       sign += 1;
     else if (ptr->two_lits_count(0) == ptr->two_lits_count(1))
       sign += rand() % 2;
   }
   int var_index = ptr - &(*variables()->begin());
   s_var = var_index + var_index + sign;


  assert(s_var >= 2);  // there must be a free var somewhere
  ++dlevel();
  if (dlevel() > _stats.max_dlevel)
    _stats.max_dlevel = dlevel();
  ++_stats.num_decisions_vsids;
  _implication_id = 0;
  queue_implication(s_var, NULL_CLAUSE);

  return true;
}


int CSolver::preprocess(void) {
  assert(dlevel() == 0);

  // 1. detect all the unused variables
  vector<int> un_used;
  for (unsigned i = 1, sz = variables()->size(); i < sz; ++i) {
    CVariable & v = variable(i);
    if (v.lits_count(0) == 0 && v.lits_count(1) == 0) {
      un_used.push_back(i);
      queue_implication(i+i, NULL_CLAUSE);
      int r = deduce();
      assert(r == NO_CONFLICT);
    }
  }
  if (_params.verbosity > 1 && un_used.size() > 0) {
    cout << un_used.size() << " Variables are defined but not used " << endl;
    if (_params.verbosity > 2) {
      for (unsigned i = 0; i< un_used.size(); ++i)
         cout << un_used[i] << " ";
      cout << endl;
    }
  }

  // 2. detect all variables with only one phase occuring (i.e. pure literals)
  vector<int> uni_phased;
  for (unsigned i = 1, sz = variables()->size(); i < sz; ++i) {
    CVariable & v = variable(i);
    if (v.value() != UNKNOWN)
      continue;
    if (v.lits_count(0) == 0) {  // no positive phased lits.
      queue_implication(i+i+1, NULL_CLAUSE);
      uni_phased.push_back(-i);
    }
    else if (v.lits_count(1) == 0) {  // no negative phased lits.
      queue_implication(i+i, NULL_CLAUSE);
      uni_phased.push_back(i);
    }
  }
  if (_params.verbosity > 1 && uni_phased.size() > 0) {
    cout << uni_phased.size() << " Variables only appear in one phase." <<endl;
    if (_params.verbosity > 2) {
      for (unsigned i = 0; i< uni_phased.size(); ++i)
        cout << uni_phased[i] << " ";
      cout <<endl;
    }
  }

  // 3. Unit clauses
  for (unsigned i = 0, sz = clauses()->size(); i < sz; ++i) {
    if (clause(i).status() != DELETED_CL &&
        clause(i).num_lits() == 1 &&
        variable(clause(i).literal(0).var_index()).value() == UNKNOWN)
      queue_implication(clause(i).literal(0).s_var(), i);
  }

  if (deduce() == CONFLICT) {
    cout << " CONFLICT during preprocess " <<endl;
#ifdef VERIFY_ON
    for (unsigned i = 1; i < variables()->size(); ++i) {
      if (variable(i).value() != UNKNOWN) {
        assert(variable(i).dlevel() <= 0);
        int ante = variable(i).antecedent();
        int ante_id = 0;
        if (ante >= 0) {
          ante_id = clause(ante).id();
          verify_out << "VAR: " << i
                     << " L: " << variable(i).assgn_stack_pos()
                     << " V: " << variable(i).value()
                     << " A: " << ante_id
                     << " Lits:";
          for (unsigned j = 0; j < clause(ante).num_lits(); ++j)
            verify_out <<" " <<  clause(ante).literal(j).s_var();
          verify_out << endl;
         }
       }
    }
    verify_out << "CONF: " << clause(_conflicts[0]).id() << " ==";
    for (unsigned i = 0; i < clause(_conflicts[0]).num_lits(); ++i) {
      int svar = clause(_conflicts[0]).literal(i).s_var();
      verify_out << " " << svar;
    }
    verify_out << endl;
#endif
    return CONFLICT;
  }
  if (_params.verbosity > 1) {
    cout << _assignment_stack[0]->size() << " vars set during preprocess; "
         << endl;
  }
  return NO_CONFLICT;
}

void CSolver::mark_var_unbranchable(int vid) {
  if (variable(vid).is_branchable()) {
    variable(vid).disable_branch();
    if (variable(vid).value() == UNKNOWN) {
      --num_free_variables();
      _variable_order_manager.decrease_num_free_variables(variable(vid));
    }
  }
}


void CSolver::mark_var_branchable(int vid) {
  CVariable & var = variable(vid);
  if (!var.is_branchable()) {
    var.enable_branch();
    if (var.value() == UNKNOWN) {
      ++num_free_variables();
      _variable_order_manager.increase_num_free_variables(variable(vid));
     _variable_order_manager.update_available_var_modifications(var);
    }
  }
}

ClauseIdx CSolver::add_orig_clause(int * lits, int n_lits, int gid) {
  int cid = add_clause_with_gid(lits, n_lits, gid);
  if (cid >= 0) {
    clause(cid).set_status(ORIGINAL_CL);
    clause(cid).activity() = 0;
  }
  return cid;
}

ClauseIdx CSolver::add_clause_with_gid(int * lits, int n_lits, int gid) {
  unsigned gflag;
  if (gid == PERMANENT_GID )
    gflag = 0;
  else if (gid == VOLATILE_GID) {
    gflag = (~0x0);
  } else {
    assert(gid <= WORD_WIDTH && gid > 0);
    gflag = (1 << (gid- 1));
  }
  ClauseIdx cid = add_clause(lits, n_lits, gflag);
  if (cid < 0) {
    _stats.is_mem_out = true;
    _stats.outcome = MEM_OUT;
  }
  return cid;
}

ClauseIdx CSolver::add_conflict_clause(int * lits, int n_lits, int gflag) {
  ClauseIdx cid = add_clause(lits, n_lits, gflag);
  if (cid >= 0) {
    clause(cid).set_status(CONFLICT_CL);
    clause(cid).activity() = 0;
  } else {
    _stats.is_mem_out = true;
    _stats.outcome = MEM_OUT;
  }
  return cid;
}

void CSolver::real_solve(void) {
  while (_stats.outcome == UNDETERMINED) {
    run_periodic_functions();
    if (decide_next_branch()) {
      while (deduce() == CONFLICT) {
        int blevel;
        blevel = analyze_conflicts();
        if (blevel < 0) {
          _stats.outcome = UNSATISFIABLE;
          return;
        }
      }
    } else {
      if (_sat_hook != NULL && _sat_hook(this))
        continue;
      _stats.outcome = SATISFIABLE;
      return;
    }
    if (time_out()) {
      _stats.outcome = TIME_OUT;
      return;
    }
    if (_force_terminate) {
      _stats.outcome = ABORTED;
      return;
    }
    if (_stats.is_mem_out) {
      _stats.outcome = MEM_OUT;
       return;
    }
  }
}

int CSolver::solve(void) {
  if (_stats.outcome == UNDETERMINED) {
    init_solve();

    if (preprocess() == CONFLICT)
      _stats.outcome = UNSATISFIABLE;
    else  // the real search
      real_solve();
    cout << endl;
    _stats.finish_cpu_time = get_cpu_time();
  }
  return _stats.outcome;
}

void CSolver::back_track(int blevel) {
  assert(blevel <= dlevel());
  for (int i = dlevel(); i >= blevel; --i) {
    vector<int> & assignments = *_assignment_stack[i];
    for (int j = assignments.size() - 1 ; j >= 0; --j)
      unset_var_value(assignments[j]>>1);
    assignments.clear();
  }
  dlevel() = blevel - 1;
  if (dlevel() < 0 )
    dlevel() = 0;
  ++_stats.num_backtracks;
}

int CSolver::deduce(void) {
  while (!_implication_queue.empty()) {
    const CImplication & imp = _implication_queue.front();
    int lit = imp.lit;
    int vid = lit>>1;
    ClauseIdx cl = imp.antecedent;
    _implication_queue.pop();
    CVariable & var = variable(vid);
    if (var.value() == UNKNOWN) {  // an implication
      set_var_value(vid, !(lit & 0x1), cl, dlevel());
    }
    else if (var.value() == (unsigned)(lit & 0x1)) {
      // a conflict
      // note: literal & 0x1 == 1 means the literal is in negative phase
      // when a conflict occure at not current dlevel, we need to backtrack
      // to resolve the problem.
      // conflict analysis will only work if the conflict occure at
      // the top level (current dlevel)
      _conflicts.push_back(cl);
      break;
    } else {
      // so the variable have been assigned before
      // update its antecedent with a shorter one
      if (var.antecedent() != NULL_CLAUSE &&
          clause(cl).num_lits() < clause(var.antecedent()).num_lits())
        var.antecedent() = cl;
      assert(var.dlevel() <= dlevel());
    }
  }
  // if loop exited because of a conflict, we need to clean implication queue
  while (!_implication_queue.empty())
    _implication_queue.pop();
  return (_conflicts.size() ? CONFLICT : NO_CONFLICT);
}

void CSolver::verify_integrity(void) {
  for (unsigned i = 1; i < variables()->size(); ++i) {
    if (variable(i).value() != UNKNOWN) {
      int pos = variable(i).assgn_stack_pos();
      int value = variable(i).value();
      int dlevel = variable(i).dlevel();
      assert((*_assignment_stack[dlevel])[pos] == (int) (i+i+1-value));
    }
  }
  for (unsigned i = 0; i < clauses()->size(); ++i) {
    if (clause(i).status() == DELETED_CL)
      continue;
    CClause & cl = clause(i);
    int num_0 = 0;
    int num_1 = 0;
    int num_unknown = 0;
    int watched[2];
    int watch_index = 0;
    watched[1] = watched[0] = 0;
    for (unsigned j = 0; j < cl.num_lits(); ++j) {
      CLitPoolElement lit = cl.literal(j);
      int vid = lit.var_index();
      if (variable(vid).value() == UNKNOWN) {
        ++num_unknown;
      } else {
        if (literal_value(lit) == 0)
          ++num_0;
        else
          ++num_1;
      }
      if (lit.is_watched()) {
        watched[watch_index] = lit.s_var();
        ++watch_index;
      }
    }
    if (watch_index == 0) {
      assert(cl.num_lits() == 1);
      continue;
    }
    assert(watch_index == 2);
    for (unsigned j = 0; j < cl.num_lits(); ++j) {
      CLitPoolElement lit = cl.literal(j);
      int vid1 = (watched[0]>>1);
      if (variable(vid1).value() == (unsigned)(watched[0] & 0x1)) {
        if (!lit.is_watched()) {
          assert(literal_value(lit) == 0);
          assert(variable(lit.var_index()).dlevel() <=
                  variable(vid1).dlevel());
        }
      }
      int vid2 = (watched[1]>>1);
      if (variable(vid2).value() == (unsigned)(watched[1] & 0x1)) {
        if (!lit.is_watched()) {
          assert(literal_value(lit) == 0);
          assert(variable(lit.var_index()).dlevel() <=
                  variable(vid1).dlevel());
        }
      }
    }
  }
}

void CSolver::mark_vars(ClauseIdx cl, int var_idx) {
  assert(_resolvents.empty() || var_idx != -1);
#ifdef VERIFY_ON
  _resolvents.push_back(clause(cl).id());
#endif
  for (CLitPoolElement* itr = clause(cl).literals(); (*itr).val() > 0; ++itr) {
    int v = (*itr).var_index();
    if (v == var_idx)
      continue;
    else if (variable(v).dlevel() == dlevel()) {
      if (!variable(v).is_marked()) {
        variable(v).set_marked();
        ++_num_marked;
        if (_mark_increase_score) {
          int tmp = itr->s_var();
          adjust_variable_order(&tmp, 1);
        }
      }
    } else {
      assert(variable(v).dlevel() < dlevel());
      if (variable(v).new_cl_phase() == UNKNOWN) {  // it's not in the new cl
        // We can remove the variable assigned at dlevel 0 if
        // we are nog going to use incremental SAT.
        // if(variable(v).dlevel()){
          ++_num_in_new_cl;
          variable(v).set_new_cl_phase((*itr).var_sign());
          _conflict_lits.push_back((*itr).s_var());
        // }
       } else {
         // if this variable is already in the new clause, it must
         // have the same phase
         assert(variable(v).new_cl_phase() == (*itr).var_sign());
       }
    }
  }
}

int CSolver::analyze_conflicts(void) {
  assert(!_conflicts.empty());
  assert(_conflict_lits.size() == 0);
  assert(_implication_queue.empty());
  assert(_num_marked == 0);
  if (dlevel() == 0) {  // already at level 0. Conflict means unsat.
#ifdef VERIFY_ON
    for (unsigned i = 1; i < variables()->size(); ++i) {
      if (variable(i).value() != UNKNOWN) {
        assert(variable(i).dlevel() <= 0);
        int ante = variable(i).antecedent();
        int ante_id = 0;
        if (ante >= 0) {
          ante_id = clause(ante).id();
          assert(clause(ante).status() != DELETED_CL);
          verify_out << "VAR: " << i
                     << " L: " << variable(i).assgn_stack_pos()
                     << " V: " << variable(i).value()
                     << " A: " << ante_id
                     << " Lits:";
          for (unsigned j = 0; j < clause(ante).num_lits(); ++j)
            verify_out << " " << clause(ante).literal(j).s_var();
          verify_out << endl;
        }
      }
    }
    ClauseIdx shortest;
    shortest = _conflicts.back();
    unsigned len = clause(_conflicts.back()).num_lits();
    while (!_conflicts.empty()) {
      if (clause(_conflicts.back()).num_lits() < len) {
        shortest = _conflicts.back();
        len = clause(_conflicts.back()).num_lits();
      }
      _conflicts.pop_back();
    }
    verify_out << "CONF: " << clause(shortest).id() << " ==";
    for (unsigned i = 0; i < clause(shortest).num_lits(); ++i) {
      int svar = clause(shortest).literal(i).s_var();
      verify_out << " " << svar;
    }
    verify_out << endl;
#endif
    _conflicts.clear();
    back_track(0);
    return -1;
  }
  return  conflict_analysis_firstUIP();
}

// when all the literals involved are in _conflict_lits
// call this function to finish the adding clause and backtrack

int CSolver::finish_add_conf_clause(int gflag) {
  ClauseIdx added_cl = add_conflict_clause(&(*_conflict_lits.begin()),
                                           _conflict_lits.size(), gflag);
  if (added_cl < 0) {  // memory out.
    _stats.is_mem_out = true;
    _conflicts.clear();
    assert(_implication_queue.empty());
    return 1;
  }

  top_unsat_cls = clauses()->end();
  --top_unsat_cls;

#ifdef VERIFY_ON
  verify_out << "CL: " <<  clause(added_cl).id() << " <=";
  for (unsigned i = 0; i< _resolvents.size(); ++i)
        verify_out << " " <<  _resolvents[i];
    verify_out << endl;
    _resolvents.clear();
#endif

  adjust_variable_order(&(*_conflict_lits.begin()), _conflict_lits.size());

  if (_params.shrinking.enable) {
    _shrinking_cls.clear();
    if (_stats.shrinking_cls_length != 0) {
      int benefit = _stats.shrinking_cls_length - _conflict_lits.size();
      _stats.shrinking_benefit += benefit;
      _stats.shrinking_cls_length = 0;
      _recent_shrinkings.push(benefit);
      if (_recent_shrinkings.size() > _params.shrinking.window_width) {
        _stats.shrinking_benefit -= _recent_shrinkings.front();
        _recent_shrinkings.pop();
      }
    }
    if (_conflict_lits.size() > _params.shrinking.size) {
      _shrinking_cls.clear();
      for (unsigned i = 0, sz = _conflict_lits.size(); i < sz; ++i) {
        _shrinking_cls.insert(pair<int, int>
                 (variable(_conflict_lits[i]>>1).dlevel(), _conflict_lits[i]));
      }
      int prev_dl = _shrinking_cls.begin()->first;
      multimap<int, int>::iterator itr, itr_del;
      int last_dl = _shrinking_cls.rbegin()->first;

      bool found_gap = false;
      for (itr = _shrinking_cls.begin(); itr->first != last_dl;) {
        if (itr->first - prev_dl > 2) {
          found_gap = true;
          break;
        }
        prev_dl = itr->first;
        itr_del = itr;
        ++itr;
        _shrinking_cls.erase(itr_del);
      }
      if (found_gap && _shrinking_cls.size() > 0 && prev_dl < dlevel() - 1) {
        _stats.shrinking_cls_length = _conflict_lits.size();
        ++_stats.num_shrinkings;
        back_track(prev_dl + 1);
        _conflicts.clear();
#ifdef VERIFY_ON
        _resolvents.clear();
#endif
        _num_in_new_cl = 0;
        for (unsigned i = 0, sz = _conflict_lits.size(); i < sz; ++i)
          variable(_conflict_lits[i]>>1).set_new_cl_phase(UNKNOWN);
        _conflict_lits.clear();
        if (_stats.num_shrinkings %
            _params.shrinking.bound_update_frequency == 0 &&
            _recent_shrinkings.size() == _params.shrinking.window_width) {
          if (_stats.shrinking_benefit > _params.shrinking.upper_bound)
            _params.shrinking.size += _params.shrinking.upper_delta;
          else if (_stats.shrinking_benefit < _params.shrinking.lower_bound)
            _params.shrinking.size += _params.shrinking.lower_delta;
        }
        return prev_dl;
      }
    }
  }
  int back_dl = 0;
  int unit_lit = -1;

  for (unsigned i = 0; i < clause(added_cl).num_lits(); ++i) {
    int vid = clause(added_cl).literal(i).var_index();
    int sign =clause(added_cl).literal(i).var_sign();
    assert(variable(vid).value() != UNKNOWN);
    assert(literal_value(clause(added_cl).literal(i)) == 0);
    int dl = variable(vid).dlevel();
    if (dl < dlevel()) {
      if (dl > back_dl)
        back_dl = dl;
    } else {
      assert(unit_lit == -1);
      unit_lit = vid + vid + sign;
    }
  }
  if (back_dl == 0) {
    _stats.next_restart = _stats.num_backtracks + _stats.restart_incr;
    _stats.next_cls_deletion = _stats.num_backtracks +
                               _params.cls_deletion.interval;
  }

  back_track(back_dl + 1);
  queue_implication(unit_lit, added_cl);

  // after resolve the first conflict, others must also be resolved
  // for (unsigned i = 1; i < _conflicts.size(); ++i)
  //   assert(!is_conflicting(_conflicts[i]));

  _conflicts.clear();

  while (!_conflict_lits.empty()) {
    int svar = _conflict_lits.back();
    _conflict_lits.pop_back();
    CVariable & var = variable(svar >> 1);
    assert(var.new_cl_phase() == (unsigned)(svar & 0x1));
    --_num_in_new_cl;
    var.set_new_cl_phase(UNKNOWN);
  }
  assert(_num_in_new_cl == 0);
  return back_dl;
}

int CSolver::conflict_analysis_firstUIP(void) {
  int min_conf_id = _conflicts[0];
  int min_conf_length = -1;
  ClauseIdx cl;
  unsigned gflag;
  _mark_increase_score = false;
  if (_conflicts.size() > 1) {
    for (vector<ClauseIdx>::iterator ci = _conflicts.begin();
         ci != _conflicts.end(); ci++) {
      assert(_num_in_new_cl == 0);
      assert(dlevel() > 0);
      cl = *ci;
      mark_vars(cl, -1);
      // current dl must be the conflict cl.
      vector <int> & assignments = *_assignment_stack[dlevel()];
      // now add conflict lits, and unassign vars
      for (int i = assignments.size() - 1; i >= 0; --i) {
        int assigned = assignments[i];
        if (variable(assigned >> 1).is_marked()) {
          // this variable is involved in the conflict clause or its antecedent
          variable(assigned>>1).clear_marked();
          --_num_marked;
          ClauseIdx ante_cl = variable(assigned>>1).get_antecedent();
          if ( _num_marked == 0 ) {
            // the first UIP encountered, conclude add clause
            assert(variable(assigned>>1).new_cl_phase() == UNKNOWN);
            // add this assignment's reverse, e.g. UIP
            _conflict_lits.push_back(assigned ^ 0x1);
            ++_num_in_new_cl;
            variable(assigned>>1).set_new_cl_phase((assigned^0x1)&0x1);
            break;
          } else {
            assert(ante_cl != NULL_CLAUSE);
            mark_vars(ante_cl, assigned >> 1);
          }
        }
      }
      if (min_conf_length == -1 ||
          (int)_conflict_lits.size() < min_conf_length) {
        min_conf_length = _conflict_lits.size();
        min_conf_id = cl;
      }

      for (vector<int>::iterator vi = _conflict_lits.begin(); vi !=
           _conflict_lits.end(); ++vi) {
        int s_var = *vi;
        CVariable & var = variable(s_var >> 1);
        assert(var.new_cl_phase() == (unsigned)(s_var & 0x1));
        var.set_new_cl_phase(UNKNOWN);
      }
      _num_in_new_cl = 0;
      _conflict_lits.clear();
#ifdef VERIFY_ON
      _resolvents.clear();
#endif
    }
  }

  assert(_num_marked == 0);
  cl = min_conf_id;
  clause(cl).activity() += 5;
  _mark_increase_score = true;
  mark_vars(cl, -1);
  gflag = clause(cl).gflag();
  vector <int> & assignments = *_assignment_stack[dlevel()];
  for (int i = assignments.size() - 1; i >= 0; --i) {
    int assigned = assignments[i];
    if (variable(assigned >> 1).is_marked()) {
      variable(assigned>>1).clear_marked();
      --_num_marked;
      ClauseIdx ante_cl = variable(assigned>>1).get_antecedent();
      if ( _num_marked == 0 ) {
        _conflict_lits.push_back(assigned ^ 0x1);
        ++_num_in_new_cl;
        variable(assigned >> 1).set_new_cl_phase((assigned ^ 0x1) & 0x1);
        break;
      } else {
        gflag |= clause(ante_cl).gflag();
        mark_vars(ante_cl, assigned >> 1);
        clause(ante_cl).activity() += 5;
      }
    }
  }
  return finish_add_conf_clause(gflag);
}

void CSolver::print_cls(ostream & os) {
  for (unsigned i = 0; i < clauses()->size(); ++i) {
    CClause & cl = clause(i);
    if (cl.status() == DELETED_CL)
      continue;
    if (cl.status() == ORIGINAL_CL) {
      os <<"0 ";
    } else {
      assert(cl.status() == CONFLICT_CL);
      os << "A ";
    }
    for (unsigned j = 1; j < 33; ++j)
      os << (cl.gid(j) ? 1 : 0);
    os << "\t";
    for (unsigned j = 0; j < cl.num_lits(); ++j) {
      os << (cl.literal(j).var_sign() ? "-":"")
         << cl.literal(j).var_index() << " ";
    }
    os <<"0" <<  endl;
  }
}

void CSolver::print_vars(ostream & os) {
   os << "print_vars:" << endl;
  unsigned size = num_variables();
  for (unsigned i = 1; i <= size; ++i) {
    CVariable & var = variable(i);
    
    os << "var " << i << ":" << endl;
    //os << "\tvalue = " << var.value() << endl;
    os << "\tcycle = " << var.get_cycle() << endl;
  }
}

int CSolver::mem_usage(void) {
  int mem_dbase = CDatabase::mem_usage();
  int mem_assignment = 0;
  for (int i = 0; i < _stats.max_dlevel; ++i)
    mem_assignment += _assignment_stack[i]->capacity() * sizeof(int);
  mem_assignment += sizeof(vector<int>)* _assignment_stack.size();
  return mem_dbase + mem_assignment;
}

void CSolver::clean_up_dbase(void) {
  assert(dlevel() == 0);

  int mem_before = mem_usage();
  // 1. remove all the learned clauses
  for (vector<CClause>::iterator itr = clauses()->begin();
       itr != clauses()->end() - 1; ++itr) {
    CClause & cl = * itr;
    if (cl.status() != ORIGINAL_CL)
      mark_clause_deleted(cl);
  }
  // delete_unrelevant_clauses() is specialized using berkmin deletion strategy

  // 2. free up the mem for the vectors if possible
  for (unsigned i = 0; i < variables()->size(); ++i) {
    for (unsigned j = 0; j < 2; ++j) {  // both phase
      vector<CLitPoolElement *> watched;
      vector<CLitPoolElement *> & old_watched = variable(i).watched(j);
      watched.reserve(old_watched.size());
      for (vector<CLitPoolElement *>::iterator itr = old_watched.begin();
           itr != old_watched.end(); ++itr)
        watched.push_back(*itr);
        // because watched is a temp mem allocation, it will get deleted
        // out of the scope, but by swap it with the old_watched, the
        // contents are reserved.
        old_watched.swap(watched);
#ifdef KEEP_LIT_CLAUSES
        vector<int> lits_cls;
        vector<int> & old_lits_cls = variable(i).lit_clause(j);
        lits_cls.reserve(old_lits_cls.size());
        for (vector<int>::iterator itr1 = old_lits_cls.begin(); itr1 !=
            old_lits_cls.end(); ++itr1)
          lits_cls.push_back(*itr1);
        old_lits_cls.swap(lits_cls);
#endif
    }
  }

  int mem_after = mem_usage();
  if (_params.verbosity > 0) {
    cout << "Database Cleaned, releasing (approximately) "
         << mem_before - mem_after << " Bytes" << endl;
  }
}



void CSolver::restart(void) {
  _stats.num_restarts += 1;
  if (_params.verbosity > 1 )
    cout << "Restarting ... " << endl;
  if (dlevel() > 0)
    back_track(1);
  assert(dlevel() == 0);
}

// this function can be called within a solving process. i.e. not after
// solve() terminate
int CSolver::add_clause_incr(int * lits, int num_lits, int gid) {
  // Do not mess up with shrinking.
  assert(!_params.shrinking.enable || _shrinking_cls.empty());
  unsigned gflag;

  if (gid == PERMANENT_GID)
    gflag = 0;
  else if (gid == VOLATILE_GID) {
    gflag = ~0x0;
  } else {
    assert(gid <= WORD_WIDTH && gid > 0);
    gflag = (1 << (gid - 1));
  }

  int cl = add_clause(lits, num_lits, gflag);
  if (cl < 0)
    return -1;
  clause(cl).set_status(ORIGINAL_CL);

  if (clause(cl).num_lits() == 1) {
    int var_idx = clause(cl).literal(0).var_index();
    if (literal_value(clause(cl).literal(0)) == 0 &&
        variable(var_idx).dlevel() == 0) {
      back_track(0);
      if (preprocess() == CONFLICT)
        _stats.outcome = UNSATISFIABLE;
    } else {
      if (dlevel() > 0)
        back_track(1);
      queue_implication(clause(cl).literal(0).s_var(), cl);
    }
    return cl;
  }

  for (unsigned i = 0, sz = clause(cl).num_lits(); i < sz; ++i) {
    int var_idx = lits[i] >> 1;
    int value = variable(var_idx).value();
    if (value == UNKNOWN)
      continue;
    if (variable(var_idx).dlevel() == 0 &&
        variable(var_idx).antecedent() == -1 &&
        literal_value(clause(cl).literal(i)) == 0) {
      back_track(0);
      if (preprocess() == CONFLICT)
        _stats.outcome = UNSATISFIABLE;
      return cl;
    }
  }

  int max_level = 0;
  int max_level2 = 0;
  int unit_lit = 0;
  int unknown_count = 0;
  int num_sat = 0;
  int sat_dlevel = -1, max_lit = 0;
  bool already_sat = false;

  for (unsigned i = 0, sz = clause(cl).num_lits();
       unknown_count < 2 && i < sz; ++i) {
    int var_idx = lits[i] / 2;
    int value = variable(var_idx).value();
    if (value == UNKNOWN) {
      unit_lit = clause(cl).literal(i).s_var();
      ++unknown_count;
    } else {
      int dl = variable(var_idx).dlevel();
      if (dl >= max_level) {
        max_level2 = max_level;
        max_level = dl;
        max_lit = clause(cl).literal(i).s_var();
      }
      else if (dl > max_level2)
        max_level2 = dl;
      if (literal_value(clause(cl).literal(i)) == 1) {
        already_sat = true;
        ++num_sat;
        sat_dlevel = dl;
      }
    }
  }
  if (unknown_count == 0) {
    if (already_sat) {
      assert(sat_dlevel > -1);
      if (num_sat == 1 && sat_dlevel == max_level && max_level > max_level2) {
        back_track(max_level2 + 1);
        assert(max_lit > 1);
        queue_implication(max_lit, cl);
      }
    } else {
      assert(is_conflicting(cl));
      if (max_level > max_level2) {
        back_track(max_level2 + 1);
        assert(max_lit > 1);
        queue_implication(max_lit, cl);
      } else {
        back_track(max_level);
        if (max_level == 0 && preprocess() == CONFLICT)
          _stats.outcome = UNSATISFIABLE;
      }
    }
  }
  else if (unknown_count == 1) {
    if (!already_sat) {
      if (max_level < dlevel())
        back_track(max_level + 1);
      queue_implication(unit_lit, cl);
    }
  }
  return cl;
}
