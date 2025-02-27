/****************************************************************************************[Solver.h]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef Minisat_Solver_h
#define Minisat_Solver_h

#include "minisat/core/SolverTypes.h"
#include "minisat/mtl/Alg.h"
#include "minisat/mtl/Heap.h"
#include "minisat/mtl/IntMap.h"
#include "minisat/mtl/Vec.h"
#include "minisat/utils/Options.h"

namespace Minisat {

//=================================================================================================
// Solver -- the main class:

class Solver {
public:
  // Constructor/Destructor:
  //
  Solver();
  virtual ~Solver();

  // Problem specification:
  //
  Var newVar(lbool upol = l_Undef, bool dvar = true); // Add a new variable with parameters specifying variable mode.
  void releaseVar(Literal l);                         // Make literal true and promise to never refer to variable again.

  bool addClause(const vec<Literal> &clause); // Add a clause to the solver.
  bool addEmptyClause();                      // Add the empty clause, making the solver contradictory.
  bool addClause(Literal p);                  // Add a unit clause to the solver.

  bool addClause_(vec<Literal> &clause); // Add a clause to the solver without making superflous internal copy. Will change the passed vector 'clause'.

  // Solving:
  //
  bool simplify();                                 // Removes already satisfied clauses.
  bool solve(const vec<Literal> &assumps);         // Search for a model that respects a given set of assumptions.
  lbool solveLimited(const vec<Literal> &assumps); // Search for a model that respects a given set of assumptions (With resource constraints).
  bool solve();                                    // Search without assumptions.
  bool solve(Literal p);                           // Search for a model that respects a single assumption.
  bool okay() const;                               // FALSE means solver is in a conflicting state

  bool implies(const vec<Literal> &assumps, vec<Literal> &out);

  // Iterate over clauses and top-level assignments:
  ClauseIterator clausesBegin() const;
  ClauseIterator clausesEnd() const;
  TrailIterator trailBegin() const;
  TrailIterator trailEnd() const;

  void toDimacs(FILE *f, const vec<Literal> &assumps); // Write CNF to file in DIMACS-format.
  void toDimacs(const char *file, const vec<Literal> &assumps);
  void toDimacs(FILE *f, Clause &c, vec<Var> &map, Var &max);

  // Convenience versions of 'toDimacs()':
  void toDimacs(const char *file);
  void toDimacs(const char *file, Literal p);

  // Variable mode:
  //
  void setPolarity(Var v, lbool b);   // Declare which polarity the decision heuristic should use for a variable. Requires mode 'polarity_user'.
  void setDecisionVar(Var v, bool b); // Declare if a variable should be eligible for selection in the decision heuristic.

  // Read state:
  //
  lbool value(Var x) const;          // The current value of a variable.
  lbool value(Literal p) const;      // The current value of a literal.
  lbool modelValue(Var x) const;     // The value of a variable in the last model. The last call to solve must have been satisfiable.
  lbool modelValue(Literal p) const; // The value of a literal in the last model. The last call to solve must have been satisfiable.
  int nAssigns() const;              // The current number of assigned literals.
  int nClauses() const;              // The current number of original clauses.
  int nLearnts() const;              // The current number of learnt clauses.
  int nVars() const;                 // The current number of variables.
  int nFreeVars() const;
  void printStats() const; // Print some current statistics to standard output.

  // Resource contraints:
  void setConfBudget(int64_t x);
  void setPropBudget(int64_t x);
  void budgetOff();
  void interrupt();      // Trigger a (potentially asynchronous) interruption of the solver.
  void clearInterrupt(); // Clear interrupt indicator flag.

  // Memory managment:
  //
  virtual void garbageCollect();
  void checkGarbage(double gf);
  void checkGarbage();

  // Extra results: (read-only member variable)
  //
  vec<lbool> model; // If problem is satisfiable, this vector contains the model (if any).
  LSet conflict;    // If problem is unsatisfiable (possibly under assumptions),
                    // this vector represent the final conflict clause expressed in the assumptions.

  // Mode of operation:
  //
  int verbosity;
  double var_decay;
  double clause_decay;
  double random_var_freq;
  double random_seed;
  bool luby_restart;
  int ccmin_mode;      // Controls conflict clause minimization (0=none, 1=basic, 2=deep).
  int phase_saving;    // Controls the level of phase saving (0=none, 1=limited, 2=full).
  bool rnd_pol;        // Use random polarities for branching heuristics.
  bool rnd_init_act;   // Initialize variable activities with a small random value.
  double garbage_frac; // The fraction of wasted memory allowed before a garbage collection is triggered.
  int min_learnts_lim; // Minimum number to set the learnts limit to.

  int restart_first;        // The initial restart limit.                                                                (default 100)
  double restart_inc;       // The factor with which the restart limit is multiplied in each restart.                    (default 1.5)
  double learntsize_factor; // The intitial limit for learnt clauses is a factor of the original clauses.                (default 1 / 3)
  double learntsize_inc;    // The limit for learnt clauses is multiplied with this factor each restart.                 (default 1.1)

  int learntsize_adjust_start_confl;
  double learntsize_adjust_inc;

  // Statistics: (read-only member variable)
  //
  uint64_t solves, starts, decisions, rnd_decisions, propagations, conflicts;
  uint64_t unassigned_decision_variable_count, num_clauses, num_learnts, clauses_literals, learnts_literals, max_literals, tot_literals;

protected:
  // Helper structures:
  //
  struct VarData {
    ClauseRef reason;
    int level;
  };
  static inline VarData mkVarData(ClauseRef cr, int l) {
    VarData d = {cr, l};
    return d;
  }

  struct Watcher {
    ClauseRef cref;
    Literal blocker;
    Watcher(ClauseRef cr, Literal blocker) : cref(cr),
                                             blocker(blocker) {}

    bool operator==(const Watcher &w) const { return cref == w.cref; }

    bool operator!=(const Watcher &w) const { return cref != w.cref; }
  };

  struct WatcherDeleted {
    const ClauseAllocator &ca;
    WatcherDeleted(const ClauseAllocator &_ca) : ca(_ca) {}
    bool operator()(const Watcher &w) const { return ca[w.cref].mark() == 1; }
  };

  struct VarOrderLt {
    const IntMap<Var, double> &activity;
    bool operator()(Var x, Var y) const { return activity[x] > activity[y]; }
    VarOrderLt(const IntMap<Var, double> &act) : activity(act) {}
  };

  struct ShrinkStackElem {
    uint32_t i;
    Literal l;
    ShrinkStackElem(uint32_t _i, Literal _l) : i(_i), l(_l) {}
  };

  // Solver state:
  //
  vec<ClauseRef> original_clauses; // List of problem clauses.
  vec<ClauseRef> addition_clauses; // List of learnt clauses.
  vec<Literal> trail;              // Assignment stack; stores all assigments made in the order they were made.
  vec<int> trail_separators;       // Separator indices for different decision levels in 'trail'.
  vec<Literal> assumptions;        // Current set of assumptions provided to solve by the user.

  VMap<double> activity;     // A heuristic measurement of the activity of a variable.
  VMap<lbool> assignment;    // The current assignments.
  VMap<char> polarity;       // The preferred polarity of each variable.
  VMap<lbool> user_polarity; // The users preferred polarity of each variable.
  VMap<char> decision;       // Declares if a variable is eligible for selection in the decision heuristic.
  VMap<VarData> vardata;     // Stores reason and level for each variable.
  OccLists<Literal, vec<Watcher>, WatcherDeleted, MkIndexLit>
      watches; // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).

  Heap<Var, VarOrderLt> order_heap; // A priority queue of variables ordered with respect to the variable activity.

  bool unsat_unknown;       // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
  double clause_bump;       // Amount to bump next clause with.
  double variable_bump;     // Amount to bump next variable with.
  int queue_head;           // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
  int simpDB_assigns;       // Number of top-level assignments since last execution of 'simplify()'.
  int64_t simpDB_props;     // Remaining number of propagations that must be made before next execution of 'simplify()'.
  double progress_estimate; // Set by 'search()'.
  bool remove_satisfied;    // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.
  Var next_var;             // Next variable to be created.
  ClauseAllocator ca;

  vec<Var> released_vars;
  vec<Var> free_vars;

  // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is used, exept 'seen' wich is used in several places.
  VMap<char> tmp_seen;
  vec<ShrinkStackElem> tmp_analyze_stack;
  vec<Literal> tmp_analyze_toclear;
  vec<Literal> tmp_add_clause_buffer;

  double max_learnts;
  double learntsize_adjust_confl;
  int learntsize_adjust_cnt;

  // Resource contraints:
  int64_t conflict_budget;    // -1 means no budget.
  int64_t propagation_budget; // -1 means no budget.
  bool asynch_interrupt;

  // Main internal methods:
  void insertVarOrder(Var x);                                                // Insert a variable in the decision order priority queue.
  Literal pickBranchLiteral();                                               // Return the next decision variable.
  void newDecisionLevel();                                                   // Begins a new decision level.
  void uncheckedEnqueue(Literal p, ClauseRef from = CRef_Undef);             // Enqueue a literal. Assumes value of literal is undefined.
  bool enqueue(Literal p, ClauseRef from = CRef_Undef);                      // Test if fact 'p' contradicts current state, enqueue otherwise.
  ClauseRef propagate();                                                     // Perform unit propagation. Returns possibly conflicting clause.
  void cancelUntil(int level);                                               // Backtrack until a certain level.
  void analyze(ClauseRef confl, vec<Literal> &out_learnt, int &out_btlevel); // (bt = backtrack)
  void analyzeFinal(Literal p, LSet &out_conflict);                          // COULD THIS BE IMPLEMENTED BY THE ORDINARIY "analyze" BY SOME REASONABLE GENERALIZATION?
  bool litRedundant(Literal p);                                              // (helper method for 'analyze()')
  lbool search(int nof_conflicts);                                           // Search for a given number of conflicts.
  lbool solve_();                                                            // Main solve method (assumptions given in 'assumptions').
  void reduceDB();                                                           // Reduce the set of learnt clauses.
  void removeSatisfied(vec<ClauseRef> &cs);                                  // Shrink 'cs' to contain only non-satisfied clauses.
  void rebuildOrderHeap();

  // Maintaining Variable/Clause activity:
  void varDecayActivity();                 // Decay all variables with the specified factor. Implemented by increasing the 'bump' value instead.
  void varBumpActivity(Var v, double inc); // Increase a variable with the current 'bump' value.
  void varBumpActivity(Var v);             // Increase a variable with the current 'bump' value.
  void claDecayActivity();                 // Decay all clauses with the specified factor. Implemented by increasing the 'bump' value instead.
  void clauseBumpActivity(Clause &c);      // Increase a clause with the current 'bump' value.

  // Operations on clauses:
  void attachClause(ClauseRef cr);                      // Attach a clause to watcher lists.
  void detachClause(ClauseRef cr, bool strict = false); // Detach a clause to watcher lists.
  void removeClause(ClauseRef cr);                      // Detach and free a clause.
  bool isRemoved(ClauseRef cr) const;                   // Test if a clause has been removed.
  bool locked(const Clause &c) const;                   // Returns TRUE if a clause is a reason for some implication in the current state.
  bool satisfied(const Clause &c) const;                // Returns TRUE if a clause is satisfied in the current state.

  // Misc:
  int decisionLevel() const;           // Gives the current decisionlevel.
  uint32_t abstractLevel(Var x) const; // Used to represent an abstraction of sets of decision levels.
  ClauseRef reason(Var x) const;
  int level(Var x) const;
  double progressEstimate() const; // DELETE THIS ?? IT'S NOT VERY USEFUL ...
  bool withinBudget() const;
  void relocAll(ClauseAllocator &to);

  // Static helpers:

  // Returns a random float 0 <= x < 1. Seed must never be 0.
  static inline double drand(double &seed) {
    seed *= 1389796;
    int q = (int)(seed / 2147483647);
    seed -= (double)q * 2147483647;
    return seed / 2147483647;
  }

  // Returns a random integer 0 <= x < size. Seed must never be 0.
  static inline int irand(double &seed, int size) {
    return (int)(drand(seed) * size);
  }
};

//=================================================================================================
// Implementation of inline methods:

inline ClauseRef Solver::reason(Var x) const {
  return vardata[x].reason;
}

inline int Solver::level(Var x) const {
  return vardata[x].level;
}

inline void Solver::insertVarOrder(Var x) {
  if (!order_heap.inHeap(x) && decision[x]) {
    order_heap.insert(x);
  }
}

inline void Solver::varDecayActivity() { variable_bump *= (1 / var_decay); }

inline void Solver::varBumpActivity(Var v) { varBumpActivity(v, variable_bump); }

inline void Solver::varBumpActivity(Var v, double inc) {
  if ((activity[v] += inc) > 1e100) { // Rescale:
    for (int i = 0; i < nVars(); i++) {
      activity[i] *= 1e-100;
    }
    variable_bump *= 1e-100;
  }

  // Update order_heap with respect to new activity:
  if (order_heap.inHeap(v)) {
    order_heap.decrease(v);
  }
}

inline void Solver::claDecayActivity() {
  clause_bump *= (1 / clause_decay);
}

inline void Solver::clauseBumpActivity(Clause &c) {
  if ((c.activity() += clause_bump) > 1e20) { // Rescale:
    for (int i = 0; i < addition_clauses.size(); i++) {
      ca[addition_clauses[i]].activity() *= 1e-20;
    }
    clause_bump *= 1e-20;
  }
}

inline void Solver::checkGarbage(void) { return checkGarbage(garbage_frac); }

inline void Solver::checkGarbage(double gf) {
  if (ca.wasted() > ca.size() * gf) {
    garbageCollect();
  }
}

// NOTE: enqueue does not set the ok flag! (only public methods do)
inline bool Solver::enqueue(Literal p, ClauseRef from) {
  if (value(p) != l_Undef) {    // If already valued…
    return value(p) != l_False; // … return whether on the queue or impossible to queue.
  } else {
    return (uncheckedEnqueue(p, from), true); // Value and set decision level.
  }
}

inline bool Solver::addClause(const vec<Literal> &clause) {
  clause.copyTo(tmp_add_clause_buffer);
  return addClause_(tmp_add_clause_buffer);
}
inline bool Solver::addEmptyClause() {
  tmp_add_clause_buffer.clear();
  return addClause_(tmp_add_clause_buffer);
}

inline bool Solver::addClause(Literal p) {
  tmp_add_clause_buffer.clear();
  tmp_add_clause_buffer.push(p);
  return addClause_(tmp_add_clause_buffer);
}

inline bool Solver::isRemoved(ClauseRef cr) const {
  return ca[cr].mark() == 1;
}

// A clause is locked whenever it has been used for an instance of propagation.
// The relevant background invariant here is that the last literal to be assigned is at the first index of a clause.
inline bool Solver::locked(const Clause &clause) const {
  bool satsfied_watch = value(clause[0]) == l_True;
  bool via_some_clause = reason(var(clause[0])) != CRef_Undef;
  bool via_this_clause = ca.lea(reason(var(clause[0]))) == &clause;

  return satsfied_watch && via_some_clause && via_this_clause;
}

// Creates a mark to signify the start of a new level in the trail.
inline void Solver::newDecisionLevel() {
  trail_separators.push(trail.size());
}

// A count of the number of markers used to indicate a new level.
inline int Solver::decisionLevel() const {
  return trail_separators.size();
}

inline uint32_t Solver::abstractLevel(Var x) const {
  return 1 << (level(x) & 31);
}

// The value of `x` on the current assignment.
// Note the return value of lbool, rather than bool.
inline lbool Solver::value(Var x) const {
  return assignment[x];
}

// The value of a litera on the current assignment.
inline lbool Solver::value(Literal p) const {
  // The value of p on the current assignment and the sign of p are the same.
  return assignment[var(p)] ^ sign(p);
}

// The value of `x` on the last model.
inline lbool Solver::modelValue(Var x) const {
  return model[x];
}

// The value of the literal on the last model.
inline lbool Solver::modelValue(Literal p) const {
  return model[var(p)] ^ sign(p);
}

// A count of assignments made.
// As the trail stores all assignments, this amounts to the size of the trail.
inline int Solver::nAssigns() const {
  return trail.size();
}

inline int Solver::nClauses() const { return num_clauses; }

inline int Solver::nLearnts() const { return num_learnts; }

inline int Solver::nVars() const { return next_var; }

// TODO: nFreeVars() is not quite correct, try to calculate right instead of adapting it like below:
// The intended value is not documented in the source, nor in the paper.
// So, what would be correct is a guess… though by name this should be all variables which have not been assigned.
inline int Solver::nFreeVars() const {
  // If no assumptions have been made, subtract the trail.
  // If some assumptions have been made, things are more difficult, as assumptions are mixed with consequences of those assumptions.
  // Taking the first separator will discount propagations with no assumptions, but some additional propagations may have happened.
  return (int)unassigned_decision_variable_count - (trail_separators.size() == 0 ? trail.size() : trail_separators[0]);
}
inline void Solver::setPolarity(Var v, lbool b) { user_polarity[v] = b; }

// If b is false, the value of v is not up for decision, otherwise the value of v may be set.
// Only used during with a fresh variable.
inline void Solver::setDecisionVar(Var v, bool b) {
  if (b && !decision[v]) {
    unassigned_decision_variable_count++;
  } else if (!b && decision[v]) {
    unassigned_decision_variable_count--;
  }

  decision[v] = b;
  insertVarOrder(v);
}

inline void Solver::setConfBudget(int64_t x) {
  conflict_budget = conflicts + x;
}

inline void Solver::setPropBudget(int64_t x) {
  propagation_budget = propagations + x;
}

inline void Solver::interrupt() {
  asynch_interrupt = true;
}

inline void Solver::clearInterrupt() {
  asynch_interrupt = false;
}

inline void Solver::budgetOff() {
  conflict_budget = -1;
  propagation_budget = -1;
}

inline bool Solver::withinBudget() const {
  bool conflicts_ok = conflict_budget < 0 || conflicts < (uint64_t)conflict_budget;
  bool propagations_ok = (propagation_budget < 0 || propagations < (uint64_t)propagation_budget);

  return !asynch_interrupt && conflicts_ok && propagations_ok;
}

// FIXME: after the introduction of asynchronous interrruptions the solve-versions that return a
// pure bool do not give a safe interface. Either interrupts must be possible to turn off here, or
// all calls to solve must return an 'lbool'. I'm not yet sure which I prefer.
inline bool Solver::solve() {
  budgetOff();
  assumptions.clear();
  return solve_() == l_True;
}

inline bool Solver::solve(Literal p) {
  budgetOff();
  assumptions.clear();
  assumptions.push(p);
  return solve_() == l_True;
}

inline bool Solver::solve(const vec<Literal> &assumps) {
  budgetOff();
  assumps.copyTo(assumptions);
  return solve_() == l_True;
}

inline lbool Solver::solveLimited(const vec<Literal> &assumps) {
  assumps.copyTo(assumptions);
  return solve_();
}

inline bool Solver::okay() const {
  return unsat_unknown;
}

inline ClauseIterator Solver::clausesBegin() const {
  return ClauseIterator(ca, &original_clauses[0]);
}

inline ClauseIterator Solver::clausesEnd() const {
  return ClauseIterator(ca, &original_clauses[original_clauses.size()]);
}

inline TrailIterator Solver::trailBegin() const {
  return TrailIterator(&trail[0]);
}

inline TrailIterator Solver::trailEnd() const {
  return TrailIterator(&trail[decisionLevel() == 0 ? trail.size() : trail_separators[0]]);
}

inline void Solver::toDimacs(const char *file) {
  vec<Literal> assumptions;
  toDimacs(file, assumptions);
}

inline void Solver::toDimacs(const char *file, Literal p) {
  vec<Literal> as;
  as.push(p);
  toDimacs(file, as);
}

//=================================================================================================
// Debug etc:

//=================================================================================================
} // namespace Minisat

#endif
