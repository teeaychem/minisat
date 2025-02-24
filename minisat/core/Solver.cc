/***************************************************************************************[Solver.cc]
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

#include <math.h>

#include "minisat/core/Solver.h"
#include "minisat/mtl/Alg.h"
#include "minisat/mtl/Sort.h"
#include "minisat/utils/System.h"

using namespace Minisat;

//=================================================================================================
// Options:

static const char *_cat = "CORE";

static DoubleOption opt_var_decay(_cat, "var-decay", "The variable activity decay factor", 0.95, DoubleRange(0, false, 1, false));
static DoubleOption opt_clause_decay(_cat, "cla-decay", "The clause activity decay factor", 0.999, DoubleRange(0, false, 1, false));
static DoubleOption opt_random_var_freq(_cat, "rnd-freq", "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
static DoubleOption opt_random_seed(_cat, "rnd-seed", "Used by the random variable selection", 91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption opt_ccmin_mode(_cat, "ccmin-mode", "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption opt_phase_saving(_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption opt_rnd_init_act(_cat, "rnd-init", "Randomize the initial activity", false);
static BoolOption opt_luby_restart(_cat, "luby", "Use the Luby restart sequence", true);
static IntOption opt_restart_first(_cat, "rfirst", "The base restart interval", 100, IntRange(1, INT32_MAX));
static DoubleOption opt_restart_inc(_cat, "rinc", "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
static DoubleOption opt_garbage_frac(_cat, "gc-frac", "The fraction of wasted memory allowed before a garbage collection is triggered", 0.20, DoubleRange(0, false, HUGE_VAL, false));
static IntOption opt_min_learnts_lim(_cat, "min-learnts", "Minimum learnt clause limit", 0, IntRange(0, INT32_MAX));

//=================================================================================================
// Constructor/Destructor:

Solver::Solver() : // Parameters (user settable):
                   verbosity(0),
                   var_decay(opt_var_decay),
                   clause_decay(opt_clause_decay),
                   random_var_freq(opt_random_var_freq),
                   random_seed(opt_random_seed),
                   luby_restart(opt_luby_restart),
                   ccmin_mode(opt_ccmin_mode),
                   phase_saving(opt_phase_saving),
                   rnd_pol(false),
                   rnd_init_act(opt_rnd_init_act),
                   garbage_frac(opt_garbage_frac),
                   min_learnts_lim(opt_min_learnts_lim),
                   restart_first(opt_restart_first),
                   restart_inc(opt_restart_inc),

                   // Parameters (the rest):

                   learntsize_factor((double)1 / (double)3),
                   learntsize_inc(1.1),

                   // Parameters (experimental):

                   learntsize_adjust_start_confl(100),
                   learntsize_adjust_inc(1.5),

                   // Statistics: (formerly in 'SolverStats')
                   solves(0),
                   starts(0),
                   decisions(0),
                   rnd_decisions(0),
                   propagations(0),
                   conflicts(0),
                   dec_vars(0),
                   num_clauses(0),
                   num_learnts(0),
                   clauses_literals(0),
                   learnts_literals(0),
                   max_literals(0),
                   tot_literals(0),

                   watches(WatcherDeleted(ca)),
                   order_heap(VarOrderLt(activity)),
                   ok(true),
                   cla_inc(1),
                   var_inc(1),
                   qhead(0),
                   simpDB_assigns(-1),
                   simpDB_props(0),
                   progress_estimate(0),
                   remove_satisfied(true),
                   next_var(0),

                   // Resource constraints:
                   conflict_budget(-1),
                   propagation_budget(-1),
                   asynch_interrupt(false) {}

Solver::~Solver() {
}

//=================================================================================================
// Minor methods:

// Creates a new SAT variable in the solver.
// If 'decision' is cleared, variable will not be used as a decision variable.
// (NOTE! This has effects on the meaning of a SATISFIABLE result.)
Var Solver::newVar(lbool upol, bool dvar) {
  Var v;
  if (free_vars.size() > 0) {
    v = free_vars.last();
    free_vars.pop();
  } else {
    v = next_var++;
  }

  // Initialise watch lists
  watches.init(mkLiteral(v, false));
  watches.init(mkLiteral(v, true));

  // Extend the assignment
  assigns.insert(v, l_Undef);

  // Set the reason and level (undefined, zero)
  vardata.insert(v, mkVarData(CRef_Undef, 0));

  // The activity of the variable
  activity.insert(v, rnd_init_act ? drand(random_seed) * 0.00001 : 0);

  seen.insert(v, 0);

  // The default polarity
  polarity.insert(v, true);
  user_pol.insert(v, upol);

  // Whether the variable can be decided
  decision.reserve(v);
  trail.capacity(v + 1);
  setDecisionVar(v, dvar);
  return v;
}

// Note: at the moment, only unassigned variable will be released
// (this is to avoid duplicate releases of the same variable).
void Solver::releaseVar(Literal l) {
  if (value(l) == l_Undef) {
    addClause(l);
    released_vars.push(var(l));
  }
}

bool Solver::addClause_(vec<Literal> &clause) {
  assert(decisionLevel() == 0);
  if (!ok)
    return false;

  // Check if clause is satisfied and remove false/duplicate literals:
  sort(clause);
  Literal literal;
  int i, j;

  for (i = j = 0, literal = lit_Undef; i < clause.size(); i++) {
    if (value(clause[i]) == l_True || clause[i] == ~literal) {
      return true; // Return true on tautology
    } else if (value(clause[i]) != l_False && clause[i] != literal) {
      // If the literal is not known to be false and is distinct from the previous literal…
      literal = clause[i];     // Update the literal
      clause[j++] = clause[i]; // Set the literal in the clause.
    }
  }

  clause.shrink(i - j);

  if (clause.size() == 0) {
    return ok = false; // False on a contradiction
  } else if (clause.size() == 1) {
    uncheckedEnqueue(clause[0]);
    return ok = (propagate() == CRef_Undef); // Immediately propagate a unit clause
  } else {
    ClauseRef cr = ca.alloc(clause, false);
    clauses.push(cr);
    attachClause(cr); // Sets the watches, increments counters
  }

  return true;
}

void Solver::attachClause(ClauseRef cr) {
  const Clause &c = ca[cr];
  assert(c.size() > 1);

  watches[~c[0]].push(Watcher(cr, c[1]));
  watches[~c[1]].push(Watcher(cr, c[0]));

  if (c.learnt()) {
    num_learnts++, learnts_literals += c.size();
  } else {
    num_clauses++, clauses_literals += c.size();
  }
}

void Solver::detachClause(ClauseRef cr, bool strict) {
  const Clause &c = ca[cr];
  assert(c.size() > 1);

  // Strict or lazy detaching:
  if (strict) { // Immediately remove watchers from the watch list.
    remove(watches[~c[0]], Watcher(cr, c[1]));
    remove(watches[~c[1]], Watcher(cr, c[0]));
  } else { // Otherwise, note the watch is lost.
    watches.smudge(~c[0]);
    watches.smudge(~c[1]);
  }

  if (c.learnt()) {
    num_learnts--, learnts_literals -= c.size();
  } else {
    num_clauses--, clauses_literals -= c.size();
  }
}

void Solver::removeClause(ClauseRef cr) {
  Clause &c = ca[cr];
  detachClause(cr);
  // Don't leave pointers to free'd memory!
  if (locked(c)) {
    vardata[var(c[0])].reason = CRef_Undef;
  }
  c.mark(1);
  ca.free(cr);
}

// Returns true if the clause is satisfied on the current assignment
bool Solver::satisfied(const Clause &clause) const {
  for (int i = 0; i < clause.size(); i++) {
    if (value(clause[i]) == l_True) {
      return true;
    }
  }
  return false;
}

// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
/*
1. For each literal in the queue:
  - Clear the assignment made for the literal.
  - If required, update phase information.
  - Put the variable on the variable heap, as it's available for choice.

2. Shrink the queue.
*/
void Solver::cancelUntil(int level) {
  if (decisionLevel() > level) {
    for (int lit_idx = trail.size() - 1; lit_idx >= trail_lim[level]; lit_idx--) {

      Var v = var(trail[lit_idx]);
      assigns[v] = l_Undef;

      if (phase_saving > 1 || (phase_saving == 1 && lit_idx > trail_lim.last())) {
        polarity[v] = sign(trail[lit_idx]);
      }

      insertVarOrder(v);
    }

    qhead = trail_lim[level];
    trail.shrink(trail.size() - trail_lim[level]);
    trail_lim.shrink(trail_lim.size() - level);
  }
}

//=================================================================================================
// Major methods:

Literal Solver::pickBranchLiteral() {
  Var next = var_Undef;

  // Random decision:
  if (drand(random_seed) < random_var_freq && !order_heap.empty()) {
    next = order_heap[irand(random_seed, order_heap.size())];
    if (value(next) == l_Undef && decision[next]) {
      rnd_decisions++;
    }
  }

  // Activity based decision:
  while (next == var_Undef || value(next) != l_Undef || !decision[next])
    if (order_heap.empty()) {
      next = var_Undef;
      break;
    } else {
      next = order_heap.removeMin();
    }

  // Choose polarity based on different polarity modes (global or per-variable):
  if (next == var_Undef) {
    return lit_Undef;
  } else if (user_pol[next] != l_Undef) {
    return mkLiteral(next, user_pol[next] == l_True);
  } else if (rnd_pol) {
    return mkLiteral(next, drand(random_seed) < 0.5);
  } else {
    return mkLiteral(next, polarity[next]);
  }
}

/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|
|  Description:
|    Analyze conflict and produce a reason clause.
|
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the
|        rest of literals. There may be others from the same level though.
|
|________________________________________________________________________________________________@*/
void Solver::analyze(ClauseRef conflict, vec<Literal> &out_learnt, int &out_btlevel) {
  int pathC = 0;
  Literal p = lit_Undef;

  // Generate conflict clause:
  out_learnt.push(); // Leave room for the asserting literal at the start of the clause, in order to maintain watch invariants.
  int index = trail.size() - 1;

  /*
  Analysis is covered very lightly in the MiniSAT paper.

  At a high-level, the goal is to walk backwards through the trail, collecting just as many literals from previous decision levels to obtain the current conflict through BCP.
  For, the most recent decision was required to derive a contradiction.
  And, so, without the most recent decision, that collection will force some different decision.
  (Note, though, that the decision may or may not be to decide on the opposite of the previous decision.)

  At a high-level, this may be done by establishing a bound on how many instances of BCP are required at the current level to obtain the current contradiction.
  As soon as a bound of zero is established, the clause can be used.

  The bound increases when a literal asserted at the current decision level is identified (for the first time).
  And, the bound decreases when a clause which asserts at the current decision level is identified and resolution is applied/simulated.

  With some reflection, this makes sense.
  For, the instance of resolution means the instance of BCP was not required.

  In addition, the trail is examined in reverse, which ensures the bound will be kept to a minimum, though we skip details on why.
  And, any literal which does not contribute to the bound forms part of the clause being built through analysis.

  Though, with an important exception!
  Literals asserted at the current level are skipped, as these are pivot literals for resolution.

  Note, that the literals are pivot literals follows from the background.
  For, each clause asserts some literal used in some other instance of BCP.
  That is, the clause asserts x and for some other literal y in the trail, the clause used to assert the literal contains ~x.
  Else, BCP used to derive y could have been applied to at some prior level.

  So, in summary:
  - Keep a bound on how may instance of BCP are required at the current level to derive a contradiction.
  - For each asserted literal in the trail which have not yet been examined, either:
    + Ignore the literal, as it was asserted at the current level, and so is the pivot for some instance of resolution.
    + Increase the bound, as the literal was obtain via BCP at the current level.
    + Add the literal to the clause under construction, as it was decided at some prior level.

  To identify which literals are the result of BCP at the current level the implementation makes use of an important invariant in relation to watch literals:

  - If some watch literal has an unknown value, it is at the start of a clause.

  This is quite general, but has a key consequence:

  - If a clause was used during BCP, then the asserted literal is at the start of the clause.

  This is useful, as it's then possible to infer how BCP handled a clause.
  No further analysis is required.
   */
  do {
    assert(conflict != CRef_Undef); // (otherwise should be UIP)
    Clause &clause = ca[conflict];

    if (clause.learnt()) {
      clauseBumpActivity(clause);
    }

    // p is the asserted literal for each clause, and will only be undef on the first pass of the do loop.
    // As, for each subsequent pass p is obtained from a clause to which BCP was applied.
    for (int j = (p == lit_Undef) ? 0 : 1; j < clause.size(); j++) {
      Literal q = clause[j];
      //  If seen_undef and …
      if (!seen[var(q)] && level(var(q)) > 0) { // Skip seen literal and unit clauses.

        varBumpActivity(var(q));
        seen[var(q)] = 1;

        if (level(var(q)) >= decisionLevel()) {
          pathC++; // Ignore anything from the current decision level.
        } else {
          out_learnt.push(q); // Record everything from prior decision levels.
        }
      }
    }

    // Select next clause to look at:
    while (!seen[var(trail[index--])]) {
    };
    p = trail[index + 1]; // Readjust index as --, though don't update index.

    conflict = reason(var(p));
    seen[var(p)] = 0;
    pathC--;

  } while (pathC > 0);

  out_learnt[0] = ~p; // Set the asserting literal.

  // Simplify conflict clause:

  // The asserted literal is at 0, so start at index 1.
  int i = 1; // Index of the next kept literal.
  int j = 1; // Index of the literal under consideration.
  out_learnt.copyTo(analyze_toclear);

  if (ccmin_mode == 2) {

    // Keep a literal just in case it's reason is missing, or it's not redundant.
    for (; i < out_learnt.size(); i++) {
      if (!litRedundant(out_learnt[i])) {
        out_learnt[j++] = out_learnt[i];
      }
    }

  } else if (ccmin_mode == 1) {
    for (; i < out_learnt.size(); i++) {
      Var x = var(out_learnt[i]);

      if (reason(x) == CRef_Undef) { // Keep any literal whose reason has been removed.
        out_learnt[j++] = out_learnt[i];
      } else {
        Clause &clause = ca[reason(var(out_learnt[i]))];
        for (int k = 1; k < clause.size(); k++) {
          // Keep any literal whose current derivation rests on an unseen clause.
          if (!seen[var(clause[k])] && level(var(clause[k])) > 0) {
            out_learnt[j++] = out_learnt[i];
            break;
          }
        }
      }
    }
  } else {
    i = j = out_learnt.size();
  }

  max_literals += out_learnt.size();
  out_learnt.shrink(i - j);
  tot_literals += out_learnt.size();

  // Find correct backtrack level:
  if (out_learnt.size() == 1) {
    out_btlevel = 0;
  } else {
    int max_idx = 1;
    // Find the first literal assigned at the next-highest level:
    for (int idx = 2; idx < out_learnt.size(); idx++) {
      if (level(var(out_learnt[idx])) > level(var(out_learnt[max_idx]))) {
        max_idx = idx;
      }
    }
    // Swap-in this literal at index 1:
    Literal p = out_learnt[max_idx];
    out_learnt[max_idx] = out_learnt[1];
    out_learnt[1] = p;
    out_btlevel = level(var(p));
  }

  for (int j = 0; j < analyze_toclear.size(); j++) {
    seen[var(analyze_toclear[j])] = 0; // ('seen[]' is now cleared)
  }
}

// Check if 'p' can be removed from a conflict clause.
bool Solver::litRedundant(Literal literal) {
  enum { seen_undef = 0,
         seen_source = 1,
         seen_removable = 2,
         seen_failed = 3 };

  assert(seen[var(literal)] == seen_undef || seen[var(literal)] == seen_source);
  // The clause used to obtain p has not been removed.
  if (reason(var(literal)) == CRef_Undef) {
    return false;
  }

  Clause *reason_clause = &ca[reason(var(literal))];
  vec<ShrinkStackElem> &stack = analyze_stack; // The analyze prefix indicates exclusive use here.
  stack.clear();

  // As we're inspecting the clause used to obtain p, p is at the first index of the clause.
  // So, to begin with idx at 1 is to skip p.
  for (uint32_t idx = 1;; idx++) {
    if (idx < (uint32_t)reason_clause->size()) {
      // Checking 'p'-parents 'l':
      Literal reason_literal = (*reason_clause)[idx];

      // Variable at level 0 or previously removable:
      if (level(var(reason_literal)) == 0 ||
          seen[var(reason_literal)] == seen_source ||
          seen[var(reason_literal)] == seen_removable) {
        continue;
      }

      // Check variable can not be removed for some local reason:
      if (reason(var(reason_literal)) == CRef_Undef || // It's not possible to remove a variable whose reason has been removed
          seen[var(reason_literal)] == seen_failed     // Nor if failed already.
      ) {
        // If a parent of p can't be removed, p goes on the stack
        stack.push(ShrinkStackElem(0, literal));

        for (int stack_idx = 0; stack_idx < stack.size(); stack_idx++) { // Anything on the stack…
          if (seen[var(stack[stack_idx].l)] == seen_undef) {
            seen[var(stack[stack_idx].l)] = seen_failed; // … fails if no other marker has been set.
            analyze_toclear.push(stack[stack_idx].l);    // And the literal is part of the addition clause.
          }
        }

        return false;
      }

      // Recursively check 'l':
      stack.push(ShrinkStackElem(idx, literal)); // The loop repeats, though p will be returned to later.
      literal = reason_literal;                  // This time, with the reason literal
      idx = 0;                                   // And, starting at 0
      reason_clause = &ca[reason(var(literal))]; // with the reason clause.

    } else {
      // Finished with current element 'p' and reason 'c':
      if (seen[var(literal)] == seen_undef) {
        seen[var(literal)] = seen_removable;
        analyze_toclear.push(literal);
      }

      // Terminate with success if stack is empty:
      if (stack.size() == 0)
        break;

      // Continue with top element on stack:
      idx = stack.last().i;
      literal = stack.last().l;
      reason_clause = &ca[reason(var(literal))];

      stack.pop();
    }
  }

  return true;
}

/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Literal p, LSet &out_conflict) {
  out_conflict.clear();
  out_conflict.insert(p);

  if (decisionLevel() == 0)
    return;

  seen[var(p)] = 1;

  for (int i = trail.size() - 1; i >= trail_lim[0]; i--) {
    Var x = var(trail[i]);
    if (seen[x]) {
      if (reason(x) == CRef_Undef) {
        assert(level(x) > 0);
        out_conflict.insert(~trail[i]);
      } else {
        Clause &c = ca[reason(x)];
        for (int j = 1; j < c.size(); j++)
          if (level(var(c[j])) > 0)
            seen[var(c[j])] = 1;
      }
      seen[x] = 0;
    }
  }

  seen[var(p)] = 0;
}

void Solver::uncheckedEnqueue(Literal p, ClauseRef from) {
  assert(value(p) == l_Undef);
  assigns[var(p)] = lbool(!sign(p));
  vardata[var(p)] = mkVarData(from, decisionLevel());
  trail.push_(p);
}

/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
ClauseRef Solver::propagate() {
  ClauseRef confl = CRef_Undef;
  int num_props = 0;

  while (qhead < trail.size()) {
    Literal p = trail[qhead++]; // 'p' is enqueued fact to propagate.
    vec<Watcher> &ws = watches.lookup(p);
    Watcher *i, *j, *end;
    num_props++;

    for (i = j = (Watcher *)ws, end = i + ws.size(); i != end;) {
      // Try to avoid inspecting the clause:
      Literal blocker = i->blocker;
      if (value(blocker) == l_True) {
        *j++ = *i++;
        continue;
      }

      // Make sure the false literal is data[1]:
      ClauseRef cr = i->cref;
      Clause &c = ca[cr];
      Literal false_lit = ~p;
      if (c[0] == false_lit)
        c[0] = c[1], c[1] = false_lit;
      assert(c[1] == false_lit);
      i++;

      // If 0th watch is true, then clause is already satisfied.
      Literal first = c[0];
      Watcher w = Watcher(cr, first);
      if (first != blocker && value(first) == l_True) {
        *j++ = w;
        continue;
      }

      // Look for new watch:
      for (int k = 2; k < c.size(); k++)
        if (value(c[k]) != l_False) {
          c[1] = c[k];
          c[k] = false_lit;
          watches[~c[1]].push(w);
          goto NextClause;
        }

      // Did not find watch -- clause is unit under assignment:
      *j++ = w;
      if (value(first) == l_False) {
        confl = cr;
        qhead = trail.size();
        // Copy the remaining watches:
        while (i < end)
          *j++ = *i++;
      } else
        uncheckedEnqueue(first, cr);

    NextClause:;
    }
    ws.shrink(i - j);
  }
  propagations += num_props;
  simpDB_props -= num_props;

  return confl;
}

/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt {
  ClauseAllocator &ca;
  reduceDB_lt(ClauseAllocator &ca_) : ca(ca_) {}
  bool operator()(ClauseRef x, ClauseRef y) {
    return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity());
  }
};
void Solver::reduceDB() {
  int i, j;
  double extra_lim = cla_inc / learnts.size(); // Remove any clause below this activity

  sort(learnts, reduceDB_lt(ca));
  // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
  // and clauses with activity smaller than 'extra_lim':
  for (i = j = 0; i < learnts.size(); i++) {
    Clause &c = ca[learnts[i]];
    if (c.size() > 2 && !locked(c) && (i < learnts.size() / 2 || c.activity() < extra_lim))
      removeClause(learnts[i]);
    else
      learnts[j++] = learnts[i];
  }
  learnts.shrink(i - j);
  checkGarbage();
}

void Solver::removeSatisfied(vec<ClauseRef> &cs) {
  int i, j;
  for (i = j = 0; i < cs.size(); i++) {
    Clause &c = ca[cs[i]];
    if (satisfied(c))
      removeClause(cs[i]);
    else {
      // Trim clause:
      assert(value(c[0]) == l_Undef && value(c[1]) == l_Undef);
      for (int k = 2; k < c.size(); k++)
        if (value(c[k]) == l_False) {
          c[k--] = c[c.size() - 1];
          c.pop();
        }
      cs[j++] = cs[i];
    }
  }
  cs.shrink(i - j);
}

void Solver::rebuildOrderHeap() {
  vec<Var> vs;
  for (Var v = 0; v < nVars(); v++)
    if (decision[v] && value(v) == l_Undef)
      vs.push(v);
  order_heap.build(vs);
}

/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify() {
  assert(decisionLevel() == 0);

  if (!ok || propagate() != CRef_Undef)
    return ok = false;

  if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
    return true;

  // Remove satisfied clauses:
  removeSatisfied(learnts);
  if (remove_satisfied) { // Can be turned off.
    removeSatisfied(clauses);

    // TODO: what todo in if 'remove_satisfied' is false?

    // Remove all released variables from the trail:
    for (int i = 0; i < released_vars.size(); i++) {
      assert(seen[released_vars[i]] == 0);
      seen[released_vars[i]] = 1;
    }

    int i, j;
    for (i = j = 0; i < trail.size(); i++)
      if (seen[var(trail[i])] == 0)
        trail[j++] = trail[i];
    trail.shrink(i - j);
    // printf("trail.size()= %d, qhead = %d\n", trail.size(), qhead);
    qhead = trail.size();

    for (int i = 0; i < released_vars.size(); i++)
      seen[released_vars[i]] = 0;

    // Released variables are now ready to be reused:
    append(released_vars, free_vars);
    released_vars.clear();
  }
  checkGarbage();
  rebuildOrderHeap();

  simpDB_assigns = nAssigns();
  simpDB_props = clauses_literals + learnts_literals; // (shouldn't depend on stats really, but it will do for now)

  return true;
}

/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|
|  Description:
|    Search for a model the specified number of conflicts.
|    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
|
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search(int nof_conflicts) {
  assert(ok);
  int backtrack_level;
  int conflictC = 0;
  vec<Literal> learnt_clause;
  starts++;

  for (;;) {
    ClauseRef confl = propagate();
    if (confl != CRef_Undef) {
      // CONFLICT
      conflicts++;
      conflictC++;
      if (decisionLevel() == 0)
        return l_False;

      learnt_clause.clear();
      analyze(confl, learnt_clause, backtrack_level);
      cancelUntil(backtrack_level);

      if (learnt_clause.size() == 1) {
        uncheckedEnqueue(learnt_clause[0]);
      } else {
        ClauseRef cr = ca.alloc(learnt_clause, true);
        learnts.push(cr);
        attachClause(cr);
        clauseBumpActivity(ca[cr]);
        uncheckedEnqueue(learnt_clause[0], cr);
      }

      varDecayActivity();
      claDecayActivity();

      if (--learntsize_adjust_cnt == 0) {
        learntsize_adjust_confl *= learntsize_adjust_inc;
        learntsize_adjust_cnt = (int)learntsize_adjust_confl;
        max_learnts *= learntsize_inc;

        if (verbosity >= 1)
          printf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n",
                 (int)conflicts,
                 (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals,
                 (int)max_learnts, nLearnts(), (double)learnts_literals / nLearnts(), progressEstimate() * 100);
      }

    } else {
      // NO CONFLICT
      if ((nof_conflicts >= 0 && conflictC >= nof_conflicts) || !withinBudget()) {
        // Reached bound on number of conflicts:
        progress_estimate = progressEstimate();
        cancelUntil(0);
        return l_Undef;
      }

      // Simplify the set of problem clauses:
      if (decisionLevel() == 0 && !simplify())
        return l_False;

      if (learnts.size() - nAssigns() >= max_learnts)
        // Reduce the set of learnt clauses:
        reduceDB();

      Literal next = lit_Undef;
      while (decisionLevel() < assumptions.size()) {
        // Perform user provided assumption:
        Literal p = assumptions[decisionLevel()];
        if (value(p) == l_True) {
          // Dummy decision level:
          newDecisionLevel();
        } else if (value(p) == l_False) {
          analyzeFinal(~p, conflict);
          return l_False;
        } else {
          next = p;
          break;
        }
      }

      if (next == lit_Undef) {
        // New variable decision:
        decisions++;
        next = pickBranchLiteral();

        if (next == lit_Undef)
          // Model found:
          return l_True;
      }

      // Increase decision level and enqueue 'next'
      newDecisionLevel();
      uncheckedEnqueue(next);
    }
  }
}

double Solver::progressEstimate() const {
  double progress = 0;
  double F = 1.0 / nVars();

  for (int i = 0; i <= decisionLevel(); i++) {
    int beg = i == 0 ? 0 : trail_lim[i - 1];
    int end = i == decisionLevel() ? trail.size() : trail_lim[i];
    progress += pow(F, i) * (end - beg);
  }

  return progress / nVars();
}

/*
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...


 */

static double luby(double y, int x) {

  // Find the finite subsequence that contains index 'x', and the
  // size of that subsequence:
  int size, seq;
  for (size = 1, seq = 0; size < x + 1; seq++, size = 2 * size + 1)
    ;

  while (size - 1 != x) {
    size = (size - 1) >> 1;
    seq--;
    x = x % size;
  }

  return pow(y, seq);
}

// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver::solve_() {
  model.clear();
  conflict.clear();
  if (!ok)
    return l_False;

  solves++;

  max_learnts = nClauses() * learntsize_factor;
  if (max_learnts < min_learnts_lim)
    max_learnts = min_learnts_lim;

  learntsize_adjust_confl = learntsize_adjust_start_confl;
  learntsize_adjust_cnt = (int)learntsize_adjust_confl;
  lbool status = l_Undef;

  if (verbosity >= 1) {
    printf("============================[ Search Statistics ]==============================\n");
    printf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
    printf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
    printf("===============================================================================\n");
  }

  // Search:
  int curr_restarts = 0;
  while (status == l_Undef) {
    double rest_base = luby_restart ? luby(restart_inc, curr_restarts) : pow(restart_inc, curr_restarts);
    status = search(rest_base * restart_first);
    if (!withinBudget())
      break;
    curr_restarts++;
  }

  if (verbosity >= 1)
    printf("===============================================================================\n");

  if (status == l_True) {
    // Extend & copy model:
    model.growTo(nVars());
    for (int i = 0; i < nVars(); i++)
      model[i] = value(i);
  } else if (status == l_False && conflict.size() == 0)
    ok = false;

  cancelUntil(0);
  return status;
}

bool Solver::implies(const vec<Literal> &assumps, vec<Literal> &out) {
  trail_lim.push(trail.size());
  for (int i = 0; i < assumps.size(); i++) {
    Literal a = assumps[i];

    if (value(a) == l_False) {
      cancelUntil(0);
      return false;
    } else if (value(a) == l_Undef)
      uncheckedEnqueue(a);
  }

  unsigned trail_before = trail.size();
  bool ret = true;
  if (propagate() == CRef_Undef) {
    out.clear();
    for (int j = trail_before; j < trail.size(); j++)
      out.push(trail[j]);
  } else
    ret = false;

  cancelUntil(0);
  return ret;
}

//=================================================================================================
// Writing CNF to DIMACS:
//
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec<Var> &map, Var &max) {
  if (map.size() <= x || map[x] == -1) {
    map.growTo(x + 1, -1);
    map[x] = max++;
  }
  return map[x];
}

void Solver::toDimacs(FILE *f, Clause &c, vec<Var> &map, Var &max) {
  if (satisfied(c))
    return;

  for (int i = 0; i < c.size(); i++)
    if (value(c[i]) != l_False)
      fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max) + 1);
  fprintf(f, "0\n");
}

void Solver::toDimacs(const char *file, const vec<Literal> &assumps) {
  FILE *f = fopen(file, "wr");
  if (f == NULL)
    fprintf(stderr, "could not open file %s\n", file), exit(1);
  toDimacs(f, assumps);
  fclose(f);
}

void Solver::toDimacs(FILE *f, const vec<Literal> &assumps) {
  // Handle case when solver is in contradictory state:
  if (!ok) {
    fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
    return;
  }

  vec<Var> map;
  Var max = 0;

  // Cannot use removeClauses here because it is not safe
  // to deallocate them at this point. Could be improved.
  int cnt = 0;
  for (int i = 0; i < clauses.size(); i++)
    if (!satisfied(ca[clauses[i]]))
      cnt++;

  for (int i = 0; i < clauses.size(); i++)
    if (!satisfied(ca[clauses[i]])) {
      Clause &c = ca[clauses[i]];
      for (int j = 0; j < c.size(); j++)
        if (value(c[j]) != l_False)
          mapVar(var(c[j]), map, max);
    }

  // Assumptions are added as unit clauses:
  cnt += assumps.size();

  fprintf(f, "p cnf %d %d\n", max, cnt);

  for (int i = 0; i < assumps.size(); i++) {
    assert(value(assumps[i]) != l_False);
    fprintf(f, "%s%d 0\n", sign(assumps[i]) ? "-" : "", mapVar(var(assumps[i]), map, max) + 1);
  }

  for (int i = 0; i < clauses.size(); i++)
    toDimacs(f, ca[clauses[i]], map, max);

  if (verbosity > 0)
    printf("Wrote DIMACS with %d variables and %d clauses.\n", max, cnt);
}

void Solver::printStats() const {
  double cpu_time = cpuTime();
  double mem_used = memUsedPeak();
  printf("restarts              : %" PRIu64 "\n", starts);
  printf("conflicts             : %-12" PRIu64 "   (%.0f /sec)\n", conflicts, conflicts / cpu_time);
  printf("decisions             : %-12" PRIu64 "   (%4.2f %% random) (%.0f /sec)\n", decisions, (float)rnd_decisions * 100 / (float)decisions, decisions / cpu_time);
  printf("propagations          : %-12" PRIu64 "   (%.0f /sec)\n", propagations, propagations / cpu_time);
  printf("conflict literals     : %-12" PRIu64 "   (%4.2f %% deleted)\n", tot_literals, (max_literals - tot_literals) * 100 / (double)max_literals);
  if (mem_used != 0)
    printf("Memory used           : %.2f MB\n", mem_used);
  printf("CPU time              : %g s\n", cpu_time);
}

//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator &to) {
  // All watchers:
  //
  watches.cleanAll();
  for (int v = 0; v < nVars(); v++)
    for (int s = 0; s < 2; s++) {
      Literal p = mkLiteral(v, s);
      vec<Watcher> &ws = watches[p];
      for (int j = 0; j < ws.size(); j++)
        ca.reloc(ws[j].cref, to);
    }

  // All reasons:
  //
  for (int i = 0; i < trail.size(); i++) {
    Var v = var(trail[i]);

    // Note: it is not safe to call 'locked()' on a relocated clause. This is why we keep
    // 'dangling' reasons here. It is safe and does not hurt.
    if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)]))) {
      assert(!isRemoved(reason(v)));
      ca.reloc(vardata[v].reason, to);
    }
  }

  // All learnt:
  //
  int i, j;
  for (i = j = 0; i < learnts.size(); i++)
    if (!isRemoved(learnts[i])) {
      ca.reloc(learnts[i], to);
      learnts[j++] = learnts[i];
    }
  learnts.shrink(i - j);

  // All original:
  //
  for (i = j = 0; i < clauses.size(); i++)
    if (!isRemoved(clauses[i])) {
      ca.reloc(clauses[i], to);
      clauses[j++] = clauses[i];
    }
  clauses.shrink(i - j);
}

void Solver::garbageCollect() {
  // Initialize the next region to a size corresponding to the estimated utilization degree. This
  // is not precise but should avoid some unnecessary reallocations for the new region:
  ClauseAllocator to(ca.size() - ca.wasted());

  relocAll(to);
  if (verbosity >= 2)
    printf("|  Garbage collection:   %12d bytes => %12d bytes             |\n",
           ca.size() * ClauseAllocator::Unit_Size, to.size() * ClauseAllocator::Unit_Size);
  to.moveTo(ca);
}
