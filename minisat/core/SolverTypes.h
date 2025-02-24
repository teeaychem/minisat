/***********************************************************************************[SolverTypes.h]
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

#ifndef Minisat_SolverTypes_h
#define Minisat_SolverTypes_h

#include <assert.h>

#include "minisat/mtl/Alg.h"
#include "minisat/mtl/Alloc.h"
#include "minisat/mtl/IntMap.h"
#include "minisat/mtl/IntTypes.h"
#include "minisat/mtl/Map.h"
#include "minisat/mtl/Vec.h"

namespace Minisat {

//=================================================================================================
// Variables, literals, lifted booleans, clauses:

// NOTE! Variables are just integers. No abstraction here. They should be chosen from 0..N,
// so that they can be used as array indices.

typedef int Var;
#if defined(MINISAT_CONSTANTS_AS_MACROS)
#define var_Undef (-1)
#else
const Var var_Undef = -1;
#endif

struct Literal {
  int x;

  // Use this as a constructor:
  friend Literal mkLit(Var var, bool sign);

  bool operator==(Literal p) const { return x == p.x; }
  bool operator!=(Literal p) const { return x != p.x; }
  bool operator<(Literal p) const { return x < p.x; } // '<' makes p, ~p adjacent in the ordering.
};

// Negation of l is l XOR 1.
inline Literal mkLiteral(Var var, bool sign = false) {
  Literal p;
  p.x = var + var + (int)sign;
  return p;
}
inline Literal operator~(Literal p) {
  Literal q;
  q.x = p.x ^ 1;
  return q;
}
inline Literal operator^(Literal p, bool b) {
  Literal q;
  q.x = p.x ^ (unsigned int)b;
  return q;
}
inline bool sign(Literal p) { return p.x & 1; }
inline int var(Literal p) { return p.x >> 1; }

// Mapping Literals to and from compact integers suitable for array indexing:
inline int toInt(Var v) { return v; }
inline int toInt(Literal p) { return p.x; }
inline Literal toLit(int i) {
  Literal p;
  p.x = i;
  return p;
}

// const Lit lit_Undef = mkLit(var_Undef, false);  // }- Useful special constants.
// const Lit lit_Error = mkLit(var_Undef, true );  // }

const Literal lit_Undef = {-2}; // }- Useful special constants.
const Literal lit_Error = {-1}; // }

struct MkIndexLit {
  vec<Literal>::Size operator()(Literal l) const { return vec<Literal>::Size(l.x); }
};

template <class T>
class VMap : public IntMap<Var, T> {};
template <class T>
class LMap : public IntMap<Literal, T, MkIndexLit> {};
class LSet : public IntSet<Literal, MkIndexLit> {};

//=================================================================================================
// Lifted booleans:
//
// NOTE: this implementation is optimized for the case when comparisons between values are mostly
//       between one variable and one constant. Some care had to be taken to make sure that gcc
//       does enough constant propagation to produce sensible code, and this appears to be somewhat
//       fragile unfortunately.

class lbool {
  uint8_t value;

public:
  explicit lbool(uint8_t v) : value(v) {}

  lbool() : value(0) {}
  explicit lbool(bool x) : value(!x) {}

  bool operator==(lbool b) const { return ((b.value & 2) & (value & 2)) | (!(b.value & 2) & (value == b.value)); }
  bool operator!=(lbool b) const { return !(*this == b); }
  lbool operator^(bool b) const { return lbool((uint8_t)(value ^ (uint8_t)b)); }

  lbool operator&&(lbool b) const {
    uint8_t sel = (this->value << 1) | (b.value << 3);
    uint8_t v = (0xF7F755F4 >> sel) & 3;
    return lbool(v);
  }

  lbool operator||(lbool b) const {
    uint8_t sel = (this->value << 1) | (b.value << 3);
    uint8_t v = (0xFCFCF400 >> sel) & 3;
    return lbool(v);
  }

  friend int toInt(lbool l);
  friend lbool toLbool(int v);
};
inline int toInt(lbool l) { return l.value; }
inline lbool toLbool(int v) { return lbool((uint8_t)v); }

#if defined(MINISAT_CONSTANTS_AS_MACROS)
#define l_True (lbool((uint8_t)0)) // gcc does not do constant propagation if these are real constants.
#define l_False (lbool((uint8_t)1))
#define l_Undef (lbool((uint8_t)2))
#else
const lbool l_True((uint8_t)0);
const lbool l_False((uint8_t)1);
const lbool l_Undef((uint8_t)2);
#endif

//=================================================================================================
// Clause -- a simple class for representing a clause:

class Clause;
typedef RegionAllocator<uint32_t>::Ref ClauseRef;

class Clause {
  struct {
    unsigned mark : 2;
    unsigned learnt : 1;
    unsigned has_extra : 1;
    unsigned reloced : 1;
    unsigned size : 27;
  } header;
  union {
    Literal lit;
    float act;
    uint32_t abs;
    ClauseRef rel;
  } data[0];

  friend class ClauseAllocator;

  // NOTE: This constructor cannot be used directly (doesn't allocate enough memory).
  Clause(const vec<Literal> &ps, bool use_extra, bool learnt) {
    header.mark = 0;
    header.learnt = learnt;
    header.has_extra = use_extra;
    header.reloced = 0;
    header.size = ps.size();

    for (int i = 0; i < ps.size(); i++)
      data[i].lit = ps[i];

    if (header.has_extra) {
      if (header.learnt)
        data[header.size].act = 0;
      else
        calcAbstraction();
    }
  }

  // NOTE: This constructor cannot be used directly (doesn't allocate enough memory).
  Clause(const Clause &from, bool use_extra) {
    header = from.header;
    header.has_extra = use_extra; // NOTE: the copied clause may lose the extra field.

    for (int i = 0; i < from.size(); i++)
      data[i].lit = from[i];

    if (header.has_extra) {
      if (header.learnt)
        data[header.size].act = from.data[header.size].act;
      else
        data[header.size].abs = from.data[header.size].abs;
    }
  }

public:
  void calcAbstraction() {
    assert(header.has_extra);
    uint32_t abstraction = 0;
    for (int i = 0; i < size(); i++)
      abstraction |= 1 << (var(data[i].lit) & 31);
    data[header.size].abs = abstraction;
  }

  int size() const { return header.size; }
  void shrink(int i) {
    assert(i <= size());
    if (header.has_extra)
      data[header.size - i] = data[header.size];
    header.size -= i;
  }
  void pop() { shrink(1); }
  bool learnt() const { return header.learnt; }
  bool has_extra() const { return header.has_extra; }
  uint32_t mark() const { return header.mark; }
  void mark(uint32_t mark) { header.mark = mark; }
  const Literal &last() const { return data[header.size - 1].lit; }

  bool reloced() const { return header.reloced; }
  ClauseRef relocation() const { return data[0].rel; }
  void relocate(ClauseRef c) {
    header.reloced = 1;
    data[0].rel = c;
  }

  // NOTE: somewhat unsafe to change the clause in-place! Must manually call 'calcAbstraction' afterwards for
  //       subsumption operations to behave correctly.
  Literal &operator[](int i) { return data[i].lit; }
  Literal operator[](int i) const { return data[i].lit; }
  operator const Literal *(void) const { return (Literal *)data; }

  float &activity() {
    assert(header.has_extra);
    return data[header.size].act;
  }
  uint32_t abstraction() const {
    assert(header.has_extra);
    return data[header.size].abs;
  }

  Literal subsumes(const Clause &other) const;
  void strengthen(Literal p);
};

//=================================================================================================
// ClauseAllocator -- a simple class for allocating memory for clauses:

const ClauseRef CRef_Undef = RegionAllocator<uint32_t>::Ref_Undef;
class ClauseAllocator {
  RegionAllocator<uint32_t> ra;

  static uint32_t clauseWord32Size(int size, bool has_extra) {
    return (sizeof(Clause) + (sizeof(Literal) * (size + (int)has_extra))) / sizeof(uint32_t);
  }

public:
  enum { Unit_Size = RegionAllocator<uint32_t>::Unit_Size };

  bool extra_clause_field;

  ClauseAllocator(uint32_t start_cap) : ra(start_cap), extra_clause_field(false) {}
  ClauseAllocator() : extra_clause_field(false) {}

  void moveTo(ClauseAllocator &to) {
    to.extra_clause_field = extra_clause_field;
    ra.moveTo(to.ra);
  }

  ClauseRef alloc(const vec<Literal> &ps, bool learnt = false) {
    assert(sizeof(Literal) == sizeof(uint32_t));
    assert(sizeof(float) == sizeof(uint32_t));
    bool use_extra = learnt | extra_clause_field;
    ClauseRef cid = ra.alloc(clauseWord32Size(ps.size(), use_extra));
    new (lea(cid)) Clause(ps, use_extra, learnt);

    return cid;
  }

  ClauseRef alloc(const Clause &from) {
    bool use_extra = from.learnt() | extra_clause_field;
    ClauseRef cid = ra.alloc(clauseWord32Size(from.size(), use_extra));
    new (lea(cid)) Clause(from, use_extra);
    return cid;
  }

  uint32_t size() const { return ra.size(); }
  uint32_t wasted() const { return ra.wasted(); }

  // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
  Clause &operator[](ClauseRef r) { return (Clause &)ra[r]; }
  const Clause &operator[](ClauseRef r) const { return (Clause &)ra[r]; }
  Clause *lea(ClauseRef r) { return (Clause *)ra.lea(r); }
  const Clause *lea(ClauseRef r) const {
    return (Clause *)ra.lea(r);
    ;
  }
  ClauseRef ael(const Clause *t) { return ra.ael((uint32_t *)t); }

  void free(ClauseRef cid) {
    Clause &c = operator[](cid);
    ra.free(clauseWord32Size(c.size(), c.has_extra()));
  }

  void reloc(ClauseRef &cr, ClauseAllocator &to) {
    Clause &c = operator[](cr);

    if (c.reloced()) {
      cr = c.relocation();
      return;
    }

    cr = to.alloc(c);
    c.relocate(cr);
  }
};

//=================================================================================================
// Simple iterator classes (for iterating over clauses and top-level assignments):

class ClauseIterator {
  const ClauseAllocator &ca;
  const ClauseRef *crefs;

public:
  ClauseIterator(const ClauseAllocator &_ca, const ClauseRef *_crefs) : ca(_ca), crefs(_crefs) {}

  void operator++() { crefs++; }
  const Clause &operator*() const { return ca[*crefs]; }

  // NOTE: does not compare that references use the same clause-allocator:
  bool operator==(const ClauseIterator &ci) const { return crefs == ci.crefs; }
  bool operator!=(const ClauseIterator &ci) const { return crefs != ci.crefs; }
};

class TrailIterator {
  const Literal *lits;

public:
  TrailIterator(const Literal *_lits) : lits(_lits) {}

  void operator++() { lits++; }
  Literal operator*() const { return *lits; }

  bool operator==(const TrailIterator &ti) const { return lits == ti.lits; }
  bool operator!=(const TrailIterator &ti) const { return lits != ti.lits; }
};

//=================================================================================================
// OccLists -- a class for maintaining occurence lists with lazy deletion:

template <class K, class Vec, class Deleted, class MkIndex = MkIndexDefault<K> >
class OccLists {
  IntMap<K, Vec, MkIndex> occs;
  IntMap<K, char, MkIndex> dirty;
  vec<K> dirties;
  Deleted deleted;

public:
  OccLists(const Deleted &d, MkIndex _index = MkIndex()) : occs(_index),
                                                           dirty(_index),
                                                           deleted(d) {}

  void init(const K &idx) {
    occs.reserve(idx);
    occs[idx].clear();
    dirty.reserve(idx, 0);
  }

  Vec &operator[](const K &idx) { return occs[idx]; }

  Vec &lookup(const K &idx) {
    if (dirty[idx])
      clean(idx);
    return occs[idx];
  }

  void cleanAll();

  void clean(const K &idx);

  void smudge(const K &idx) {
    if (dirty[idx] == 0) {
      dirty[idx] = 1;
      dirties.push(idx);
    }
  }

  void clear(bool free = true) {
    occs.clear(free);
    dirty.clear(free);
    dirties.clear(free);
  }
};

template <class K, class Vec, class Deleted, class MkIndex>
void OccLists<K, Vec, Deleted, MkIndex>::cleanAll() {
  for (int i = 0; i < dirties.size(); i++)
    // Dirties may contain duplicates so check here if a variable is already cleaned:
    if (dirty[dirties[i]])
      clean(dirties[i]);
  dirties.clear();
}

template <class K, class Vec, class Deleted, class MkIndex>
void OccLists<K, Vec, Deleted, MkIndex>::clean(const K &idx) {
  Vec &vec = occs[idx];
  int i, j;
  for (i = j = 0; i < vec.size(); i++)
    if (!deleted(vec[i]))
      vec[j++] = vec[i];
  vec.shrink(i - j);
  dirty[idx] = 0;
}

//=================================================================================================
// CMap -- a class for mapping clauses to values:

template <class T>
class CMap {
  struct CRefHash {
    uint32_t operator()(ClauseRef cr) const { return (uint32_t)cr; }
  };

  typedef Map<ClauseRef, T, CRefHash> HashTable;
  HashTable map;

public:
  // Size-operations:
  void clear() { map.clear(); }
  int size() const { return map.elems(); }

  // Insert/Remove/Test mapping:
  void insert(ClauseRef cr, const T &t) { map.insert(cr, t); }
  void growTo(ClauseRef cr, const T &t) { map.insert(cr, t); } // NOTE: for compatibility
  void remove(ClauseRef cr) { map.remove(cr); }
  bool has(ClauseRef cr, T &t) { return map.peek(cr, t); }

  // Vector interface (the clause 'c' must already exist):
  const T &operator[](ClauseRef cr) const { return map[cr]; }
  T &operator[](ClauseRef cr) { return map[cr]; }

  // Iteration (not transparent at all at the moment):
  int bucket_count() const { return map.bucket_count(); }
  const vec<typename HashTable::Pair> &bucket(int i) const { return map.bucket(i); }

  // Move contents to other map:
  void moveTo(CMap &other) { map.moveTo(other.map); }

  // TMP debug:
  void debug() {
    printf(" --- size = %d, bucket_count = %d\n", size(), map.bucket_count());
  }
};

/*_________________________________________________________________________________________________
|
|  subsumes : (other : const Clause&)  ->  Lit
|
|  Description:
|       Checks if clause subsumes 'other', and at the same time, if it can be used to simplify 'other'
|       by subsumption resolution.
|
|    Result:
|       lit_Error  - No subsumption or simplification
|       lit_Undef  - Clause subsumes 'other'
|       p          - The literal p can be deleted from 'other'
|________________________________________________________________________________________________@*/
inline Literal Clause::subsumes(const Clause &other) const {
  // if (other.size() < size() || (extra.abst & ~other.extra.abst) != 0)
  // if (other.size() < size() || (!learnt() && !other.learnt() && (extra.abst & ~other.extra.abst) != 0))
  assert(!header.learnt);
  assert(!other.header.learnt);
  assert(header.has_extra);
  assert(other.header.has_extra);
  if (other.header.size < header.size || (data[header.size].abs & ~other.data[other.header.size].abs) != 0)
    return lit_Error;

  Literal ret = lit_Undef;
  const Literal *c = (const Literal *)(*this);
  const Literal *d = (const Literal *)other;

  for (unsigned i = 0; i < header.size; i++) {
    // search for c[i] or ~c[i]
    for (unsigned j = 0; j < other.header.size; j++)
      if (c[i] == d[j])
        goto ok;
      else if (ret == lit_Undef && c[i] == ~d[j]) {
        ret = c[i];
        goto ok;
      }

    // did not find it
    return lit_Error;
  ok:;
  }

  return ret;
}

inline void Clause::strengthen(Literal p) {
  remove(*this, p);
  calcAbstraction();
}

//=================================================================================================
} // namespace Minisat

#endif
