import Mathlib
import Submission.Work.PL.Defs

/-!
# Shelling the barycentric subdivision of a simplex (A4 `PL/Shell`)

Combinatorial objects for `Work.PL.Shell.*`.

Conventions (the "shell form" of the lead's `NOTES_LEAD_poincare_engulf.md` §3):

* `bary S` is the centroid of a finite set of points of `PL.E N`.
* A *flag* of a finite set `Δ` of vertices is an enumeration `l = [π₀, …, π_d]` of the
  vertices of `Δ`; its `i`-th *prefix set* is `prefAt l i = {π₀,…,π_i}`.  The top
  simplices of the barycentric subdivision `sd Δ` are the `(prefixes l).image bary`.
* `flagEnum vs` enumerates the flags of `vs` in the reverse-lexicographic order of the
  key `(rk π_d, …, rk π₀)`, where `rk` ranks the vertices with `τ₁` first; it is defined
  recursively by the last vertex (the "sectors" of §3.2 of the lead's notes).
* `splitOf Δ T rk l` is the attaching set `τ₁'(π)` of the flag `l`: the facets opposite
  the *ascent* vertices `bary {π₀..π_i}` (`i < d`, `rk π_i < rk π_{i+1}`), together with
  `bary Δ` when `π_d ∈ T`.
* `sdIter r Δ T` iterates the construction: each small simplex of `sd^r Δ` is
  subdivided with its attaching set as the new `τ₁` (the rank then puts those vertices
  first, via `subList`/`subRank`).
-/

open Set Metric Finset
open scoped BigOperators

namespace Work.PL.Shell

noncomputable section

variable {N : ℕ}

/-- Centroid ("barycentre") of a finite set of points of `E N`. -/
def bary (S : Finset (PL.E N)) : PL.E N := (S.card : ℝ)⁻¹ • ∑ x ∈ S, x

/-- The `k`-th prefix set (as a `Finset`) of a list. -/
def prefAt {α : Type*} [DecidableEq α] (l : List α) (k : ℕ) : Finset α := (l.take (k + 1)).toFinset

/-- The chain of prefix sets of a list. -/
def prefixes {α : Type*} [DecidableEq α] (l : List α) : Finset (Finset α) :=
  (Finset.range l.length).image fun i => prefAt l i

/-- Reverse-lexicographic comparison of the key of two flags: compare `(rk π_d, …, rk π₀)`
lexicographically, i.e. look at the first position (from the top) where the two keys
differ. -/
def keyLt {α : Type*} [LT α] (a b : List α) : Prop :=
  ∃ i, i < a.length ∧ a.take i = b.take i ∧ ∃ x y, a[i]? = some x ∧ b[i]? = some y ∧ x < y

/-- Enumeration of the flags of a list in reverse-lexicographic order of the key
`(rk π_d, …, rk π₀)`: recursively by the last vertex, the vertices being processed in the
order of the list. -/
def flagEnum : List (PL.E N) → List (List (PL.E N))
  | [] => [[]]
  | vs => vs.flatMap fun m => (flagEnum (vs.erase m)).map fun t => t ++ [m]
termination_by vs => vs.length
decreasing_by
  have hm : m ∈ vs := by assumption
  rw [List.length_erase_of_mem hm]
  have : 0 < vs.length := List.length_pos_iff_exists_mem.mpr ⟨m, hm⟩
  omega

/-- Auxiliary recursion computing the set of ascent positions (with respect to `rk`) of a
list of consecutive pairs. -/
def ascIdxAux (rk : PL.E N → ℕ) : List (PL.E N × PL.E N) → ℕ → Finset ℕ
  | [], _ => ∅
  | (p :: ps), i => if rk p.1 < rk p.2 then insert i (ascIdxAux rk ps (i + 1))
                    else ascIdxAux rk ps (i + 1)

/-- The set of ascent positions of the flag `l` with respect to the rank `rk`. -/
def ascIdx (rk : PL.E N → ℕ) (l : List (PL.E N)) : Finset ℕ := ascIdxAux rk (l.zip l.tail) 0

/-- The attaching set `τ₁'(π)` of the flag `l`: the vertices opposite which the new small
simplex attaches, i.e. the centroids of the prefix sets at the ascent positions, together
with `bary Δ` when the last vertex of the flag lies in `T`. -/
def splitOf (Δ T : Finset (PL.E N)) (rk : PL.E N → ℕ) (l : List (PL.E N)) : Finset (PL.E N) :=
  let as := (ascIdx rk l).image fun i => bary (prefAt l i)
  if ∃ v, l.getLast? = some v ∧ v ∈ T then insert (bary Δ) as else as

/-- The vertex list of a simplex `σ` with splitting `T`, with the vertices of `T ∩ σ`
first: this is the order with respect to which `subRank` ranks the vertices. -/
def subList (σ T : Finset (PL.E N)) : List (PL.E N) :=
  (T.filter (· ∈ σ)).toList ++ (σ \ T).toList

/-- The rank of the vertices of `σ` for the subdivision of `σ` with splitting `T`:
`T`-vertices first. -/
def subRank (σ T : Finset (PL.E N)) : PL.E N → ℕ := fun x => (subList σ T).idxOf x

/-- The ordered list of (small simplex, attaching set) pairs of the barycentric
subdivision of the simplex `σ` with splitting `T`. -/
def sd1Data (σ T : Finset (PL.E N)) : List ((Finset (PL.E N)) × (Finset (PL.E N))) :=
  (flagEnum (subList σ T)).map fun l =>
    ((prefixes l).image bary, splitOf σ T (subRank σ T) l)

/-- Shelling data of the `r`-fold barycentric subdivision of the simplex `Δ` with
splitting `T`: a list of pairs (small simplex, attaching set). -/
def sdIter : ℕ → Finset (PL.E N) → Finset (PL.E N) →
    List ((Finset (PL.E N)) × (Finset (PL.E N)))
  | 0, Δ, T => [(Δ, T)]
  | r + 1, Δ, T => (sdIter r Δ T).flatMap fun p => sd1Data p.1 p.2

/-- The shelling order of the `r`-fold barycentric subdivision of `Δ` w.r.t. `T`. -/
def shellOrd (r : ℕ) (Δ T : Finset (PL.E N)) : List (Finset (PL.E N)) :=
  (sdIter r Δ T).map (·.1)

/-- The attaching set of the `i`-th step of the shelling order. -/
def shellSplit (r : ℕ) (Δ T : Finset (PL.E N)) (i : ℕ) : Finset (PL.E N) :=
  ((sdIter r Δ T).getD i (∅, ∅)).2

/-- The union of the simplices of the first `i` elements of a list of vertex sets. -/
def preUnion (ord : List (Finset (PL.E N))) (i : ℕ) : Set (PL.E N) :=
  ⋃ j ∈ Finset.range i, PL.simp (ord.getD j ∅)

end

end Work.PL.Shell
