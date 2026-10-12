import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseFixB1S.hopChildCoeffSumB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.a0A2QJointHopChildReindex` — reindexing the child (edge) double sum

The hop (edge) layer sums each *edge* `(i, p)`, `p ∈ disjPairs N`, `i ∈ p.1`, i.e. each `P`-slot `i`
of a disjoint pair, against the weight of the **child** `c_i(p) = hopChild i p` obtained by moving
the slot `i` from the `P`-component into the `Q`-component:

    Σᵢ Σ_{p ∋ i} G(c_i(p))  =  Σ_q |q.2| · G(q) .

The reason for the weight `|q.2|` on the right is the fibre transfer: for a fixed slot `i` the child
map is a bijection from the `P`-slot-`i` pairs onto the `Q`-slot-`i` pairs, with inverse the parent
map `hopParent i q = (insert i q.1, q.2.erase i)`; summing over `i` therefore hits every pair `q`
exactly once for every slot `i ∈ q.2`, i.e. `|q.2|` times.

This is the unweighted companion of `hopChildCoeffSumB1` (which carries the same reindexing with the
coefficient `|p.1| + 1 + μV`), and mirrors `pairIdxInsertReindex` (the same identity with the
components exchanged).

Contents:
* §1 `hopParent_hopChild` — the parent map is a left inverse of the child map at a `P`-slot;
* §2 `hopChildFibreSum` — the fibre bijection for a fixed slot;
* §3 `hopChildCardMulFibre` — counting the fibres (`Σ_q |q.2| G q = Σᵢ Σ_{q ∋ i} G q`);
* §4 `a0A2QJointHopChildReindex` — the identity itself.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseFixB1S

open Work.BoseFixB1

set_option autoImplicit false

/-! ## 1. The parent map is a left inverse of the child map -/

/-- At a `P`-slot `i` of a disjoint pair, the parent of the child is the pair itself:
`hopParent i (hopChild i p) = p`. -/
theorem hopParent_hopChild {N : ℕ} {i : Fin N} {p : Finset (Fin N) × Finset (Fin N)}
    (hp : p ∈ Work.BoseFixB1.disjPairs N) (hi : i ∈ p.1) : hopParent i (hopChild i p) = p := by
  have hni : i ∉ p.2 :=
    fun h => (Finset.disjoint_left.mp (Work.BoseFixB1.mem_disjPairs.mp hp)) hi h
  unfold hopParent hopChild
  rw [Finset.insert_erase hi, Finset.erase_insert hni]

/-! ## 2. The fibre bijection for a fixed slot -/

/-- **The fibre bijection.** For a fixed slot `i`, the child map is a bijection from the disjoint
pairs whose `P`-component contains `i` onto the disjoint pairs whose `Q`-component contains `i`. -/
theorem hopChildFibreSum {N : ℕ} (i : Fin N) (G : Finset (Fin N) × Finset (Fin N) → ℝ) :
    (∑ p ∈ (Work.BoseFixB1.disjPairs N).filter (fun p => i ∈ p.1), G (hopChild i p))
      = ∑ q ∈ (Work.BoseFixB1.disjPairs N).filter (fun q => i ∈ q.2), G q := by
  classical
  refine Finset.sum_bij' (fun p _ => hopChild i p) (fun q _ => hopParent i q) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hopChild_mem_disjPairs hp.1 hp.2, mem_hopChild_snd i p⟩
  · intro q hq
    rw [Finset.mem_filter] at hq ⊢
    exact ⟨hopParent_mem hq.1 hq.2, mem_hopParent_fst i q⟩
  · intro p hp
    rw [Finset.mem_filter] at hp
    exact hopParent_hopChild hp.1 hp.2
  · intro q hq
    rw [Finset.mem_filter] at hq
    exact hopChild_hopParent hq.1 hq.2
  · intro p _
    rfl

/-! ## 3. Counting the fibres -/

/-- **Counting the fibres.** Weighting each pair by the cardinality of its `Q`-component is the same
as summing over the slots and the pairs whose `Q`-component contains that slot. -/
theorem hopChildCardMulFibre {N : ℕ} (G : Finset (Fin N) × Finset (Fin N) → ℝ) :
    (∑ q ∈ (Work.BoseFixB1.disjPairs N).filter (fun q => q.2 ≠ ∅), (q.2.card : ℝ) * G q)
      = ∑ i : Fin N, ∑ q ∈ (Work.BoseFixB1.disjPairs N).filter (fun q => i ∈ q.2), G q := by
  classical
  have h1 : ∀ q : Finset (Fin N) × Finset (Fin N),
      (if q.2 ≠ ∅ then (q.2.card : ℝ) * G q else 0)
        = ∑ i : Fin N, (if i ∈ q.2 then G q else 0) := by
    intro q
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    by_cases hq : q.2 = ∅
    · simp [hq]
    · simp [hq]
  calc (∑ q ∈ (Work.BoseFixB1.disjPairs N).filter (fun q => q.2 ≠ ∅), (q.2.card : ℝ) * G q)
      = ∑ q ∈ Work.BoseFixB1.disjPairs N, ∑ i : Fin N, (if i ∈ q.2 then G q else 0) := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl (fun q _ => h1 q)
    _ = ∑ i : Fin N, ∑ q ∈ Work.BoseFixB1.disjPairs N, (if i ∈ q.2 then G q else 0) :=
        Finset.sum_comm
    _ = ∑ i : Fin N, ∑ q ∈ (Work.BoseFixB1.disjPairs N).filter (fun q => i ∈ q.2), G q := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_filter]

/-! ## 4. The reindexing identity -/

/-- **Reindexing the child (edge) double sum.** Summing over the slots `i` and the disjoint pairs
`p` whose `P`-component contains `i`, against the weight of the child `c_i(p)`, is the same as
summing over the disjoint pairs `q` weighted by the cardinality of their `Q`-component. -/
theorem a0A2QJointHopChildReindex {N : ℕ}
    (G : Finset (Fin N) × Finset (Fin N) → ℝ) :
    (∑ i : Fin N, ∑ p ∈ Work.BoseFixB1S.hopPairSet i, G (Work.BoseFixB1S.hopChild i p))
      = ∑ q ∈ Work.BoseFixB1.disjPairs N, (q.2.card : ℝ) * G q := by
  classical
  -- the edges are the `P`-slot-`i` pairs: rewrite slot by slot with the fibre bijection
  have hstep : (∑ i : Fin N, ∑ p ∈ Work.BoseFixB1S.hopPairSet i, G (Work.BoseFixB1S.hopChild i p))
      = ∑ i : Fin N, ∑ q ∈ (Work.BoseFixB1.disjPairs N).filter (fun q => i ∈ q.2), G q :=
    Finset.sum_congr rfl (fun i _ => hopChildFibreSum i G)
  rw [hstep, ← hopChildCardMulFibre G]
  -- pairs with empty `Q`-component contribute `0` on both sides
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  by_cases hq : q.2 = ∅
  · simp [hq]
  · simp [hq]

end Work.BoseFixB1S
