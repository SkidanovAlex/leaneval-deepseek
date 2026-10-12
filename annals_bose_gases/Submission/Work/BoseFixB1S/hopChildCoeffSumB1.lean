import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseFixB1S.HopDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.hopChildCoeffSumB1` — the coefficient bookkeeping of the child map

The sharp Cauchy–Schwarz over the *edges* `(p, i)` with `p ∈ disjPairs N` and `i ∈ p.1`
writes the weight of the child `c_i(p) = hopChild i p` in terms of the parent.  Regrouping the
edge sums by the child gives the identity

    Σᵢ Σ_{p ∋ i} (|p.1| + 1 + μV) · J(c_i p)
      = Σ_q |q.1|·|q.2|·J q + (2 + μV)·Σ_q |q.2|·J q ,

i.e. the coefficient of a child `q` is `(|q.1| + 2 + μV)` and the edge set fibres over `q` with
multiplicity `|q.2|`.

The proof is the bijection between the edge set `{ (i,p) : i ∈ p.1 }` and the set
`{ (q,i) : i ∈ q.2 }` given by `(i,p) ↦ (c_i(p), i)`, whose inverse is
`(q,i) ↦ (i, hopParent i q)`, `hopParent i q = (insert i q.1, q.2.erase i)`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

open Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The **parent** of the pair `q` at the slot `i`: moving the slot `i` from the `Q`-part to the
`P`-part.  This is the inverse of `hopChild i` on the fibres of the child map. -/
def hopParent {N : ℕ} (i : Fin N) (q : Finset (Fin N) × Finset (Fin N)) :
    Finset (Fin N) × Finset (Fin N) :=
  (insert i q.1, q.2.erase i)

/-- The parent of a disjoint pair at a slot of its `Q`-part is again a disjoint pair. -/
lemma hopParent_mem {N : ℕ} {q : Finset (Fin N) × Finset (Fin N)} {i : Fin N}
    (hq : q ∈ Work.BoseFixB1.disjPairs N) (hi : i ∈ q.2) :
    hopParent i q ∈ Work.BoseFixB1.disjPairs N := by
  rw [Work.BoseFixB1.mem_disjPairs] at hq ⊢
  rw [hopParent]
  refine Finset.disjoint_left.mpr fun j hj hj' => ?_
  rw [Finset.mem_insert] at hj
  rw [Finset.mem_erase] at hj'
  rcases hj with rfl | hj
  · exact hj'.1 rfl
  · exact (Finset.disjoint_left.mp hq) hj hj'.2

/-- The slot `i` is a `P`-slot of the parent `hopParent i q`. -/
lemma mem_hopParent_fst {N : ℕ} (i : Fin N) (q : Finset (Fin N) × Finset (Fin N)) :
    i ∈ (hopParent i q).1 := Finset.mem_insert_self i q.1

/-- **`hopParent` is a right inverse of `hopChild`**: the child of the parent of `q` at a slot of
its `Q`-part is `q` itself. -/
lemma hopChild_hopParent {N : ℕ} {q : Finset (Fin N) × Finset (Fin N)} {i : Fin N}
    (hq : q ∈ Work.BoseFixB1.disjPairs N) (hi : i ∈ q.2) :
    hopChild i (hopParent i q) = q := by
  have hq' : Disjoint q.1 q.2 := (Work.BoseFixB1.mem_disjPairs.mp hq)
  have hi1 : i ∉ q.1 := fun h => (Finset.disjoint_left.mp hq') h hi
  unfold hopChild hopParent
  rw [Finset.erase_insert hi1, Finset.insert_erase hi]

/-- The `P`-part of the child has one slot less than the parent's. -/
lemma hopChild_fst_card_cast {N : ℕ} {i : Fin N} {p : Finset (Fin N) × Finset (Fin N)}
    (hi : i ∈ p.1) : ((hopChild i p).1.card : ℝ) = (p.1.card : ℝ) - 1 := by
  have h : (p.1.erase i).card + 1 = p.1.card := Finset.card_erase_add_one hi
  rw [hopChild_fst]
  have h' : ((p.1.erase i).card : ℝ) + 1 = (p.1.card : ℝ) := by exact_mod_cast h
  linarith

/-- **The coefficient bookkeeping of the child map.**  Summing the parent weights
`|p.1| + 1 + μV` over the edges `(p, i)`, `i ∈ p.1`, against a weight `J` of the child, regroups
by the child: each child `q` occurs `|q.2|` times and carries the weight `|q.1| + 2 + μV`. -/
theorem hopChildCoeffSumB1 {N : ℕ} (μ V : ℝ) (J : Finset (Fin N) × Finset (Fin N) → ℝ) :
    (∑ i : Fin N, ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
        ((p.1.card : ℝ) + 1 + μ * V) * J (Work.BoseFixB1S.hopChild i p))
      = (∑ q ∈ Work.BoseFixB1.disjPairs N, (q.1.card : ℝ) * (q.2.card : ℝ) * J q)
        + (2 + μ * V) * (∑ q ∈ Work.BoseFixB1.disjPairs N, (q.2.card : ℝ) * J q) := by
  -- Step 1: the double sum is the sum over the sigma-type of edges `(i,p)`, `p ∈ hopPairSet i`.
  have h1 : (∑ i : Fin N, ∑ p ∈ hopPairSet i,
        ((p.1.card : ℝ) + 1 + μ * V) * J (hopChild i p))
      = ∑ x ∈ (Finset.univ : Finset (Fin N)).sigma (fun i => hopPairSet i),
          ((x.2.1.card : ℝ) + 1 + μ * V) * J (hopChild x.1 x.2) :=
    Finset.sum_sigma' _ _ _
  -- Step 2: the bijection `(i,p) ↦ (hopChild i p, i)` from the edge set to `{(q,i) : i ∈ q.2}`.
  have h2 : (∑ x ∈ (Finset.univ : Finset (Fin N)).sigma (fun i => hopPairSet i),
          ((x.2.1.card : ℝ) + 1 + μ * V) * J (hopChild x.1 x.2))
      = ∑ y ∈ (Work.BoseFixB1.disjPairs N).sigma (fun q => q.2),
          ((y.1.1.card : ℝ) + 2 + μ * V) * J y.1 := by
    refine Finset.sum_bij (fun x _ => ⟨hopChild x.1 x.2, x.1⟩) ?_ ?_ ?_ ?_
    · -- the child of an edge is a pair, and the slot is a `Q`-slot of it
      rintro ⟨i, p⟩ hp
      rw [Finset.mem_sigma] at hp ⊢
      exact ⟨hopChild_mem_disjPairs (mem_hopPairSet.mp hp.2).1 (mem_hopPairSet.mp hp.2).2,
        mem_hopChild_snd i p⟩
    · -- injectivity of the child map on edges
      rintro ⟨i1, p1⟩ hx1 ⟨i2, p2⟩ hx2 heq
      rw [Finset.mem_sigma] at hx1 hx2
      have hi1 : i1 ∈ p1.1 := (mem_hopPairSet.mp hx1.2).2
      have hi2 : i2 ∈ p2.1 := (mem_hopPairSet.mp hx2.2).2
      have hd1 : Disjoint p1.1 p1.2 :=
        Work.BoseFixB1.mem_disjPairs.mp (mem_hopPairSet.mp hx1.2).1
      have hd2 : Disjoint p2.1 p2.2 :=
        Work.BoseFixB1.mem_disjPairs.mp (mem_hopPairSet.mp hx2.2).1
      obtain ⟨heqp, heqi⟩ : hopChild i1 p1 = hopChild i2 p2 ∧ i1 = i2 := by
        simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using heq
      rw [heqi] at heqp
      have hi1' : i2 ∈ p1.1 := heqi ▸ hi1
      have hfst : p1.1.erase i2 = p2.1.erase i2 := by
        have := congrArg Prod.fst heqp
        simpa [hopChild] using this
      have hsnd : insert i2 p1.2 = insert i2 p2.2 := by
        have := congrArg Prod.snd heqp
        simpa [hopChild] using this
      have hn1 : i2 ∉ p1.2 := fun h => (Finset.disjoint_left.mp hd1) hi1' h
      have hn2 : i2 ∉ p2.2 := fun h => (Finset.disjoint_left.mp hd2) hi2 h
      have hp1 : p1.1 = p2.1 := by
        rw [← Finset.insert_erase hi1', ← Finset.insert_erase hi2, hfst]
      have hp2 : p1.2 = p2.2 := by
        rw [← Finset.erase_insert hn1, ← Finset.erase_insert hn2, hsnd]
      have hp : p1 = p2 := Prod.ext hp1 hp2
      rw [hp, heqi]
    · -- surjectivity: the parent of `(q,i)`, `i ∈ q.2`, is an edge with child `q`
      rintro ⟨q, i⟩ hb
      rw [Finset.mem_sigma] at hb
      refine ⟨⟨i, hopParent i q⟩, ?_, ?_⟩
      · rw [Finset.mem_sigma]
        exact ⟨Finset.mem_univ _,
          mem_hopPairSet.mpr ⟨hopParent_mem hb.1 hb.2, mem_hopParent_fst i q⟩⟩
      · rw [hopChild_hopParent hb.1 hb.2]
    · -- the two weights agree: `|p.1| + 1 = |c_i(p).1| + 2`
      rintro ⟨i, p⟩ hp
      rw [Finset.mem_sigma] at hp
      have hi : i ∈ p.1 := (mem_hopPairSet.mp hp.2).2
      have hcoeff : ((hopChild i p).1.card : ℝ) + 2 + μ * V = (p.1.card : ℝ) + 1 + μ * V := by
        have := hopChild_fst_card_cast (p := p) (i := i) hi
        linarith
      rw [hcoeff]
  -- Step 3: perform the sum over the fibre `q.2` of each child.
  have h3 : (∑ y ∈ (Work.BoseFixB1.disjPairs N).sigma (fun q => q.2),
          ((y.1.1.card : ℝ) + 2 + μ * V) * J y.1)
      = ∑ q ∈ Work.BoseFixB1.disjPairs N,
          (q.2.card : ℝ) * (((q.1.card : ℝ) + 2 + μ * V) * J q) := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Finset.sum_const, nsmul_eq_mul]
  -- Step 4: expand the product and split the sum.
  have h4 : (∑ q ∈ Work.BoseFixB1.disjPairs N,
          (q.2.card : ℝ) * (((q.1.card : ℝ) + 2 + μ * V) * J q))
      = (∑ q ∈ Work.BoseFixB1.disjPairs N, (q.1.card : ℝ) * (q.2.card : ℝ) * J q)
        + (2 + μ * V) * (∑ q ∈ Work.BoseFixB1.disjPairs N, (q.2.card : ℝ) * J q) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    show (q.2.card : ℝ) * (((q.1.card : ℝ) + 2 + μ * V) * J q)
        = (q.1.card : ℝ) * (q.2.card : ℝ) * J q + (2 + μ * V) * ((q.2.card : ℝ) * J q)
    ring
  rw [h1, h2, h3, h4]

end Work.BoseFixB1S
