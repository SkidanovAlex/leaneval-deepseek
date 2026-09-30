import Mathlib
import Submission.Work.BMF.recursion.I1I2Defs
import Submission.Work.BMF.recursion.integral_normSq_eq_card
import Submission.Work.BMF.recursion.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

/-!
# `I1` as the `L²` mean square of `F1`

This file proves the mean-value identity

`I1 S k Q p hkS = ∫ θ, ‖F1 S k Q p hkS θ‖²`,

i.e. the combinatorial count `I1` (pairs of tuples with pairwise distinct head modulo `p`
and equal moment vectors) is the `L²` norm squared of the exponential sum `F1` over the
same index set.

The proof composes three ingredients:

* `I1_eq_pairCard`: `I1` counts the pairs `(x,y)` in `i1Set` with equal moment vectors,
  i.e. it is the cardinality of `pairMomSet S k Q (i1Set S k Q p hkS)`;
* `pairMomSet_card_eq` (below): that cardinality can be read off from the pure `Finset.univ`
  of the subtype `{x // x ∈ i1Set ...}` that `integral_normSq_eq_card` needs;
* `integral_normSq_eq_card`: the `L²` mean square of a character sum equals the number of
  pairs on which the moment map agrees.
-/

namespace Work.BMF.recursion

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Reading the number of pairs with equal moment vectors off the subtype of the ambient
index set: this is the bridge between `pairMomSet` (a filter on `s.product s`) and the
`Finset.univ.filter` count produced by `integral_normSq_eq_card`.  -/
lemma pairMomSet_card_eq (S k Q : ℕ) (s : Finset (Tup S Q)) :
    (pairMomSet S k Q s).card
      = ((Finset.univ : Finset ({x // x ∈ s} × {x // x ∈ s})).filter
          (fun q => Submission.Vinogradov.powerSums k q.1.1 =
                    Submission.Vinogradov.powerSums k q.2.1)).card := by
  classical
  unfold pairMomSet
  refine Finset.card_bij (fun q hq => (⟨q.1, ?_⟩, ⟨q.2, ?_⟩)) ?_ ?_ ?_
  · exact (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1
  · exact (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).2
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.mem_filter.mp hq).2
  · intro a1 ha1 a2 ha2 heq
    have h1 : a1.1 = a2.1 := congrArg (fun z => z.1.1) heq
    have h2 : a1.2 = a2.2 := congrArg (fun z => z.2.1) heq
    exact Prod.ext h1 h2
  · intro b hb
    have hb' : Submission.Vinogradov.powerSums k b.1.1 = Submission.Vinogradov.powerSums k b.2.1 :=
      (Finset.mem_filter.mp hb).2
    refine ⟨(b.1.1, b.2.1), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_product, Finset.product_eq_sprod]
      exact ⟨⟨b.1.2, b.2.2⟩, hb'⟩
    · exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)

/-- `F1` is the sum of the Fourier characters indexed by the *subtype* of `i1Set`, which is
the form in which `integral_normSq_eq_card` consumes it. -/
lemma F1_eq_subtype (S k Q p : ℕ) (hkS : k ≤ S) :
    F1 S k Q p hkS
      = fun θ => ∑ i : {x // x ∈ i1Set S k Q p hkS},
          UnitAddTorus.mFourier (Submission.Vinogradov.powerSums k i.1) θ := by
  funext θ
  unfold F1
  rw [← Finset.sum_attach (i1Set S k Q p hkS)
    (fun x => UnitAddTorus.mFourier (Submission.Vinogradov.powerSums k x) θ)]
  rfl

theorem I1_eq_integral (S k Q p : ℕ) (hkS : k ≤ S) :
    (I1 S k Q p hkS : ℝ) = ∫ θ : UnitAddTorus (Fin (k + 1)), ‖F1 S k Q p hkS θ‖ ^ 2 := by
  classical
  have hcard := pairMomSet_card_eq S k Q (i1Set S k Q p hkS)
  have hchar := integral_normSq_eq_card (k + 1) {x // x ∈ i1Set S k Q p hkS}
    (fun i => Submission.Vinogradov.powerSums k i.1)
  rw [I1_eq_pairCard S k Q p hkS, hcard, ← hchar]
  apply integral_congr_ae
  filter_upwards with θ
  rw [F1_eq_subtype]

end

end Work.BMF.recursion
