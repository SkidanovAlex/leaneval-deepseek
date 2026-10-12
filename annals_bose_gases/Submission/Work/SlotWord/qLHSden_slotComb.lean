import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SlotWord.slotSplit_integral_slotBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SlotWord

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open Work.PerSector

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {N : ℕ}

/-- **The one-particle sum over a slot splitting.**

For a kernel `g : ℝ³ → ℝ` that vanishes on the slots *outside* `S` (hypothesis `h0`), the sum of
`g` over all `N` particle indices of the reassembled configuration `slotComb S z y` collapses to the
sum over the in-slots `SlotIn N S`. -/
lemma sum_slotComb_eq_sum_slotIn (S : Finset (Fin N)) (z : SlotIn N S → ℝ³)
    (y : SlotOut N S → ℝ³) (g : ℝ³ → ℝ)
    (h0 : ∀ i : Fin N, i ∉ S → g (slotComb S z y i) = 0) :
    (∑ i : Fin N, g (slotComb S z y i)) = ∑ i : SlotIn N S, g (z i) := by
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => h0 i hi)]
  rw [← Finset.sum_attach S (fun i => g (slotComb S z y i))]
  rw [← Finset.univ_eq_attach S]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [slotComb_apply, dif_pos i.2]

/-- **The pair sum over a slot splitting.**

The ordered-distinct-pair sum of `w` over the pairs of `Fin N` that lie *both* in `S`, evaluated on
the reassembled configuration `slotComb S z y` with `z i = x (e i)`, reindexes along `e` to the
ordered-distinct-pair sum of `w` over the pairs of `Fin S.card` evaluated on `x`. -/
lemma pairSet_slotComb_eq (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card)
    (x : X S.card) (y : SlotOut N S → ℝ³) (w : ℝ³ → ℝ³ → ℝ) :
    (∑ p ∈ (pairSet N).filter (fun p => p.1 ∈ S ∧ p.2 ∈ S),
        w (slotComb S (fun i => x (e i)) y p.1) (slotComb S (fun i => x (e i)) y p.2))
      = ∑ q ∈ pairSet S.card, w (x q.1) (x q.2) := by
  classical
  refine Finset.sum_bij'
    (fun a ha => (e ⟨a.1, (Finset.mem_filter.mp ha).2.1⟩,
      e ⟨a.2, (Finset.mem_filter.mp ha).2.2⟩))
    (fun b _ => ((e.symm b.1).1, (e.symm b.2).1)) ?_ ?_ ?_ ?_ ?_
  · -- `i a ha ∈ pairSet S.card`
    intro a ha
    have hne : a.1 ≠ a.2 := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
    simp only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and]
    intro hc
    exact hne (congrArg Subtype.val (e.injective hc))
  · -- `j b hb ∈ (pairSet N).filter …`
    have key : ∀ b ∈ pairSet S.card, ((e.symm b.1).1, (e.symm b.2).1)
        ∈ (pairSet N).filter (fun p => p.1 ∈ S ∧ p.2 ∈ S) := by
      intro b hb
      have hb' : b.1 ≠ b.2 := (Finset.mem_filter.mp hb).2
      refine Finset.mem_filter.mpr ⟨?_, ⟨(e.symm b.1).2, (e.symm b.2).2⟩⟩
      simp only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and]
      intro hc
      exact hb' (by simpa [Equiv.apply_symm_apply] using congrArg e (Subtype.ext hc))
    intro b hb
    exact key b hb
  · -- `j (i a ha) = a`
    intro a ha
    simp only [Equiv.symm_apply_apply]
  · -- `i (j b hb) = b`
    intro b hb
    simp only [Equiv.apply_symm_apply, Subtype.coe_eta]
  · -- `f a = g (i a ha)`
    intro a ha
    have ha1 : a.1 ∈ S := (Finset.mem_filter.mp ha).2.1
    have ha2 : a.2 ∈ S := (Finset.mem_filter.mp ha).2.2
    simp only [slotComb_apply, dif_pos ha1, dif_pos ha2]

/-- **The diagonal `qLHS` density of a slot splitting.**

Under the two support hypotheses on the kernels (`w1` vanishing off the sliding box `B(u)` in its
first argument, `w` vanishing as soon as one argument leaves `B(u)`) and with the outside
configuration `y` entirely outside `B(u)`, the `N`-particle diagonal density of `qLHSword`,
evaluated at the reassembled configuration `slotComb S (fun i => x (e i)) y`, equals the
`S.card`-particle diagonal density at `x`. -/
theorem qLHSden_slotComb {N : ℕ} (L d μ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) (S : Finset (Fin N))
    (e : Work.PerSector.SlotIn N S ≃ Fin S.card)
    (w w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (hsupp1 : ∀ x : EuclideanSpace ℝ (Fin 3), x ∉ Submission.BoseGases.dlBox L d u →
      ∀ y : EuclideanSpace ℝ (Fin 3), w1 x y = 0)
    (hsupp2 : ∀ x y : EuclideanSpace ℝ (Fin 3),
      (x ∉ Submission.BoseGases.dlBox L d u ∨ y ∉ Submission.BoseGases.dlBox L d u) → w x y = 0)
    (x : Submission.BoseGases.X S.card) (y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))
    (hy : ∀ j : Work.PerSector.SlotOut N S, y j ∉ Submission.BoseGases.dlBox L d u) :
    Submission.BoseGases.qLHSden N L μ w w1
        (Work.PerSector.slotComb S (fun i : Work.PerSector.SlotIn N S => x (e i)) y)
      = Submission.BoseGases.qLHSden S.card L μ w w1 x := by
  classical
  set z : SlotIn N S → ℝ³ := fun i => x (e i) with hz
  have h1 : (∑ i : Fin N, w1Fibre L w1 (slotComb S z y i))
      = ∑ j : Fin S.card, w1Fibre L w1 (x j) := by
    rw [sum_slotComb_eq_sum_slotIn S z y (w1Fibre L w1) ?_]
    · exact Equiv.sum_comp e (fun j => w1Fibre L w1 (x j))
    · intro i hi
      rw [slotComb_apply, dif_neg hi, w1Fibre]
      have hv : (fun z => w1 (y ⟨i, hi⟩) z) = fun _ => (0 : ℝ) := by
        funext z
        exact hsupp1 (y ⟨i, hi⟩) (hy ⟨i, hi⟩) z
      rw [hv, integral_zero]
  have h2 : (∑ p ∈ pairSet N, w (slotComb S z y p.1) (slotComb S z y p.2))
      = ∑ q ∈ pairSet S.card, w (x q.1) (x q.2) := by
    rw [← Finset.sum_subset (Finset.filter_subset (fun p : Fin N × Fin N => p.1 ∈ S ∧ p.2 ∈ S) (pairSet N)) ?_]
    · rw [hz]; exact pairSet_slotComb_eq S e x y w
    · intro p hp hpn
      have hpP : ¬ (p.1 ∈ S ∧ p.2 ∈ S) := fun hc => hpn (Finset.mem_filter.mpr ⟨hp, hc⟩)
      rw [not_and_or] at hpP
      rcases hpP with h1 | h2
      · have hc : slotComb S z y p.1 ∉ dlBox L d u := by
          rw [slotComb_apply, dif_neg h1]; exact hy ⟨p.1, h1⟩
        exact hsupp2 _ _ (Or.inl hc)
      · have hc : slotComb S z y p.2 ∉ dlBox L d u := by
          rw [slotComb_apply, dif_neg h2]; exact hy ⟨p.2, h2⟩
        exact hsupp2 _ _ (Or.inr hc)
  unfold Submission.BoseGases.qLHSden
  rw [h1, h2]

end

end Work.SlotWord
