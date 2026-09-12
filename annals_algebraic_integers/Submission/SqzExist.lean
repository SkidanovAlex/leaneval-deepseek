import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic

/-! # Child task: mean-value point lemma on a probability space.

Prove `exists_ge_integral` (mirror of `Submission.SqueezeCore`'s lemma).

## What to prove

    exists_ge_integral {α} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
        {f : α → ℝ} (hf : Integrable f ν) {c : ℝ} (hc : c ≤ ∫ x, f x ∂ν) :
        ∃ x : α, c ≤ f x

Proof sketch: by contradiction assume `∀ x, f x < c`. Then `g := c - f` is
pointwise positive, hence `Function.support g = Set.univ` which has positive
measure (probability space), so `∫ g > 0` by
`MeasureTheory.integral_pos_iff_support_of_nonneg`.  But linearity of the
integral gives `∫ g = c - ∫ f ≤ 0` by `hc`, a contradiction.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal Topology

namespace Submission.SqzExist

lemma exists_ge_integral {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
    {f : α → ℝ} (hf : Integrable f ν) {c : ℝ} (hc : c ≤ ∫ x, f x ∂ν) :
    ∃ x : α, c ≤ f x := by
  by_contra h
  have hlt : ∀ x, f x < c := by
    intro x
    exact lt_of_not_ge fun hx : c ≤ f x => h ⟨x, hx⟩
  let g : α → ℝ := fun x => c - f x
  have hgpos : ∀ x, 0 < g x := by
    intro x
    dsimp [g]
    exact sub_pos.mpr (hlt x)
  have hg_nonneg : 0 ≤ g := fun x => le_of_lt (hgpos x)
  have hg_supp : Function.support g = Set.univ := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      exact ne_of_gt (hgpos x)
  have hg_supp_pos : 0 < ν (Function.support g) := by
    rw [hg_supp]
    have hprob : ν Set.univ = 1 := IsProbabilityMeasure.measure_univ
    rw [hprob]
    norm_num
  have hg_int : Integrable g ν := by
    dsimp [g]
    exact (integrable_const c).sub hf
  have hg_pos_int : 0 < ∫ x, g x ∂ν := by
    exact (integral_pos_iff_support_of_nonneg hg_nonneg hg_int).2 hg_supp_pos
  have hg_le : ∫ x, g x ∂ν ≤ 0 := by
    calc
      (∫ x, g x ∂ν) = (∫ x : α, c ∂ν) - (∫ x, f x ∂ν) := by
        dsimp [g]
        exact integral_sub (integrable_const c) hf
      _ = c - (∫ x, f x ∂ν) := by
        rw [integral_const]
        simp
      _ ≤ 0 := by linarith
  linarith

end Submission.SqzExist
