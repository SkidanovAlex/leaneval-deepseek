import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs9.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs9.B

open MeasureTheory Filter
open scoped ContDiff Topology
open Submission.BoseGases

/-- The centred cube `acube ℓ` is compact for **every** `ℓ` (the corpus's
`acube_compact` asks for `0 < ℓ`; for `ℓ < 0` the cube is empty). -/
lemma acube_isCompact (ℓ : ℝ) : IsCompact (acube ℓ) := by
  by_cases hℓ : 0 ≤ ℓ
  · exact (Metric.isCompact_iff_isClosed_bounded).mpr
      ⟨acube_isClosed ℓ, acube_isBounded ℓ hℓ⟩
  · have hlt : ℓ < 0 := lt_of_not_ge hℓ
    have hempty : acube ℓ = ∅ := by
      ext y
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hy
      rw [mem_acube_iff] at hy
      have h1 : (-ℓ / 2 : ℝ) ≤ ℓ / 2 := le_trans (hy 0).1 (hy 0).2
      linarith
    rw [hempty]; exact isCompact_empty

/-- The `N`-particle centred box `abox N ℓ` is compact for **every** `ℓ`. -/
lemma abox_isCompact (N : ℕ) (ℓ : ℝ) : IsCompact (abox N ℓ) := by
  have hac : IsCompact (acube ℓ) := acube_isCompact ℓ
  have h : abox N ℓ = Set.univ.pi (fun _ : Fin N => acube ℓ) := by
    ext x; simp [abox, Set.mem_pi]
  rw [h]
  exact isCompact_univ_pi (fun _ => hac)

/-- A continuous function is integrable over the `N`-box, for **every** `ℓ`. -/
lemma integrableOn_abox_of_continuous' {N : ℕ} {ℓ : ℝ} {F : X N → ℝ}
    (hF : Continuous F) : IntegrableOn F (abox N ℓ) volume :=
  ContinuousOn.integrableOn_compact (abox_isCompact N ℓ) hF.continuousOn

theorem kinWordW_le_sup {N : ℕ} {ℓ : ℝ} {Φ : Submission.BoseGases.X N → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    Work.UBBInputs9.kinWordW N ℓ Φ ≤ Submission.BoseGases.chiSup ^ 2 * Submission.BoseGases.kinWord N ℓ Φ := by
  -- per-(particle, coordinate) comparison, after pulling the constant out of the integral
  have hterm : ∀ (i : Fin N) (k : Fin 3),
      (∫ x in abox N ℓ, (chiScale ℓ (x i)) ^ 2 * (fderiv ℝ Φ x (kcDir N i k)) ^ 2)
        ≤ chiSup ^ 2 * ∫ x in abox N ℓ, (fderiv ℝ Φ x (kcDir N i k)) ^ 2 := by
    intro i k
    have hcont : Continuous
        (fun x : X N => chiSup ^ 2 * (fderiv ℝ Φ x (kcDir N i k)) ^ 2) := by
      have h1 : ContDiff ℝ ∞ (fun x : X N => fderiv ℝ Φ x (kcDir N i k)) :=
        firstDir_contDiff hΦ (kcDir N i k)
      exact (h1.continuous.pow 2).const_mul _
    have hint : Integrable
        (fun x : X N => chiSup ^ 2 * (fderiv ℝ Φ x (kcDir N i k)) ^ 2)
        (volume.restrict (abox N ℓ)) :=
      integrableOn_abox_of_continuous' hcont
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg ?_ hint ?_
    · filter_upwards with x
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · filter_upwards with x
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      rw [sq_le_sq, abs_of_nonneg chiSup_pos.le]
      exact abs_chiScale_le_chiSup ℓ (x i)
  calc Work.UBBInputs9.kinWordW N ℓ Φ
      = ∑ i : Fin N, ∑ k : Fin 3,
          (∫ x in abox N ℓ, (chiScale ℓ (x i)) ^ 2 * (fderiv ℝ Φ x (kcDir N i k)) ^ 2) := rfl
    _ ≤ ∑ i : Fin N, ∑ k : Fin 3,
          chiSup ^ 2 * ∫ x in abox N ℓ, (fderiv ℝ Φ x (kcDir N i k)) ^ 2 := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro k _
        exact hterm i k
    _ = chiSup ^ 2 * ∑ i : Fin N, ∑ k : Fin 3,
          (∫ x in abox N ℓ, (fderiv ℝ Φ x (kcDir N i k)) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]
    _ = chiSup ^ 2 * Submission.BoseGases.kinWord N ℓ Φ := rfl

end Work.UBBInputs9.B
