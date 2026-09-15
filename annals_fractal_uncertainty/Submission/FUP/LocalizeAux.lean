import Submission.FUP.LocalizeGeom
import Submission.Commons.Analysis.Fourier.truncation_high_le
import Submission.Commons.Analysis.Fourier.convolution_sq_le_hsNorm
import Submission.Commons.Analysis.Fourier.tsum_bracket_lattice_le
import Submission.Commons.Analysis.Fourier.exists_compactlySupported_kernel_of_bandlimited
import Submission.Commons.Analysis.Fourier.fourier_modulation_ae
import Submission.Commons.Analysis.Fourier.norm_sum_sq_le_of_bounded_overlap

open MeasureTheory FourierTransform Metric Filter Set
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Auxiliaries for the single-scale localisation estimate (Han–Schlag Lemma 4.3)

This module collects the bookkeeping objects for the proof of `LocalizationStatement` via
Han–Schlag's §4 route (see `Submission/FUP/ROADMAP.md`, Session 54):

* `hsq g` — the **squared `H^{-d}` norm** `∫ ⟨ξ⟩^{-2d}‖𝓕g ξ‖²` of an `L²` class.
* `norm_sq_eq_integral` — `‖g‖² = ∫‖g‖²` for an `L²` class.

The results here are complete and independent of the deep input (`PropLocddim`).
-/

namespace Submission.FUP

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- The squared `H^{-d}` (negative-order Sobolev) norm of an `L²` class:
`∫ ⟨ξ⟩^{-2d} ‖𝓕g ξ‖²`, where `⟨ξ⟩^{-2d} = (1+‖ξ‖²)^{-d}`. -/
noncomputable def hsq (g : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝ :=
  ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) *
    ‖((𝓕 g : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ‖ ^ 2

/-- `‖g‖ ^ 2` as an integral of `‖g‖²` over `volume`. -/
lemma norm_sq_eq_integral (g : Lp ℂ 2 (volume : Measure ℝᵈ)) :
    ‖g‖ ^ 2 = ∫ x, ‖(g : ℝᵈ → ℂ) x‖ ^ 2 :=
  (Commons.Analysis.Fourier.lp_integral_norm_sq g).symm

/-- The `H^{-d}` weight `⟨ξ⟩^{-2d}` is nonnegative. -/
lemma hweight_nonneg (ξ : ℝᵈ) : 0 ≤ (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) :=
  Real.rpow_nonneg (by positivity) _

/-- The `H^{-d}` weight is at most `1`. -/
lemma hweight_le_one (ξ : ℝᵈ) : (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) ≤ 1 := by
  have hx : (1 : ℝ) ≤ 1 + ‖ξ‖ ^ 2 := by have h := sq_nonneg ‖ξ‖; linarith
  calc (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) ≤ (1 + ‖ξ‖ ^ 2) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx (by simp)
    _ = 1 := Real.rpow_zero _

/-- The `H^{-d}` weight is measurable. -/
lemma measurable_hweight : Measurable fun ξ : ℝᵈ => (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) := by
  fun_prop

/-- `hsq` is nonnegative. -/
lemma hsq_nonneg (g : Lp ℂ 2 (volume : Measure ℝᵈ)) : 0 ≤ hsq g :=
  integral_nonneg fun ξ => mul_nonneg (hweight_nonneg ξ) (sq_nonneg _)

/-- **`hsq` is dominated by the squared `L²` norm** (Plancherel, `⟨ξ⟩^{-2d} ≤ 1`). -/
lemma hsq_le_norm_sq (g : Lp ℂ 2 (volume : Measure ℝᵈ)) : hsq g ≤ ‖g‖ ^ 2 := by
  have hInt : Integrable
      (fun ξ => ‖((𝓕 g : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp (𝓕 g)).aestronglyMeasurable).mp (Lp.memLp (𝓕 g))
  have h1 : hsq g ≤ ∫ ξ, ‖((𝓕 g : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ‖ ^ 2 := by
    rw [hsq]
    exact integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun ξ => mul_nonneg (hweight_nonneg ξ) (sq_nonneg _))
      hInt
      (Filter.Eventually.of_forall fun ξ => mul_le_of_le_one_left (sq_nonneg _) (hweight_le_one ξ))
  have h2 : ‖g‖ ^ 2 = ∫ ξ, ‖((𝓕 g : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ‖ ^ 2 := by
    rw [← MeasureTheory.Lp.norm_fourier_eq g, norm_sq_eq_integral (𝓕 g)]
  rw [h2]; exact h1

end Submission.FUP
