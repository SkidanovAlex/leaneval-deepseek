/-
# The `L¹` mass bounds for the bumps `φ_N`, `φ̃_N` (the `integral_iteratedDeriv_bumps_le` interface)

This file converts the `∫⁻`-valued (ENNReal) form of the bump mass bounds -- the theorem
`Work.KMTPlan.A6.loBumpBounds` of `Submission/Work/KMTAreas/A7/LoErrSymD.lean`,
`∫⁻ ξ, ofReal ‖(φ_N)^{(m)}(ξ)‖ ≤ ofReal (C · S^{m-1})` with `S = 2^{Log N}/2^k` -- into the
ordinary (Bochner) integral form

`∫ ξ, ‖(φ_N)^{(m)}(ξ)‖ ≤ C · S^{m-1}`,  `∫ ξ, ‖(φ̃_N)^{(m)}(ξ)‖ ≤ C · (2^{d(Log N-k)})^{m-1}`,

`m ≤ 2`, with the constants independent of `N`, `k` and of the degree `d`.

The bridge is `integral_eq_lintegral_of_nonneg_ae`, which is *unconditional* (no integrability
hypothesis): for a nonnegative a.e. strongly measurable real function `f`,
`∫ f = (∫⁻ ofReal ∘ f).toReal`.  Since `ofReal` is finite, `ENNReal.toReal` is monotone on the
`≠ ⊤` range, and the `∫⁻` bound transfers to the Bochner integral.  Strong measurability comes
from `ContDiff.continuous_iteratedDeriv` (`m ≤ 2`) applied to the C²-bumps.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LoErrSymD

namespace Work.KMTAreas.A7

open MeasureTheory

theorem integral_iteratedDeriv_bumps_le (P : Polynomial ℤ) : ∃ Cφ Cψ : ℝ, 0 < Cφ ∧ 0 < Cψ ∧ (∀ (N k m : ℕ), m ≤ 2 → (∫ ξ : ℝ, ‖iteratedDeriv m (Work.KMTAreas.A7.varphiN N k) ξ‖) ≤ Cφ * (Work.KMTPlan.A6.lothN N / (2 : ℝ) ^ k) ^ ((m : ℝ) - 1)) ∧ (∀ (N k m : ℕ), m ≤ 2 → (∫ ξ : ℝ, ‖iteratedDeriv m (Work.KMTAreas.A7.varphitildeN P.natDegree N k) ξ‖) ≤ Cψ * Work.KMTPlan.A6.lopsN P.natDegree N k ^ ((m : ℝ) - 1)) := by
  obtain ⟨Cφ, Cψ, hCφ, hCψ, hφ, hψ⟩ := Work.KMTPlan.A6.loBumpBounds P
  refine ⟨Cφ, Cψ, hCφ, hCψ, ?_, ?_⟩
  · intro N k m hm
    have hbase := hφ N k m hm
    have hS : 0 < Work.KMTPlan.A6.lothN N / (2 : ℝ) ^ k :=
      div_pos (Work.KMTPlan.A6.lothN_pos N) (by positivity)
    have hr : 0 ≤ Cφ * (Work.KMTPlan.A6.lothN N / (2 : ℝ) ^ k) ^ ((m : ℝ) - 1) :=
      mul_nonneg hCφ.le (Real.rpow_nonneg hS.le _)
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      ((contDiff_varphiN N k).continuous_iteratedDeriv m (by exact_mod_cast hm)).norm.aestronglyMeasurable]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbase).trans_eq (ENNReal.toReal_ofReal hr)
  · intro N k m hm
    have hbase := hψ N k m hm
    have hS : 0 < Work.KMTPlan.A6.lopsN P.natDegree N k :=
      Work.KMTPlan.A6.lopsN_pos P.natDegree N k
    have hr : 0 ≤ Cψ * Work.KMTPlan.A6.lopsN P.natDegree N k ^ ((m : ℝ) - 1) :=
      mul_nonneg hCψ.le (Real.rpow_nonneg hS.le _)
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      ((contDiff_varphitildeN P.natDegree N k).continuous_iteratedDeriv m
        (by exact_mod_cast hm)).norm.aestronglyMeasurable]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbase).trans_eq (ENNReal.toReal_ofReal hr)

end Work.KMTAreas.A7
