/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliary estimates for the light angular integration by parts

This module collects the elementary endpoint estimates needed to discharge the
analytic side conditions of `Work.FTS.EllipticEst.TT.slice_ibp_light`
(`Submission/Work/FTS/EllipticEst/TT/sliceIBPLight.lean`) for a function `f` of
class `C²` on the closed angular interval `Iθ = [0, π/2]` vanishing at the two
endpoints.

Contents:

* the trigonometric endpoint bounds `sin(2θ) ≤ 2θ` and Jordan's inequality
  `(4/π)·min θ (π/2-θ) ≤ sin(2θ)` on `Iθ` (with the reflected form);
* the limits `x^r → 0` (`r > 0`) at `0⁺` and `(π/2 - θ)^r → 0` at `(π/2)⁻`,
  for the filters `𝓝[>] 0`, `𝓝[≥] 0`, `𝓝[<] (π/2)`, `𝓝[≤] (π/2)`;
* generic squeeze lemmas producing `Tendsto g … (𝓝 0)` from a bound
  `|g θ| ≤ K θ^r` (resp. `|g θ| ≤ K (π/2 - θ)^r`) with `r > 0`;
* the identification `volume.restrict (Ioo 0 (π/2)) = volume.restrict Iθ` of the
  two measures (they differ by the null set `{0, π/2}`), used to transfer
  a.e. strong measurability from the open interval to the closed one;
* the generic integrability criterion
  `integrableOn_Iθ_of_continuousOn_Ioo_of_abs_le`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.sliceIBPLight

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-! ## Trigonometric endpoint bounds -/

/-- `sin(2θ) ≤ 2θ` for `θ ≥ 0`. -/
lemma sin_two_le_two_mul {θ : ℝ} (hθ : 0 ≤ θ) : Real.sin (2 * θ) ≤ 2 * θ :=
  Real.sin_le (by linarith)

/-- Reflection symmetry: `sin(2θ) = sin(2(π/2 - θ))`. -/
lemma sin_two_eq_sin_two_sub (θ : ℝ) : Real.sin (2 * θ) = Real.sin (2 * (Real.pi / 2 - θ)) := by
  rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]

/-- Jordan's inequality in the form `(4/π)·θ ≤ sin(2θ)` for `θ ∈ [0, π/4]`. -/
lemma four_div_pi_mul_le_sin_two {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 4) :
    (4 / Real.pi) * θ ≤ Real.sin (2 * θ) := by
  have h := Real.mul_le_sin (x := 2 * θ) (by linarith) (by linarith [Real.pi_pos])
  have h2 : 2 / Real.pi * (2 * θ) = (4 / Real.pi) * θ := by ring
  linarith [h, h2]

/-- Jordan's inequality at the right endpoint: `(4/π)(π/2 - θ) ≤ sin(2θ)` for
`θ ∈ [π/4, π/2]`. -/
lemma four_div_pi_mul_sub_le_sin_two {θ : ℝ} (hθ0 : Real.pi / 4 ≤ θ)
    (hθ1 : θ ≤ Real.pi / 2) :
    (4 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.sin (2 * θ) := by
  rw [sin_two_eq_sin_two_sub]
  exact four_div_pi_mul_le_sin_two (by linarith [Real.pi_pos]) (by linarith)

/-- The combined endpoint lower bound `(4/π)·min θ (π/2-θ) ≤ sin(2θ)` on `Iθ`. -/
lemma four_div_pi_mul_min_le_sin_two {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (4 / Real.pi) * min θ (Real.pi / 2 - θ) ≤ Real.sin (2 * θ) := by
  rcases le_total θ (Real.pi / 4) with h | h
  · rw [min_eq_left (by linarith [Real.pi_pos])]
    exact four_div_pi_mul_le_sin_two hθ.1 h
  · rw [min_eq_right (by linarith [Real.pi_pos])]
    exact four_div_pi_mul_sub_le_sin_two h hθ.2

/-! ## The limits `x^r → 0`, `r > 0`, at `0⁺` and of `(π/2 - θ)^r` at `(π/2)⁻` -/

/-- `x^r → 0` as `x → 0` within `[0,∞)`, for `r > 0`. -/
lemma tendsto_rpow_nhdsIci_zero {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x : ℝ => x ^ r) (nhdsWithin (0 : ℝ) (Ici 0)) (nhds 0) := by
  have hcont : ContinuousWithinAt (fun x : ℝ => x ^ r) (Ici (0 : ℝ)) 0 :=
    ContinuousWithinAt.rpow continuousWithinAt_id continuousWithinAt_const (Or.inr hr)
  have h0 : (0 : ℝ) ^ r = 0 := Real.zero_rpow (ne_of_gt hr)
  have h := hcont.tendsto
  rwa [h0] at h

/-- `x^r → 0` as `x → 0⁺`, for `r > 0`. -/
lemma tendsto_rpow_nhdsGT_zero {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x : ℝ => x ^ r) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) :=
  (tendsto_rpow_nhdsIci_zero hr).mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)

/-- `(π/2 - θ)^r → 0` as `θ → π/2` within `(-∞, π/2]`, for `r > 0`. -/
lemma tendsto_sub_pi2_rpow_nhdsIic {r : ℝ} (hr : 0 < r) :
    Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ r)
      (nhdsWithin (Real.pi / 2) (Iic (Real.pi / 2))) (nhds 0) := by
  have hδ : Tendsto (fun θ : ℝ => Real.pi / 2 - θ)
      (nhdsWithin (Real.pi / 2) (Iic (Real.pi / 2))) (nhdsWithin (0 : ℝ) (Ici 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hh : Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (nhds (Real.pi / 2))
          (nhds (Real.pi / 2 - Real.pi / 2)) :=
        (tendsto_const_nhds (x := Real.pi / 2) (f := nhds (Real.pi / 2))).sub
          (tendsto_id (x := nhds (Real.pi / 2)))
      simpa using hh.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      exact sub_nonneg.mpr (mem_Iic.mp hθ)
  exact (tendsto_rpow_nhdsIci_zero hr).comp hδ

/-- `(π/2 - θ)^r → 0` as `θ → (π/2)⁻`, for `r > 0`. -/
lemma tendsto_sub_pi2_rpow_nhdsLT {r : ℝ} (hr : 0 < r) :
    Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ r)
      (nhdsWithin (Real.pi / 2) (Iio (Real.pi / 2))) (nhds 0) :=
  (tendsto_sub_pi2_rpow_nhdsIic hr).mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)

/-! ## Generic squeeze lemmas -/

/-- If `|g θ| ≤ K θ^r` on `(0, π/4)` with `r > 0`, then `g → 0` at `0⁺`. -/
lemma tendsto_zero_of_abs_le_mul_rpow_left {g : ℝ → ℝ} {K r : ℝ} (hr : 0 < r)
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4), |g θ| ≤ K * θ ^ r) :
    Tendsto g (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  refine squeeze_zero' (f := fun θ => ‖g θ‖) (g := fun θ => K * θ ^ r)
    (Eventually.of_forall fun θ => abs_nonneg _) ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / 4 by positivity)] with θ hθ
    simpa [Real.norm_eq_abs] using h θ hθ
  · simpa using (tendsto_rpow_nhdsGT_zero hr).const_mul K

/-- If `|g θ| ≤ K (π/2 - θ)^r` on `(π/4, π/2)` with `r > 0`, then `g → 0` at `(π/2)⁻`. -/
lemma tendsto_zero_of_abs_le_mul_sub_rpow_right {g : ℝ → ℝ} {K r : ℝ} (hr : 0 < r)
    (h : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2), |g θ| ≤ K * (Real.pi / 2 - θ) ^ r) :
    Tendsto g (nhdsWithin (Real.pi / 2) (Iio (Real.pi / 2))) (nhds 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  refine squeeze_zero' (f := fun θ => ‖g θ‖) (g := fun θ => K * (Real.pi / 2 - θ) ^ r)
    (Eventually.of_forall fun θ => abs_nonneg _) ?_ ?_
  · filter_upwards [Ioo_mem_nhdsLT (show Real.pi / 4 < Real.pi / 2 by linarith [Real.pi_pos])]
      with θ hθ
    simpa [Real.norm_eq_abs] using h θ hθ
  · simpa using (tendsto_sub_pi2_rpow_nhdsLT hr).const_mul K

/-! ## The measure identification and the integrability criterion -/

/-- `volume.restrict (Ioo 0 (π/2)) = volume.restrict Iθ`: the two sets differ by the null
set `{0, π/2}`. -/
lemma restrict_Ioo_eq_restrict_Iθ :
    volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) = volume.restrict Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]
  refine MeasureTheory.Measure.restrict_congr_set ?_
  rw [MeasureTheory.ae_eq_set]
  refine ⟨?_, ?_⟩
  · refine measure_mono_null ?_ measure_empty
    intro x hx
    exact absurd ⟨le_of_lt hx.1.1, le_of_lt hx.1.2⟩ hx.2
  · have hsub : Set.Icc (0 : ℝ) (Real.pi / 2) \ Set.Ioo (0 : ℝ) (Real.pi / 2)
        ⊆ ({0, Real.pi / 2} : Set ℝ) := by
      intro x hx
      rw [Set.mem_sdiff] at hx
      rw [Set.mem_Icc] at hx
      rw [Set.mem_Ioo] at hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases lt_or_eq_of_le hx.1.1 with h | h
      · rcases lt_or_eq_of_le hx.1.2 with h2 | h2
        · exact absurd ⟨h, h2⟩ hx.2
        · exact Or.inr h2
      · exact Or.inl h.symm
    refine measure_mono_null hsub ?_
    exact Set.Finite.measure_zero (by simp) volume

/-- Almost every point of `Iθ` lies in the open interval. -/
lemma ae_mem_Ioo_of_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [← restrict_Ioo_eq_restrict_Iθ]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- A function continuous on the open angular interval and bounded there is integrable on
the closed interval. -/
lemma integrableOn_Iθ_of_continuousOn_Ioo_of_abs_le {g : ℝ → ℝ} {K : ℝ}
    (hcont : ContinuousOn g (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |g θ| ≤ K) :
    MeasureTheory.IntegrableOn g Work.Spaces.Iθ := by
  refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ K ?_
  · rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  · rw [← restrict_Ioo_eq_restrict_Iθ]
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [ae_mem_Ioo_of_Iθ] with θ hθ
    rw [Real.norm_eq_abs]
    exact h θ hθ

end Work.FTS.EllipticEst.TT
