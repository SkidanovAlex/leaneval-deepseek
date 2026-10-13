import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Honest.hksq_eq_w2_sliceIntegral
import Submission.Work.FTS.EllipticEst.AngSecond.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.AeProof

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Elementary facts used below

The statement of the target lemma is an estimate of the `z`-`lintegral` of
`φ z · w z²` against the *slice* `θ`-`lintegral` of `G z θ² · sin(2θ)^{-η}` by the level-`0`
quantity `HkSq α 0 G`.  The pointwise input is that `HkIntegrand α 0 G z θ` is exactly
`w z² · (G z θ² · sin(2θ)^{-η})`, the weight `w z²` being a `θ`-independent factor. -/

/-- The angular weight `sEta θ = sin(2θ)^{-η}` is nonnegative on `[0, π/2]`. -/
theorem sEta_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ) _

/-- **The level-`0` integrand, with the radial factor pulled out.**  On `Iθ`,
`HkIntegrand α 0 G z θ = w z² · (G z θ² · sin(2θ)^{-η})`. -/
theorem HkIntegrand_zero_eq_w2_sEta (α : ℝ) (G : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 G z θ
      = (Work.Spaces.w z) ^ 2 * ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
    Work.FTS.EllipticEst.Honest.sq_profile_eq G z θ
      (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ)]
  simp only [Work.FTS.EllipticEst.sEta]
  ring

/-- The radial weight vanishes at `z = 0` (Lean's totalised division). -/
theorem w_zero : Work.Spaces.w 0 = 0 := by
  rw [Work.Spaces.w]; norm_num

theorem FnLintegralLeHkSq {α : ℝ} {G : ℝ → ℝ → ℝ} (hG : Work.Spaces.HkMem α 0 G)
    (φ : ℝ → ℝ) (hφnn : ∀ z : ℝ, 0 ≤ φ z) (hφ1 : ∀ z : ℝ, φ z ≤ 1) :
    (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
      ≤ ENNReal.ofReal (Work.Spaces.HkSq α 0 G) := by
  -- The unweighted `θ`-slice of the `H⁰`-energy of `G`.
  let S : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
  -- `HkMem α 0 G` identifies `HkSq α 0 G` with the `z`-integral of `w z² · S z`.
  have hslice := Work.FTS.EllipticEst.Honest.hksq_eq_w2_sliceIntegral (α := α) (g := G) hG
  have h_int_outer : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * S z) Work.Spaces.Iz := hslice.1
  have h_eq_outer : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * S z)
      = Work.Spaces.HkSq α 0 G := hslice.2
  -- The `θ`-integrand is nonnegative a.e., hence so is every slice `S z`.
  have hnn_θ : ∀ z : ℝ, 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    intro z
    refine (MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc).mpr ?_
    exact Filter.Eventually.of_forall
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_of_mem_Iθ hθ))
  have S_nonneg : ∀ z : ℝ, 0 ≤ S z := fun z =>
    MeasureTheory.integral_nonneg_of_ae (hnn_θ z)
  -- On `z > 0` the unweighted slice is honest: it is a multiple of `HkIntegrand α 0 G z ·`.
  have hInt : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ := by
    intro z hz
    have hHk : MeasureTheory.Integrable (fun θ => Work.Spaces.HkIntegrand α 0 G z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      hG.1 z (Set.mem_Ici.mpr (le_of_lt hz))
    have hconst : MeasureTheory.Integrable
        (fun θ => ((Work.Spaces.w z) ^ 2)⁻¹ * Work.Spaces.HkIntegrand α 0 G z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hHk.const_mul _
    refine MeasureTheory.IntegrableOn.congr_fun hconst ?_ measurableSet_Icc
    intro θ hθ
    change ((Work.Spaces.w z) ^ 2)⁻¹ * Work.Spaces.HkIntegrand α 0 G z θ
      = (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [HkIntegrand_zero_eq_w2_sEta α G hθ]
    have hw2 : (Work.Spaces.w z) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.AngSecond.w_pos hz))
    rw [inv_mul_cancel_left₀ hw2]
  -- Pointwise comparison of the `z`-integrands on the half-line.
  have hpt : ∀ z ∈ Work.Spaces.Iz,
      ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        ≤ ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * S z) := by
    intro z hz
    rcases lt_or_eq_of_le (Set.mem_Ici.mp hz) with hzpos | hz0
    · -- `z > 0`: turn the inner `lintegral` into `ofReal (S z)` and multiply out.
      have hinner : (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
          = ENNReal.ofReal (S z) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hInt z hzpos) (hnn_θ z)).symm
      rw [hinner, ← ENNReal.ofReal_mul (mul_nonneg (hφnn z) (sq_nonneg _))]
      refine ENNReal.ofReal_le_ofReal ?_
      have hSw : 0 ≤ (Work.Spaces.w z) ^ 2 * S z := mul_nonneg (sq_nonneg _) (S_nonneg z)
      have h1 : φ z * ((Work.Spaces.w z) ^ 2 * S z) ≤ (Work.Spaces.w z) ^ 2 * S z := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hφ1 z) hSw
      calc (φ z * (Work.Spaces.w z) ^ 2) * S z
          = φ z * ((Work.Spaces.w z) ^ 2 * S z) := by ring
        _ ≤ (Work.Spaces.w z) ^ 2 * S z := h1
    · -- `z = 0`: the radial weight vanishes, so both sides are `0`.
      subst hz0
      rw [w_zero]
      simp
  -- `HkSq α 0 G` is the `z`-`lintegral` of `ofReal (w z² · S z)`.
  have h_rhs : ENNReal.ofReal (Work.Spaces.HkSq α 0 G)
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * S z) := by
    rw [← h_eq_outer]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_outer
      (Filter.Eventually.of_forall (fun z => mul_nonneg (sq_nonneg _) (S_nonneg z)))
  calc (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
      ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * S z) := by
        refine MeasureTheory.lintegral_mono_ae ?_
        refine (MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici).mpr ?_
        exact Filter.Eventually.of_forall (fun z hz => hpt z hz)
    _ = ENNReal.ofReal (Work.Spaces.HkSq α 0 G) := h_rhs.symm

end Work.FTS.EllipticEst.H2W.AeProof
