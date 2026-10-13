/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability and endpoint bounds for the reciprocal angular weight `(thEta θ)⁻¹`

The angular weight of the first sum of the `H^k`-norm is `thEta θ = sin(2θ)^{-η}` with
`η = 99/100` (`Work.Spaces.eta`).  Its reciprocal is the *positive* power
`(thEta θ)⁻¹ = sin(2θ)^η` on the open strip `(0, π/2)`, which vanishes like
`θ^η` at `θ = 0` and like `(π/2 - θ)^η` at `θ = π/2`; consequently it is
integrable on every open subinterval of `(0, π/2)` and its integral over
`(0, θ)` (resp. `(θ, π/2)`) is controlled by `2 θ^{1+η}` (resp.
`2 (π/2 - θ)^{1+η}`).

The proof is elementary: `sin x ≤ x` for `x ≥ 0` together with
`sin(2θ) = sin(2(π/2 - θ))` gives the pointwise bounds
`sin(2θ)^η ≤ (2θ)^η ≤ 2^η θ^η` on `(0, θ)` and
`sin(2θ)^η ≤ (2(π/2 - θ))^η ≤ 2^η (π/2 - θ)^η` on `(θ, π/2)`; integrating the
constant majorant over an interval of length `L` costs a factor `2^η L`, and
`2^η ≤ 2`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core

open scoped Real
open MeasureTheory Set

/-- On the open strip `(0, π/2)` the reciprocal of the angular weight `thEta` is the
*positive* power `sin(2θ)^η` of `sin(2θ)`. -/
lemma thEta_inv_eq_sin_two_rpow {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.FTS.EllipticEst.thEta t)⁻¹ = (Real.sin (2 * t)) ^ (Work.Spaces.eta) := by
  have hs : 0 ≤ Real.sin (2 * t) :=
    Work.FTS.EllipticEst.sin_two_nonneg (Set.Ioo_subset_Icc_self ht)
  rw [Work.FTS.EllipticEst.thEta, Real.rpow_neg hs, inv_inv]

/-- `θ ↦ sin(2θ)^η` is continuous on every closed interval. -/
lemma continuousOn_sin_two_rpow_eta (a b : ℝ) :
    ContinuousOn (fun t : ℝ => (Real.sin (2 * t)) ^ (Work.Spaces.eta)) (Set.Icc a b) :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
    (fun _ _ => Or.inr Work.Spaces.eta_nonneg)

/-- `θ ↦ sin(2θ)^η` is integrable on every open interval with finite endpoints. -/
lemma integrableOn_sin_two_rpow_eta_Ioo (a b : ℝ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (Real.sin (2 * t)) ^ (Work.Spaces.eta)) (Set.Ioo a b) :=
  ((continuousOn_sin_two_rpow_eta a b).integrableOn_compact isCompact_Icc).mono_set
    Set.Ioo_subset_Icc_self

/-- The pointwise bound at the left endpoint: for `0 < t < θ < π/2`,
`sin(2t)^η ≤ 2^η θ^η`. -/
lemma sin_two_rpow_le_of_lt {θ t : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (ht : t ∈ Set.Ioo (0 : ℝ) θ) :
    (Real.sin (2 * t)) ^ (Work.Spaces.eta) ≤
      (2 : ℝ) ^ (Work.Spaces.eta) * θ ^ (Work.Spaces.eta) := by
  obtain ⟨hθ0, hθ2⟩ := hθ
  obtain ⟨ht0, htθ⟩ := ht
  have hpi := Real.pi_pos
  have hsin0 : 0 ≤ Real.sin (2 * t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hle : Real.sin (2 * t) ≤ 2 * θ := by
    have h1 : Real.sin (2 * t) ≤ 2 * t := Real.sin_le (by linarith)
    linarith
  have hstep := Real.rpow_le_rpow hsin0 hle Work.Spaces.eta_nonneg
  rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hθ0)] at hstep

/-- The pointwise bound at the right endpoint: for `0 < θ < t < π/2`,
`sin(2t)^η ≤ 2^η (π/2 - θ)^η`. -/
lemma sin_two_rpow_le_of_gt {θ t : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (ht : t ∈ Set.Ioo θ (Real.pi / 2)) :
    (Real.sin (2 * t)) ^ (Work.Spaces.eta) ≤
      (2 : ℝ) ^ (Work.Spaces.eta) * (Real.pi / 2 - θ) ^ (Work.Spaces.eta) := by
  obtain ⟨hθ0, hθ2⟩ := hθ
  obtain ⟨htθ, ht2⟩ := ht
  have hpi := Real.pi_pos
  have hsin0 : 0 ≤ Real.sin (2 * t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hsub0 : 0 ≤ Real.pi / 2 - θ := by linarith
  have hle : Real.sin (2 * t) ≤ 2 * (Real.pi / 2 - θ) := by
    have h1 : Real.sin (2 * (Real.pi / 2 - t)) ≤ 2 * (Real.pi / 2 - t) :=
      Real.sin_le (by linarith)
    have h2 : Real.sin (2 * t) = Real.sin (2 * (Real.pi / 2 - t)) := by
      rw [show 2 * (Real.pi / 2 - t) = Real.pi - 2 * t by ring, Real.sin_pi_sub]
    rw [h2]
    linarith
  have hstep := Real.rpow_le_rpow hsin0 hle Work.Spaces.eta_nonneg
  rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hsub0] at hstep

/-- The elementary arithmetic at the heart of both endpoint estimates:
`2^η L^η · L ≤ 2 L^{1+η}` for `L > 0`. -/
lemma two_pow_eta_mul_rpow_mul_le {L : ℝ} (hL : 0 < L) :
    (2 : ℝ) ^ (Work.Spaces.eta) * L ^ (Work.Spaces.eta) * L ≤
      2 * L ^ (1 + Work.Spaces.eta) := by
  have h2 : (2 : ℝ) ^ (Work.Spaces.eta) ≤ 2 := by
    calc (2 : ℝ) ^ (Work.Spaces.eta) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_lt Work.Spaces.eta_lt_one)
      _ = 2 := Real.rpow_one 2
  have hpow : L ^ (1 + Work.Spaces.eta) = L ^ Work.Spaces.eta * L := by
    rw [Real.rpow_add hL, Real.rpow_one, mul_comm]
  calc (2 : ℝ) ^ (Work.Spaces.eta) * L ^ (Work.Spaces.eta) * L
      = (2 : ℝ) ^ (Work.Spaces.eta) * (L ^ Work.Spaces.eta * L) := by ring
    _ = (2 : ℝ) ^ (Work.Spaces.eta) * L ^ (1 + Work.Spaces.eta) := by rw [hpow]
    _ ≤ 2 * L ^ (1 + Work.Spaces.eta) :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (le_of_lt hL) _)

/-- Integrating a nonnegative function on `(a, b)` which is everywhere bounded by the
constant `2^η (b - a)^η` gives at most `2 (b - a)^{1+η}`. -/
lemma integral_le_two_mul_rpow {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (h0 : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioo a b)] f)
    (hle : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioo a b)),
      f t ≤ (2 : ℝ) ^ (Work.Spaces.eta) * (b - a) ^ (Work.Spaces.eta)) :
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo a b)) f
      ≤ 2 * (b - a) ^ (1 + Work.Spaces.eta) := by
  have hvol : MeasureTheory.volume (Set.Ioo a b) ≠ ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hgi : MeasureTheory.Integrable
      (fun _ : ℝ => (2 : ℝ) ^ (Work.Spaces.eta) * (b - a) ^ (Work.Spaces.eta))
      (MeasureTheory.volume.restrict (Set.Ioo a b)) := by
    rw [MeasureTheory.integrable_const_iff]
    exact Or.inr (MeasureTheory.isFiniteMeasure_restrict.mpr hvol)
  have hmono : MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo a b)) f
      ≤ MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo a b))
          (fun _ : ℝ => (2 : ℝ) ^ (Work.Spaces.eta) * (b - a) ^ (Work.Spaces.eta)) :=
    MeasureTheory.integral_mono_of_nonneg h0 hgi hle
  have hconst : MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo a b))
      (fun _ : ℝ => (2 : ℝ) ^ (Work.Spaces.eta) * (b - a) ^ (Work.Spaces.eta))
      = (2 : ℝ) ^ (Work.Spaces.eta) * (b - a) ^ (Work.Spaces.eta) * (b - a) := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, Real.volume_Ioo,
        ENNReal.toReal_ofReal (sub_nonneg.mpr (le_of_lt hab)), smul_eq_mul]
    ring
  exact hmono.trans
    (le_trans (le_of_eq hconst) (two_pow_eta_mul_rpow_mul_le (sub_pos.mpr hab)))

theorem thEtaInvIntegralBounds :
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      MeasureTheory.IntegrableOn (fun t => (Work.FTS.EllipticEst.thEta t)⁻¹) (Set.Ioo 0 θ)) ∧
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo 0 θ))
        (fun t => (Work.FTS.EllipticEst.thEta t)⁻¹) ≤ 2 * θ ^ (1 + Work.Spaces.eta)) ∧
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      MeasureTheory.IntegrableOn (fun t => (Work.FTS.EllipticEst.thEta t)⁻¹) (Set.Ioo θ (Real.pi / 2))) ∧
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo θ (Real.pi / 2)))
        (fun t => (Work.FTS.EllipticEst.thEta t)⁻¹) ≤ 2 * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Integrability on `(0, θ)`
    intro θ hθ
    exact (integrableOn_sin_two_rpow_eta_Ioo 0 θ).congr_fun
      (fun t ht => (thEta_inv_eq_sin_two_rpow ⟨ht.1, lt_trans ht.2 hθ.2⟩).symm)
      measurableSet_Ioo
  · -- The bound on `(0, θ)`
    intro θ hθ
    have hmain := integral_le_two_mul_rpow (a := 0) (b := θ) hθ.1
      (f := fun t => (Work.FTS.EllipticEst.thEta t)⁻¹) ?_ ?_
    · simpa using hmain
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      rw [thEta_inv_eq_sin_two_rpow ⟨ht.1, lt_trans ht.2 hθ.2⟩]
      exact Real.rpow_nonneg
        (Work.FTS.EllipticEst.sin_two_nonneg
          ⟨le_of_lt ht.1, le_of_lt (lt_trans ht.2 hθ.2)⟩) _
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      rw [thEta_inv_eq_sin_two_rpow ⟨ht.1, lt_trans ht.2 hθ.2⟩]
      simpa using sin_two_rpow_le_of_lt (θ := θ) (t := t) hθ ht
  · -- Integrability on `(θ, π/2)`
    intro θ hθ
    exact (integrableOn_sin_two_rpow_eta_Ioo θ (Real.pi / 2)).congr_fun
      (fun t ht => (thEta_inv_eq_sin_two_rpow ⟨lt_trans hθ.1 ht.1, ht.2⟩).symm)
      measurableSet_Ioo
  · -- The bound on `(θ, π/2)`
    intro θ hθ
    have hmain := integral_le_two_mul_rpow (a := θ) (b := Real.pi / 2) hθ.2
      (f := fun t => (Work.FTS.EllipticEst.thEta t)⁻¹) ?_ ?_
    · simpa using hmain
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      rw [thEta_inv_eq_sin_two_rpow ⟨lt_trans hθ.1 ht.1, ht.2⟩]
      exact Real.rpow_nonneg
        (Work.FTS.EllipticEst.sin_two_nonneg
          ⟨le_of_lt (lt_trans hθ.1 ht.1), le_of_lt ht.2⟩) _
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      rw [thEta_inv_eq_sin_two_rpow ⟨lt_trans hθ.1 ht.1, ht.2⟩]
      simpa using sin_two_rpow_le_of_gt (θ := θ) (t := t) hθ ht

end Work.EllipticEst.Core
