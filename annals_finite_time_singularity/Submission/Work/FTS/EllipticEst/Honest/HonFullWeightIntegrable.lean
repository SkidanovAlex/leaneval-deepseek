/-
Work module: `HonFullWeightIntegrable`.

The **full** singular weight `sin(2θ)^{-(2+η)}` (as opposed to the truncated one
`sin(2θ)^{-η}` of `HonAuxIntegrable`) can be carried by `u²` on the open angular
interval `Iθo = (0, π/2)`, under the honest endpoint bounds `|u θ| ≤ C θ` and
`|u θ| ≤ C (π/2 - θ)` and `η ∈ [0, 1)`.

## Why it is integrable

The point is that the two endpoint bounds together give `|u θ| ≤ C · min(θ, π/2 - θ)`,
and Jordan's inequality `(4/π) min(θ, π/2 - θ) ≤ sin(2θ)` (`SliceBoundary`) gives the
matching lower bound for the weight.  Hence the integrand

  `u(θ)² / sin(2θ)^{2+η} = (u(θ)/sin(2θ))² · sin(2θ)^{-η}`

is dominated by `(C π/4)² · sin(2θ)^{-η}`, and the singular factor is dominated by
`K (θ^{-η} + (π/2 - θ)^{-η})`.  Both `θ ↦ θ^{-η}` and `θ ↦ (π/2 - θ)^{-η}` are integrable
near the respective endpoint because `η < 1`, and the general majorant statement
`Work.Elliptic.integrableOn_of_rpow_majorant` finishes the job.

The counting is done in the equivalent `min`-form: with `m := min θ (π/2 - θ)`,
`u² ≤ C² m²` while `sin(2θ)^{-(2+η)} ≤ (π/4)^{2+η} m^{-(2+η)}`, so
`u² sin(2θ)^{-(2+η)} ≤ C² (π/4)^{2+η} m^{-η} ≤ C² (π/4)^{2+η} (θ^{-η} + (π/2-θ)^{-η})`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Honest.SliceIbpDefs
import Submission.Work.FTS.EllipticEst.Honest.SliceBoundary
import Submission.Work.Elliptic.integrableOn_of_rpow_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary facts on the open interval `Iθo = (0, π/2)` -/

private lemma sin_two_pos_Iθo {θ : ℝ} (hθ : θ ∈ Iθo) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

private lemma sub_pi_div_two_pos {θ : ℝ} (hθ : θ ∈ Iθo) : 0 < Real.pi / 2 - θ := by
  linarith [hθ.2, Real.pi_pos]

/-- Jordan's inequality in the form `(4/π) min θ (π/2 - θ) ≤ sin (2θ)` on `Iθo`. -/
private lemma four_div_pi_mul_min_le_sin_two {θ : ℝ} (hθ : θ ∈ Iθo) :
    (4 / Real.pi) * min θ (Real.pi / 2 - θ) ≤ Real.sin (2 * θ) := by
  rcases le_total θ (Real.pi / 2 - θ) with h | h
  · rw [min_eq_left h]
    exact sin_two_ge_four_div_pi_mul θ hθ.1.le (by linarith [hθ.2, h])
  · rw [min_eq_right h]
    exact sin_two_ge_four_div_pi_mul_sub θ (by linarith [hθ.1, h]) hθ.2

/-- The singular weight is dominated by the `min` of the two endpoint powers. -/
private lemma sin_two_rpow_le_min {p θ : ℝ} (hp : 0 < p) (hθ : θ ∈ Iθo) :
    (Real.sin (2 * θ)) ^ (-p) ≤ (Real.pi / 4) ^ p * (min θ (Real.pi / 2 - θ)) ^ (-p) := by
  have hm0 : 0 < min θ (Real.pi / 2 - θ) := lt_min hθ.1 (sub_pi_div_two_pos hθ)
  have hbase : 0 < 4 / Real.pi * min θ (Real.pi / 2 - θ) := mul_pos (by positivity) hm0
  have key : (Real.sin (2 * θ)) ^ (-p) ≤ (4 / Real.pi * min θ (Real.pi / 2 - θ)) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hbase (four_div_pi_mul_min_le_sin_two hθ) (by linarith)
  have hcoef : (4 / Real.pi : ℝ) ^ (-p) = (Real.pi / 4) ^ p := by
    have hp4 : (0 : ℝ) < 4 / Real.pi := by positivity
    rw [Real.rpow_neg (le_of_lt hp4), ← Real.inv_rpow (le_of_lt hp4), inv_div]
  rwa [Real.mul_rpow (le_of_lt (by positivity : (0 : ℝ) < 4 / Real.pi)) (le_of_lt hm0),
    hcoef] at key

/-! ## The pointwise majorant -/

/-- The full-weight integrand is dominated by the endpoint majorant. -/
private lemma full_weight_bound (u : ℝ → ℝ) (η C : ℝ) (hη0 : 0 ≤ η) (_hC : 0 ≤ C)
    (hb1 : ∀ θ ∈ Iθo, |u θ| ≤ C * θ)
    (hb2 : ∀ θ ∈ Iθo, |u θ| ≤ C * (Real.pi / 2 - θ)) {θ : ℝ} (hθ : θ ∈ Iθo) :
    |(u θ) ^ 2 / (Real.sin (2 * θ)) ^ (2 + η)| ≤
      (C ^ 2 * (Real.pi / 4) ^ (2 + η)) * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) := by
  have hδ0 := sub_pi_div_two_pos hθ
  have hs0 := sin_two_pos_Iθo hθ
  have hm0 : 0 < min θ (Real.pi / 2 - θ) := lt_min hθ.1 hδ0
  -- `u² ≤ C² min(θ, δ)²`
  have hu2 : (u θ) ^ 2 ≤ C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 := by
    have h1 : (u θ) ^ 2 ≤ C ^ 2 * θ ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (u θ)) (hb1 θ hθ) 2
      rw [sq_abs] at h
      calc (u θ) ^ 2 ≤ (C * θ) ^ 2 := h
        _ = C ^ 2 * θ ^ 2 := by ring
    have h2 : (u θ) ^ 2 ≤ C ^ 2 * (Real.pi / 2 - θ) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (u θ)) (hb2 θ hθ) 2
      rw [sq_abs] at h
      calc (u θ) ^ 2 ≤ (C * (Real.pi / 2 - θ)) ^ 2 := h
        _ = C ^ 2 * (Real.pi / 2 - θ) ^ 2 := by ring
    rcases le_total θ (Real.pi / 2 - θ) with h | h
    · rw [min_eq_left h]; exact h1
    · rw [min_eq_right h]; exact h2
  -- the singular weight is dominated by `min^{-(2+η)}`
  have hsinp : (Real.sin (2 * θ)) ^ (-(2 + η))
      ≤ (Real.pi / 4) ^ (2 + η) * (min θ (Real.pi / 2 - θ)) ^ (-(2 + η)) :=
    sin_two_rpow_le_min (p := 2 + η) (by linarith) hθ
  -- `min² · min^{-(2+η)} = min^{-η}`
  have hmpow : (min θ (Real.pi / 2 - θ)) ^ 2 * (min θ (Real.pi / 2 - θ)) ^ (-(2 + η))
      = (min θ (Real.pi / 2 - θ)) ^ (-η) := by
    rw [← Real.rpow_natCast (min θ (Real.pi / 2 - θ)) 2, ← Real.rpow_add hm0]
    congr 1
    ring
  have hmle : (min θ (Real.pi / 2 - θ)) ^ (-η)
      ≤ θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η) := by
    rcases le_total θ (Real.pi / 2 - θ) with h | h
    · rw [min_eq_left h]
      exact le_add_of_nonneg_right (Real.rpow_nonneg hδ0.le _)
    · rw [min_eq_right h]
      exact le_add_of_nonneg_left (Real.rpow_nonneg hθ.1.le _)
  have hsg : 0 ≤ (Real.sin (2 * θ)) ^ (-(2 + η)) := Real.rpow_nonneg hs0.le _
  have hnn : 0 ≤ C ^ 2 * (Real.pi / 4) ^ (2 + η) :=
    mul_nonneg (sq_nonneg C) (Real.rpow_nonneg (by positivity) _)
  have hdiv : (u θ) ^ 2 / (Real.sin (2 * θ)) ^ (2 + η)
      = (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)) := by
    rw [div_eq_mul_inv, Real.rpow_neg hs0.le]
  have habs : |(u θ) ^ 2 / (Real.sin (2 * θ)) ^ (2 + η)|
      = (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)) := by
    rw [hdiv, abs_of_nonneg (mul_nonneg (sq_nonneg _) hsg)]
  calc |(u θ) ^ 2 / (Real.sin (2 * θ)) ^ (2 + η)|
      = (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)) := habs
    _ ≤ (C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2)
          * ((Real.pi / 4) ^ (2 + η) * (min θ (Real.pi / 2 - θ)) ^ (-(2 + η))) :=
        mul_le_mul hu2 hsinp hsg (mul_nonneg (sq_nonneg C) (sq_nonneg _))
    _ = C ^ 2 * (Real.pi / 4) ^ (2 + η)
          * ((min θ (Real.pi / 2 - θ)) ^ 2 * (min θ (Real.pi / 2 - θ)) ^ (-(2 + η))) := by
        ring
    _ = C ^ 2 * (Real.pi / 4) ^ (2 + η) * (min θ (Real.pi / 2 - θ)) ^ (-η) := by rw [hmpow]
    _ ≤ C ^ 2 * (Real.pi / 4) ^ (2 + η) * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
        mul_le_mul_of_nonneg_left hmle hnn

/-! ## Continuity on the open interval -/

private lemma continuousOn_full_weight (u : ℝ → ℝ) (η : ℝ) (hu : ContinuousOn u Iθo) :
    ContinuousOn (fun θ : ℝ => (u θ) ^ 2 / (Real.sin (2 * θ)) ^ (2 + η)) Iθo := by
  have hsin2 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) Iθo :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hden : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 + η)) Iθo :=
    hsin2.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_Iθo hθ)))
  exact (hu.pow 2).div hden fun θ hθ =>
    (Real.rpow_pos_of_pos (sin_two_pos_Iθo hθ) (2 + η)).ne'

/-! ## The theorem -/

theorem HonFullWeightIntegrable (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (u : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hu : ContinuousOn u Work.FTS.EllipticEst.Honest.Iθo)
    (hb1 : ∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |u θ| ≤ C * θ)
    (hb2 : ∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |u θ| ≤ C * (Real.pi / 2 - θ)) :
    MeasureTheory.IntegrableOn
        (fun θ => (u θ) ^ 2 / (Real.sin (2 * θ)) ^ (2 + η)) Work.FTS.EllipticEst.Honest.Iθo
        MeasureTheory.volume := by
  have hK : 0 ≤ C ^ 2 * (Real.pi / 4) ^ (2 + η) :=
    mul_nonneg (sq_nonneg C) (Real.rpow_nonneg (by positivity) _)
  have h := Work.Elliptic.integrableOn_of_rpow_majorant hη0 hη1 hK
    (continuousOn_full_weight u η hu) (fun θ hθ => by
      rw [Real.norm_eq_abs]
      exact full_weight_bound u η C hη0 hC hb1 hb2 hθ)
  simpa [Iθo] using h.mono_set Ioo_subset_Icc_self

end Work.FTS.EllipticEst.Honest
