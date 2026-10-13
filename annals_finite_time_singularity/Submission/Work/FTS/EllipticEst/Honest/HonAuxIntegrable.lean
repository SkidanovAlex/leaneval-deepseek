/-
Work module: `HonAuxIntegrable`.

Both integrands of the auxiliary `θ`-energy of the honest slice calculus are integrable on
the open angular interval `Iθo = (0, π/2)`, under the honest endpoint bounds
`|u θ| ≤ C θ`, `|u θ| ≤ C (π/2 - θ)` and `η ∈ [0, 1)`.

## Why they are integrable

Write `δ := π/2 - θ`.  On `Iθo` one has `sin (2θ) > 0`, and

* `(2/π) δ ≤ sin δ = cos θ`, so `u²/cos²θ ≤ C² δ² (π/2)² δ⁻² = C² (π/2)²` (using `|u| ≤ C δ`);
* `(4/π) min θ δ ≤ sin (2θ)`, hence `sig η θ = sin(2θ)^{-η} ≤ (π/4)^η min(θ,δ)^{-η}` and
  `sin(2θ)^{-(η+2)} ≤ (π/4)^{η+2} min(θ,δ)^{-(η+2)}`;
* `u² ≤ C² min(θ,δ)²`, so the second integrand is dominated by
  `C² (π/4)^{η+2} min(θ,δ)^{-η} ≤ C² (π/4)^{η+2} (θ^{-η} + δ^{-η})`.

Since `η < 1`, both `θ ↦ θ^{-η}` and `θ ↦ δ^{-η}` are integrable near the corresponding
endpoint, and the general majorant statement
`Work.Elliptic.integrableOn_of_rpow_majorant` finishes the job.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
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

/-- `sig η θ ≤ (π/4)^η (θ^{-η} + (π/2 - θ)^{-η})` on `Iθo` for `η ≥ 0`. -/
private lemma sig_le_majorant {η : ℝ} (hη0 : 0 ≤ η) {θ : ℝ} (hθ : θ ∈ Iθo) :
    sig η θ ≤ (Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) := by
  have hd0 := sub_pi_div_two_pos hθ
  have hminle : (min θ (Real.pi / 2 - θ)) ^ (-η)
      ≤ θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η) := by
    rcases le_total θ (Real.pi / 2 - θ) with h | h
    · rw [min_eq_left h]
      exact le_add_of_nonneg_right (Real.rpow_nonneg hd0.le _)
    · rw [min_eq_right h]
      exact le_add_of_nonneg_left (Real.rpow_nonneg hθ.1.le _)
  rcases eq_or_lt_of_le hη0 with h0 | hpos
  · rw [← h0]
    have hsig0 : sig 0 θ = 1 := by simp only [sig, neg_zero, Real.rpow_zero]
    have hrhs : (Real.pi / 4) ^ (0 : ℝ)
        * (θ ^ (-(0 : ℝ)) + (Real.pi / 2 - θ) ^ (-(0 : ℝ))) = 2 := by
      simp only [neg_zero, Real.rpow_zero]
      norm_num
    rw [hsig0, hrhs]
    norm_num
  · calc sig η θ = (Real.sin (2 * θ)) ^ (-η) := rfl
      _ ≤ (Real.pi / 4) ^ η * (min θ (Real.pi / 2 - θ)) ^ (-η) :=
          sin_two_rpow_le_min hpos hθ
      _ ≤ (Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
          mul_le_mul_of_nonneg_left hminle (Real.rpow_nonneg (by positivity) _)

/-! ## The pointwise bounds for the two integrands -/

/-- Bound for the first integrand: only the right-hand endpoint hypothesis is used, together
with `cos θ = sin (π/2 - θ) ≥ (2/π)(π/2 - θ)`. -/
private lemma F1_bound (u : ℝ → ℝ) (η C : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (_hC : 0 ≤ C)
    (hb2 : ∀ θ ∈ Iθo, |u θ| ≤ C * (Real.pi / 2 - θ)) {θ : ℝ} (hθ : θ ∈ Iθo) :
    |(u θ) ^ 2 * sig η θ * (1 / 2 * (1 - η) / Real.cos θ ^ 2)| ≤
      (1 / 2 * (1 - η) * C ^ 2 * (Real.pi / 2) ^ 2 * (Real.pi / 4) ^ η)
        * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) := by
  have hδ0 := sub_pi_div_two_pos hθ
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have ha : 0 ≤ 1 / 2 * (1 - η) := by linarith
  have hsg : 0 ≤ sig η θ := Real.rpow_nonneg (le_of_lt (sin_two_pos_Iθo hθ)) _
  -- `u² ≤ C² δ²`
  have hu2 : (u θ) ^ 2 ≤ C ^ 2 * (Real.pi / 2 - θ) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (u θ)) (hb2 θ hθ) 2
    rw [sq_abs] at h
    calc (u θ) ^ 2 ≤ (C * (Real.pi / 2 - θ)) ^ 2 := h
      _ = C ^ 2 * (Real.pi / 2 - θ) ^ 2 := by ring
  -- `δ ≤ (π/2) cos θ`
  have hδle : Real.pi / 2 - θ ≤ (Real.pi / 2) * Real.cos θ := by
    have hmul : (2 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.cos θ := by
      have h := Real.mul_le_sin (x := Real.pi / 2 - θ) (le_of_lt hδ0)
        (by linarith [Real.pi_pos, hθ.1])
      rwa [Real.sin_pi_div_two_sub] at h
    have hpi : (Real.pi / 2) * (2 / Real.pi) = 1 := by
      have h2 : (2 : ℝ) / Real.pi = (Real.pi / 2)⁻¹ := (inv_div Real.pi 2).symm
      rw [h2, mul_inv_cancel₀ (by positivity : (Real.pi / 2) ≠ 0)]
    have h1 := mul_le_mul_of_nonneg_left hmul (by positivity : (0 : ℝ) ≤ Real.pi / 2)
    rwa [← mul_assoc, hpi, one_mul] at h1
  have hδsq : (Real.pi / 2 - θ) ^ 2 ≤ (Real.pi / 2) ^ 2 * Real.cos θ ^ 2 := by
    have h := pow_le_pow_left₀ hδ0.le hδle 2
    rwa [mul_pow] at h
  -- `u² / cos²θ ≤ C² (π/2)²`
  have hcq : (u θ) ^ 2 / Real.cos θ ^ 2 ≤ C ^ 2 * (Real.pi / 2) ^ 2 := by
    rw [div_le_iff₀ (pow_pos hcos 2)]
    calc (u θ) ^ 2 ≤ C ^ 2 * (Real.pi / 2 - θ) ^ 2 := hu2
      _ ≤ C ^ 2 * ((Real.pi / 2) ^ 2 * Real.cos θ ^ 2) :=
          mul_le_mul_of_nonneg_left hδsq (sq_nonneg C)
      _ = C ^ 2 * (Real.pi / 2) ^ 2 * Real.cos θ ^ 2 := by ring
  have hstep : (u θ) ^ 2 * (1 / 2 * (1 - η) / Real.cos θ ^ 2)
      ≤ (C ^ 2 * (Real.pi / 2) ^ 2) * (1 / 2 * (1 - η)) := by
    calc (u θ) ^ 2 * (1 / 2 * (1 - η) / Real.cos θ ^ 2)
        = (1 / 2 * (1 - η)) * ((u θ) ^ 2 / Real.cos θ ^ 2) := by ring
      _ ≤ (1 / 2 * (1 - η)) * (C ^ 2 * (Real.pi / 2) ^ 2) :=
          mul_le_mul_of_nonneg_left hcq ha
      _ = (C ^ 2 * (Real.pi / 2) ^ 2) * (1 / 2 * (1 - η)) := by ring
  have hnn : 0 ≤ (C ^ 2 * (Real.pi / 2) ^ 2) * (1 / 2 * (1 - η)) :=
    mul_nonneg (mul_nonneg (sq_nonneg C) (sq_nonneg _)) ha
  have habs : |(u θ) ^ 2 * sig η θ * (1 / 2 * (1 - η) / Real.cos θ ^ 2)|
      = (u θ) ^ 2 * sig η θ * (1 / 2 * (1 - η) / Real.cos θ ^ 2) :=
    abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hsg)
      (div_nonneg ha (pow_pos hcos 2).le))
  calc |(u θ) ^ 2 * sig η θ * (1 / 2 * (1 - η) / Real.cos θ ^ 2)|
      = (u θ) ^ 2 * (1 / 2 * (1 - η) / Real.cos θ ^ 2) * sig η θ := by
        rw [habs]; ring
    _ ≤ ((C ^ 2 * (Real.pi / 2) ^ 2) * (1 / 2 * (1 - η))) * sig η θ :=
        mul_le_mul_of_nonneg_right hstep hsg
    _ ≤ ((C ^ 2 * (Real.pi / 2) ^ 2) * (1 / 2 * (1 - η)))
          * ((Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η))) :=
        mul_le_mul_of_nonneg_left (sig_le_majorant hη0 hθ) hnn
    _ = (1 / 2 * (1 - η) * C ^ 2 * (Real.pi / 2) ^ 2 * (Real.pi / 4) ^ η)
          * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) := by ring

/-- Bound for the second integrand, using the `min` form of both endpoint bounds. -/
private lemma F2_bound (u : ℝ → ℝ) (η C : ℝ) (hη0 : 0 ≤ η) (_hC : 0 ≤ C)
    (hb1 : ∀ θ ∈ Iθo, |u θ| ≤ C * θ)
    (hb2 : ∀ θ ∈ Iθo, |u θ| ≤ C * (Real.pi / 2 - θ)) {θ : ℝ} (hθ : θ ∈ Iθo) :
    |(u θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig η θ / (Real.sin (2 * θ)) ^ 2| ≤
      (C ^ 2 * (Real.pi / 4) ^ (η + 2)) * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) := by
  have hδ0 := sub_pi_div_two_pos hθ
  have hs0 : 0 < Real.sin (2 * θ) := sin_two_pos_Iθo hθ
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
  have hcos2 : (Real.cos (2 * θ)) ^ 2 ≤ 1 := by
    nlinarith [Real.cos_le_one (2 * θ), Real.neg_one_le_cos (2 * θ)]
  have hsinp : (Real.sin (2 * θ)) ^ (-(η + 2))
      ≤ (Real.pi / 4) ^ (η + 2) * (min θ (Real.pi / 2 - θ)) ^ (-(η + 2)) :=
    sin_two_rpow_le_min (by linarith) hθ
  have hdiv : sig η θ / (Real.sin (2 * θ)) ^ 2 = (Real.sin (2 * θ)) ^ (-(η + 2)) := by
    rw [div_eq_iff (by positivity : (Real.sin (2 * θ)) ^ 2 ≠ 0), sig]
    rw [← Real.rpow_natCast (Real.sin (2 * θ)) 2, ← Real.rpow_add hs0]
    congr 1
    ring
  have hmpow : (min θ (Real.pi / 2 - θ)) ^ 2 * (min θ (Real.pi / 2 - θ)) ^ (-(η + 2))
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
  have hstep : (u θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(η + 2))
      ≤ (C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2) * 1
        * ((Real.pi / 4) ^ (η + 2) * (min θ (Real.pi / 2 - θ)) ^ (-(η + 2))) := by
    have h1 : 0 ≤ (Real.sin (2 * θ)) ^ (-(η + 2)) := Real.rpow_nonneg hs0.le _
    have h2 : 0 ≤ (C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2) * 1 :=
      mul_nonneg (mul_nonneg (sq_nonneg C) (sq_nonneg _)) zero_le_one
    exact mul_le_mul
      (mul_le_mul hu2 hcos2 (sq_nonneg _) (mul_nonneg (sq_nonneg C) (sq_nonneg _)))
      hsinp h1 h2
  have hsg : 0 ≤ sig η θ := Real.rpow_nonneg hs0.le _
  have hnn : 0 ≤ C ^ 2 * (Real.pi / 4) ^ (η + 2) :=
    mul_nonneg (sq_nonneg C) (Real.rpow_nonneg (by positivity) _)
  have habs : |(u θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig η θ / (Real.sin (2 * θ)) ^ 2|
      = (u θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig η θ / (Real.sin (2 * θ)) ^ 2 :=
    abs_of_nonneg (div_nonneg
      (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hsg) (pow_pos hs0 2).le)
  calc |(u θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig η θ / (Real.sin (2 * θ)) ^ 2|
      = (u θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig η θ / (Real.sin (2 * θ)) ^ 2 := habs
    _ = (u θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * (sig η θ / (Real.sin (2 * θ)) ^ 2) := by
        ring
    _ = (u θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(η + 2)) := by
        rw [hdiv]
    _ ≤ (C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2) * 1
          * ((Real.pi / 4) ^ (η + 2) * (min θ (Real.pi / 2 - θ)) ^ (-(η + 2))) := hstep
    _ = C ^ 2 * (Real.pi / 4) ^ (η + 2)
          * ((min θ (Real.pi / 2 - θ)) ^ 2 * (min θ (Real.pi / 2 - θ)) ^ (-(η + 2))) := by
        ring
    _ = C ^ 2 * (Real.pi / 4) ^ (η + 2) * (min θ (Real.pi / 2 - θ)) ^ (-η) := by rw [hmpow]
    _ ≤ C ^ 2 * (Real.pi / 4) ^ (η + 2) * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
        mul_le_mul_of_nonneg_left hmle hnn

/-! ## Continuity of the two integrands -/

private lemma continuousOn_F1 (u : ℝ → ℝ) (η : ℝ) (hu : ContinuousOn u Iθo) :
    ContinuousOn (fun θ : ℝ => (u θ) ^ 2 * sig η θ * (1 / 2 * (1 - η) / Real.cos θ ^ 2))
      Iθo := by
  have hsin2 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) Iθo :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hsig : ContinuousOn (sig η) Iθo :=
    show ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-η)) Iθo from
      hsin2.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_Iθo hθ)))
  have hden : ContinuousOn (fun θ : ℝ => (1 / 2 * (1 - η)) / Real.cos θ ^ 2) Iθo :=
    continuous_const.continuousOn.div (Real.continuous_cos.continuousOn.pow 2)
      (fun θ hθ => by
        have hc : 0 < Real.cos θ :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
        exact (pow_pos hc 2).ne')
  exact ((hu.pow 2).mul hsig).mul hden

private lemma continuousOn_F2 (u : ℝ → ℝ) (η : ℝ) (hu : ContinuousOn u Iθo) :
    ContinuousOn (fun θ : ℝ => (u θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig η θ
      / (Real.sin (2 * θ)) ^ 2) Iθo := by
  have hsin2 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) Iθo :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hcos2 : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) Iθo :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hsig : ContinuousOn (sig η) Iθo :=
    show ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-η)) Iθo from
      hsin2.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_Iθo hθ)))
  have hnum : ContinuousOn
      (fun θ : ℝ => (u θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig η θ) Iθo :=
    ((hu.pow 2).mul (hcos2.pow 2)).mul hsig
  exact hnum.div (hsin2.pow 2) (fun θ hθ => (pow_pos (sin_two_pos_Iθo hθ) 2).ne')

/-! ## The theorem -/

theorem HonAuxIntegrable (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (u : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hu : ContinuousOn u Work.FTS.EllipticEst.Honest.Iθo)
    (hb1 : ∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |u θ| ≤ C * θ)
    (hb2 : ∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |u θ| ≤ C * (Real.pi / 2 - θ)) :
    MeasureTheory.IntegrableOn
        (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.Honest.sig η θ
          * (1 / 2 * (1 - η) / Real.cos θ ^ 2)) Work.FTS.EllipticEst.Honest.Iθo
        MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn
        (fun θ => (u θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * Work.FTS.EllipticEst.Honest.sig η θ
          / (Real.sin (2 * θ)) ^ 2) Work.FTS.EllipticEst.Honest.Iθo
        MeasureTheory.volume := by
  have hK1 : 0 ≤ 1 / 2 * (1 - η) * C ^ 2 * (Real.pi / 2) ^ 2 * (Real.pi / 4) ^ η := by
    have ha : 0 ≤ 1 / 2 * (1 - η) := by linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg ha (sq_nonneg C)) (sq_nonneg _))
      (Real.rpow_nonneg (by positivity) _)
  have hK2 : 0 ≤ C ^ 2 * (Real.pi / 4) ^ (η + 2) :=
    mul_nonneg (sq_nonneg C) (Real.rpow_nonneg (by positivity) _)
  constructor
  · have h := Work.Elliptic.integrableOn_of_rpow_majorant hη0 hη1 hK1
      (continuousOn_F1 u η hu) (fun θ hθ => by
        rw [Real.norm_eq_abs]
        exact F1_bound u η C hη0 hη1 hC hb2 hθ)
    simpa [Iθo] using h.mono_set Ioo_subset_Icc_self
  · have h := Work.Elliptic.integrableOn_of_rpow_majorant hη0 hη1 hK2
      (continuousOn_F2 u η hu) (fun θ hθ => by
        rw [Real.norm_eq_abs]
        exact F2_bound u η C hη0 hC hb1 hb2 hθ)
    simpa [Iθo] using h.mono_set Ioo_subset_Icc_self

end Work.FTS.EllipticEst.Honest
