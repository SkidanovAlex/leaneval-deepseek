import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2Ident
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.cos_inv_cube_mul_integral_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `end_rate_pi_half` — the endpoint rate of a slice of the self-similar profile

Let `S` solve the slice equation

`S'' = tan θ · S' + (cos θ)⁻² · S − 6 S − G`

on `(0, π/2)`, with `|G t| ≤ MG · (π/2 − t)^β` and `|S t| ≤ CS · (π/2 − t)` for `β ∈ (0, 1]`,
and suppose moreover that `Φ := S'' + 4 S + G` is **bounded** on `(0, π/2)` (this is the
hypothesis `hWb`; it pins down the regular branch of the linear equation for `Φ`).  Then

`|S''(θ)| ≤ 100 (MG + CS) · (π/2 − θ)^β`  on `(π/4, π/2)`.

The proof combines two earlier lemmas:

* `BoxAux.th2Ident`: `(cos θ)³ Φ(θ) = ∫_θ^{π/2} sin t · (cos t)² · G t dt` — the closed
  form of `Φ` obtained from the ODE and the FTC (the boundedness of `Φ` kills the boundary
  term at `π/2`);
* `BoxAux.cos_inv_cube_mul_integral_le`: `(cos θ)⁻³ ∫_θ^{π/2} sin t (cos t)² (π/2−t)^β dt
  ≤ 32 (π/2−θ)^β`.

Combining: `|Φ(θ)| ≤ (cos θ)⁻³ · MG · ∫_θ^{π/2} sin t (cos t)² (π/2−t)^β dt ≤ 32 MG δ^β`
with `δ = π/2 − θ`, and then `S'' = Φ − 4S − G` gives the claim.
-/

open MeasureTheory
open scoped Topology

namespace Work.FTS_EllLimOK.ProducerH.H2.Dev

theorem end_rate_pi_half {S G : ℝ → ℝ} {β MG CS MW : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hMG : 0 ≤ MG) (hCS : 0 ≤ CS)
    (hS : ContDiffOn ℝ 2 S (Set.Ioo (0:ℝ) (Real.pi / 2)))
    (hGc : ContinuousOn G (Set.Ioo (0:ℝ) (Real.pi / 2)))
    (hGle : ∀ t ∈ Set.Ioo (0:ℝ) (Real.pi / 2), |G t| ≤ MG)
    (hode : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      deriv (deriv S) θ = Real.tan θ * deriv S θ + ((Real.cos θ)^2)⁻¹ * S θ - 6 * S θ - G θ)
    (hWb : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      |deriv (deriv S) θ + 4 * S θ + G θ| ≤ MW)
    (hRate : ∀ t ∈ Set.Ioo (0:ℝ) (Real.pi / 2), |G t| ≤ MG * (Real.pi / 2 - t) ^ β)
    (hSr : ∀ t ∈ Set.Ioo (0:ℝ) (Real.pi / 2), |S t| ≤ CS * (Real.pi / 2 - t)) :
    ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      |deriv (deriv S) θ| ≤ (100 * (MG + CS)) * (Real.pi / 2 - θ) ^ β := by
  intro θ hθ
  have hθ45 : Real.pi / 4 < θ := hθ.1
  have hθlt : θ < Real.pi / 2 := hθ.2
  have hθpos : 0 < θ := by linarith [Real.pi_pos]
  have hθIoo : θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := ⟨hθpos, hθlt⟩
  have hcospos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  set δ : ℝ := Real.pi / 2 - θ with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδle1 : δ ≤ 1 := by rw [hδdef]; linarith [Real.pi_lt_four]
  have hδβge : δ ≤ δ ^ β := by
    have h := Real.rpow_le_rpow_of_exponent_ge hδpos hδle1 hβ1
    rwa [Real.rpow_one] at h
  have hδβnn : 0 ≤ δ ^ β := Real.rpow_nonneg hδpos.le β
  -- the closed form of `Φ = S'' + 4S + G`
  have hident := Work.FTS_EllLimOK.ProducerH.BoxAux.th2Ident hS hGc hGle hode hWb θ hθIoo
  set X : ℝ := deriv (deriv S) θ + 4 * S θ + G θ with hXdef
  set I : ℝ := ∫ t in θ..(Real.pi/2), Real.sin t * (Real.cos t)^2 * G t with hIdef
  set J : ℝ := ∫ t in θ..(Real.pi/2), Real.sin t * (Real.cos t)^2 * (Real.pi/2 - t)^β with hJdef
  have hident' : (Real.cos θ)^3 * X = I := by rw [hXdef, hIdef]; exact hident
  -- bound the integral against the rate of `G`
  have hI_le : |I| ≤ MG * J := by
    rw [hIdef, hJdef]
    have hcd : Continuous (fun t : ℝ => Real.sin t * (Real.cos t)^2) :=
      Real.continuous_sin.mul (Real.continuous_cos.pow 2)
    have hcont_pow : ContinuousOn (fun t : ℝ => (Real.pi/2 - t)^β) (Set.uIcc θ (Real.pi/2)) :=
      (continuous_const.sub continuous_id).continuousOn.rpow_const (fun _ _ => Or.inr hβ.le)
    have hJint : IntervalIntegrable (fun t : ℝ => Real.sin t * (Real.cos t)^2 * (Real.pi/2 - t)^β)
        volume θ (Real.pi/2) := ((hcd.continuousOn).mul hcont_pow).intervalIntegrable
    have hgint : IntervalIntegrable
        (fun t : ℝ => MG * (Real.sin t * (Real.cos t)^2 * (Real.pi/2 - t)^β)) volume θ (Real.pi/2) :=
      hJint.const_mul MG
    have hle : θ ≤ Real.pi/2 := hθlt.le
    have hpt : ∀ᵐ t ∂volume, t ∈ Set.Ioc θ (Real.pi/2) →
        ‖Real.sin t * (Real.cos t)^2 * G t‖
          ≤ MG * (Real.sin t * (Real.cos t)^2 * (Real.pi/2 - t)^β) := by
      filter_upwards with t ht
      rcases eq_or_lt_of_le ht.2 with h | h
      · rw [h]
        simp [Real.cos_pi_div_two, Real.zero_rpow hβ.ne']
      · have htIoo : t ∈ Set.Ioo (0:ℝ) (Real.pi/2) := ⟨by linarith [hθpos, ht.1], h⟩
        have hGt := hRate t htIoo
        have hsinnn : 0 ≤ Real.sin t :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθpos, ht.1]) (by linarith [Real.pi_pos])
        have hcos2nn : 0 ≤ (Real.cos t)^2 := sq_nonneg _
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hsinnn, abs_of_nonneg hcos2nn]
        calc Real.sin t * (Real.cos t)^2 * |G t|
            ≤ Real.sin t * (Real.cos t)^2 * (MG * (Real.pi/2 - t)^β) :=
              mul_le_mul_of_nonneg_left hGt (mul_nonneg hsinnn hcos2nn)
          _ = MG * (Real.sin t * (Real.cos t)^2 * (Real.pi/2 - t)^β) := by ring
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hle hpt hgint
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul] at hnorm
    exact hnorm
  have hcoef_nn : 0 ≤ ((Real.cos θ)^3)⁻¹ := inv_nonneg.mpr (pow_pos hcospos 3).le
  -- the normalized integral is `≤ 32 δ^β`
  have hJb : ((Real.cos θ)^3)⁻¹ * J ≤ 32 * δ^β := by
    have h := Work.FTS_EllLimOK.ProducerH.BoxAux.cos_inv_cube_mul_integral_le hβ hβ1
      (show θ ∈ Set.Icc (Real.pi/4) (Real.pi/2) from ⟨hθ45.le, hθlt.le⟩)
    rw [hJdef, hδdef, ← inv_pow]
    exact h
  -- hence `|Φ| ≤ 32 MG δ^β`
  have hX_le : |X| ≤ 32 * MG * δ^β := by
    have hXeq : X = ((Real.cos θ)^3)⁻¹ * I := by
      rw [← hident']
      exact (inv_mul_cancel_left₀ (by positivity : (Real.cos θ)^3 ≠ 0) X).symm
    have h2 : |X| = ((Real.cos θ)^3)⁻¹ * |I| := by
      rw [hXeq, abs_mul, abs_of_nonneg hcoef_nn]
    rw [h2]
    calc ((Real.cos θ)^3)⁻¹ * |I|
        ≤ ((Real.cos θ)^3)⁻¹ * (MG * J) := mul_le_mul_of_nonneg_left hI_le hcoef_nn
      _ = MG * (((Real.cos θ)^3)⁻¹ * J) := by ring
      _ ≤ MG * (32 * δ^β) := mul_le_mul_of_nonneg_left hJb hMG
      _ = 32 * MG * δ^β := by ring
  have hSθ : |S θ| ≤ CS * δ := by rw [hδdef]; exact hSr θ hθIoo
  have hGθ : |G θ| ≤ MG * δ^β := by rw [hδdef]; exact hRate θ hθIoo
  -- `S'' = Φ − 4S − G`
  have hS'' : |deriv (deriv S) θ| = |X - 4 * S θ - G θ| := by
    congr 1
    rw [hXdef]; ring
  rw [hS'']
  have h_abs : |X - 4 * S θ - G θ| ≤ |X| + 4 * |S θ| + |G θ| := by
    have h1 : |X - 4 * S θ - G θ| ≤ |X - 4 * S θ| + |G θ| := by
      have hh := abs_add_le (X - 4 * S θ) (-(G θ))
      simpa [sub_eq_add_neg] using hh
    have h2 : |X - 4 * S θ| ≤ |X| + 4 * |S θ| := by
      have hh := abs_add_le X (-(4 * S θ))
      rw [abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)] at hh
      simpa [sub_eq_add_neg] using hh
    linarith
  calc |X - 4 * S θ - G θ| ≤ |X| + 4 * |S θ| + |G θ| := h_abs
    _ ≤ 32 * MG * δ^β + 4 * CS * δ + MG * δ^β := by linarith
    _ ≤ 100 * (MG + CS) * δ^β := by nlinarith [hδβge, hMG, hCS, hδβnn]

end Work.FTS_EllLimOK.ProducerH.H2.Dev
