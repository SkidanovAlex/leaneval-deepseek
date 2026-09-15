import Submission.FUP.SphericalProjection
import Submission.FUP.WeightPiece
import Submission.Commons.MeasureTheory.Integral.integral_smoothTransition_diff_div_sq_pos

open MeasureTheory Metric Filter
open scoped Real BigOperators Topology

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# Section 4 of the paper: modifying the weight function

The paper's §4 replaces a weight `ω` satisfying the hypotheses of the Beurling–Malliavin theorem
by a weight `ω̃ ≤ ω` whose spherical projections `π ω̃_k` are *constant* on the dyadic pieces, so
that the oscillatory integral `∫ ⟨D²ω̃_k(t ŷ)v̂,v̂⟩ dt` telescopes.

This module collects the algebraic part of that construction:

* linearity of the weighted spherical projection `sphProj f v = ∫_{t>0} f(t v) t^{-2} dt`;
* the constants `p_k = π ψ_k = ∫_0^∞ ψ_k(t) t^{-2} dt`, which satisfy `p_k ≍ 2^{-k}`;
* the "radial" projection `h_k(x) = π ω_k(x̂)` used to define the correction `g_k`.
-/

section Algebra

lemma sphProj_add (f g : ℝᵈ → ℝ) (v : ℝᵈ)
    (hf : IntegrableOn (fun t : ℝ => f (t • v) * (t ^ 2)⁻¹) (Set.Ioi 0))
    (hg : IntegrableOn (fun t : ℝ => g (t • v) * (t ^ 2)⁻¹) (Set.Ioi 0)) :
    sphProj (fun x => f x + g x) v = sphProj f v + sphProj g v := by
  simp only [sphProj]
  rw [show (fun t : ℝ => (f (t • v) + g (t • v)) * (t ^ 2)⁻¹)
      = fun t : ℝ => f (t • v) * (t ^ 2)⁻¹ + g (t • v) * (t ^ 2)⁻¹ from by
        funext t; ring]
  rw [integral_add hf hg]

lemma sphProj_const_mul (c : ℝ) (f : ℝᵈ → ℝ) (v : ℝᵈ) :
    sphProj (fun x => c * f x) v = c * sphProj f v := by
  simp only [sphProj]
  rw [show (fun t : ℝ => (c * f (t • v)) * (t ^ 2)⁻¹)
      = fun t : ℝ => c * (f (t • v) * (t ^ 2)⁻¹) from by
        funext t; ring]
  rw [integral_const_mul]

end Algebra

section Pk

/-- The weighted spherical projection of the dyadic piece `ψ_k`:
`p_k = π ψ_k = ∫_0^∞ ψ_k(t) t^{-2} dt`. -/
noncomputable def pk (k : ℕ) : ℝ := ∫ t in Set.Ioi (0 : ℝ), dyadPsi k t * (t ^ 2)⁻¹

lemma sphProj_radialPsi (k : ℕ) (v : ℝᵈ) :
    sphProj (fun x : ℝᵈ => radialPsi (d := d) k x) v
      = ∫ t in Set.Ioi (0 : ℝ), dyadPsi k (t * ‖v‖) * (t ^ 2)⁻¹ := by
  have h1 : sphProj (fun x : ℝᵈ => radialPsi (d := d) k x) v
      = sphProj (fun x : ℝᵈ => dyadPsi k ‖x‖) v :=
    sphProj_congr (fun x => rfl) v
  rw [h1, sphProj_radial]

/-- On unit vectors the projection of `ψ_k` is the constant `p_k`. -/
lemma sphProj_radialPsi_eq_pk (k : ℕ) {v : ℝᵈ} (hv : ‖v‖ = 1) :
    sphProj (fun x : ℝᵈ => radialPsi (d := d) k x) v = pk k := by
  rw [sphProj_radialPsi]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  rw [hv, mul_one]

/-- Rescaling a weighted half-line integral: `∫_0^∞ ψ(t/c) t^{-2} dt = c⁻¹ ∫_0^∞ ψ(t) t^{-2} dt`
for `c > 0`. -/
lemma integral_div_self_sq_eq (ψ : ℝ → ℝ) {c : ℝ} (hc : 0 < c) :
    (∫ t in Set.Ioi (0 : ℝ), ψ (t / c) * (t ^ 2)⁻¹)
      = c⁻¹ * ∫ t in Set.Ioi (0 : ℝ), ψ t * (t ^ 2)⁻¹ := by
  have h := MeasureTheory.integral_comp_mul_left_Ioi
    (fun x : ℝ => ψ x * (x ^ 2)⁻¹) 0 (inv_pos.mpr hc)
  simp only [mul_zero] at h
  have h2 : (∫ x in Set.Ioi (0 : ℝ), (fun x : ℝ => ψ x * (x ^ 2)⁻¹) (c⁻¹ * x))
      = c ^ 2 * ∫ t in Set.Ioi (0 : ℝ), ψ (t / c) * (t ^ 2)⁻¹ := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    rw [div_eq_inv_mul]
    field_simp
  rw [h2, smul_eq_mul, inv_inv] at h
  have key : c * (c * ∫ t in Set.Ioi (0 : ℝ), ψ (t / c) * (t ^ 2)⁻¹)
      = c * ∫ t in Set.Ioi (0 : ℝ), ψ t * (t ^ 2)⁻¹ := by
    calc c * (c * ∫ t in Set.Ioi (0 : ℝ), ψ (t / c) * (t ^ 2)⁻¹)
        = c ^ 2 * ∫ t in Set.Ioi (0 : ℝ), ψ (t / c) * (t ^ 2)⁻¹ := by ring
      _ = c * ∫ t in Set.Ioi (0 : ℝ), ψ t * (t ^ 2)⁻¹ := h
  have hcI : c * ∫ t in Set.Ioi (0 : ℝ), ψ (t / c) * (t ^ 2)⁻¹
      = ∫ t in Set.Ioi (0 : ℝ), ψ t * (t ^ 2)⁻¹ := mul_left_cancel₀ hc.ne' key
  rw [← hcI, inv_mul_cancel_left₀ hc.ne']

lemma dyadPhi_one (t : ℝ) : dyadPhi 1 t = dyadCut t := by
  have h := dyadPhi_succ 0 t
  simpa using h

lemma dyadPhi_two (t : ℝ) : dyadPhi 2 t = dyadCut (t / 2) := by
  have h := dyadPhi_succ 1 t
  simpa using h

/-- `ψ_{k+1}(t) = ψ_1(t / 2^k)`. -/
lemma dyadPsi_succ_eq (k : ℕ) (t : ℝ) : dyadPsi (k + 1) t = dyadPsi 1 (t / 2 ^ k) := by
  have h1 : dyadPsi (k + 1) t = dyadCut (t / 2 ^ k) - dyadCut (t / 2 ^ (k + 1)) := by
    show dyadPhi (k + 1) t - dyadPhi (k + 1 + 1) t = _
    rw [dyadPhi_succ k, dyadPhi_succ (k + 1)]
  have h2 : dyadPsi 1 (t / 2 ^ k) = dyadCut (t / 2 ^ k) - dyadCut (t / 2 ^ k / 2) := by
    show dyadPhi 1 (t / 2 ^ k) - dyadPhi 2 (t / 2 ^ k) = _
    rw [dyadPhi_one, dyadPhi_two]
  rw [h1, h2, div_div, pow_succ]

/-- `p_{k+1} = 2^{-k} p_1`. -/
lemma pk_succ (k : ℕ) : pk (k + 1) = ((2 : ℝ) ^ k)⁻¹ * pk 1 := by
  rw [pk, pk]
  rw [show (fun t : ℝ => dyadPsi (k + 1) t * (t ^ 2)⁻¹)
      = fun t : ℝ => dyadPsi 1 (t / 2 ^ k) * (t ^ 2)⁻¹ from by
        funext t; rw [dyadPsi_succ_eq]]
  exact integral_div_self_sq_eq (dyadPsi 1) (pow_pos (by norm_num) k)

lemma pk_one_eq : pk 1 = ∫ t in Set.Ioi (0 : ℝ),
    (Real.smoothTransition (t - 1) - Real.smoothTransition (t / 2 - 1)) * (t ^ 2)⁻¹ := by
  rw [pk]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  congr 1
  show dyadPhi 1 t - dyadPhi 2 t = _
  rw [dyadPhi_one, dyadPhi_two, dyadCut, dyadCut]

/-- The universal constant `c_0 = p_1 > 0`. -/
noncomputable def pkConst : ℝ := pk 1

lemma pk_one_pos : 0 < pk 1 := by
  rw [pk_one_eq]
  exact Commons.MeasureTheory.Integral.integral_smoothTransition_diff_div_sq_pos

lemma pkConst_pos : 0 < pkConst := pk_one_pos

lemma pkConst_eq : pkConst = pk 1 := rfl

/-- `p_k = 2^{-k}·(2 p_1)` for `k ≥ 1`: the `≍ 2^{-k}` behaviour of the paper. -/
lemma pk_eq (k : ℕ) (hk : 1 ≤ k) : pk k = ((2 : ℝ) ^ k)⁻¹ * (2 * pkConst) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [pk_succ, pkConst_eq]
  have h2 : (2 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ j := by rw [pow_succ]; ring
  rw [h2]
  field_simp

lemma pk_ne_zero (k : ℕ) (hk : 1 ≤ k) : pk k ≠ 0 := by
  have h := pk_eq k hk
  rw [h]
  exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ (by norm_num))) (mul_pos (by norm_num) pkConst_pos).ne'

/-- The inverse of `p_k`: `(p_k)⁻¹ = (2p_1)⁻¹·2^k`. -/
lemma inv_pk_eq (k : ℕ) (hk : 1 ≤ k) : (pk k)⁻¹ = (2 * pkConst)⁻¹ * (2 : ℝ) ^ k := by
  rw [pk_eq k hk, mul_inv_rev, inv_inv]

lemma abs_inv_pk_le (k : ℕ) (hk : 1 ≤ k) :
    |(pk k)⁻¹| ≤ (2 * pkConst)⁻¹ * (2 : ℝ) ^ k := by
  have h1 : (0 : ℝ) ≤ (2 * pkConst)⁻¹ := inv_nonneg.mpr (mul_nonneg (by norm_num) pkConst_pos.le)
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
  rw [inv_pk_eq k hk, abs_of_nonneg (mul_nonneg h1 h2)]

end Pk

end Submission.FUP
