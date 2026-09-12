import Mathlib
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_le_pow_of_norm_sub_le
import Submission.Commons.Analysis.InnerProductSpace.norm_exteriorPower_map_sub_le

/-!
# Cone perturbation for the `π₊`-condition (Prop 5, step B)

Paper §3, the last step of the proof of Prop 5: if `u₁,…,u_i` are orthonormal with
`‖π₊(u₁∧…∧u_i)‖ ⪆ 1`, and `v_k` approximates `u_k` with controlled relative error, then
`‖π₊(v₁∧…∧v_i)‖ ⪆ ∏‖v_k‖ ⪆ ‖v₁∧…∧v_i‖` — the **cone condition** consumed by the model
dictionary (`ModelCone.model_prop1_part2`, `WedgeContract.*`).

This module isolates the estimate in the abstract form (`π₊` = an arbitrary orthogonal
projection `P` of norm `≤ 1`):

* `cone_perturbation`: for a unit family `u` and a family `v` with `‖v_k − u_k‖ ≤ δ`,
  `‖⋀^i P (v₁∧…∧v_i)‖ ≥ [(c − ((1+δ)^i − 1))/(1+δ)^i]·‖v₁∧…∧v_i‖`
  whenever `c ≤ ‖⋀^i P (u₁∧…∧u_i)‖` and `c > (1+δ)^i − 1`;
* `cone_perturbation_scaled`: the same with `‖v_k − ρ_k u_k‖ ≤ δ·ρ_k` (`ρ_k > 0`), i.e. for
  the actual annulus vectors of `FlagAnnulus.exists_flagMember_near_direction`.

Uses the two fleet lemmas `Commons.Analysis.InnerProductSpace.norm_exteriorPower_map_sub_le`
and `...norm_iMulti_le_pow_of_norm_sub_le`.
-/

noncomputable section
open Set Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Submission.ConePerturbation

open Commons.Analysis.InnerProductSpace

/-- **Cone perturbation (unit form).**  Let `P` be a projection of norm at most `1`
(`‖P x‖ ≤ ‖x‖`, `P ∘ P = P`), `u` a unit family whose `P`-wedge has norm at least `c`, and
`v` a family with `‖v_k − u_k‖ ≤ δ`.  If `c > (1+δ)^i − 1`, then the `P`-wedge of `v`
controls the wedge of `v` with the explicit constant `(c − ((1+δ)^i − 1))/(1+δ)^i`. -/
theorem cone_perturbation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {i : ℕ} (P : E →L[ℝ] E) (hP1 : ∀ x, ‖P x‖ ≤ ‖x‖)
    (hP2 : ∀ x, P (P x) = P x) {δ c : ℝ} (hδ : 0 ≤ δ) (hc : (1 + δ) ^ i - 1 < c)
    (u v : Fin i → E) (hu : ∀ k, ‖u k‖ = 1) (hv : ∀ k, ‖v k - u k‖ ≤ δ)
    (hbig : c ≤ ‖exteriorPower.map i (P : E →ₗ[ℝ] E) (exteriorPower.ιMulti ℝ i u)‖) :
    ((c - ((1 + δ) ^ i - 1)) / (1 + δ) ^ i) * ‖exteriorPower.ιMulti ℝ i v‖ ≤
      ‖exteriorPower.map i (P : E →ₗ[ℝ] E) (exteriorPower.ιMulti ℝ i v)‖ := by
  have h1 := norm_exteriorPower_map_sub_le P hP1 hP2 hδ u v hu hv
  have h2 := norm_iMulti_le_pow_of_norm_sub_le hδ u v hu hv
  have htw : (0 : ℝ) < (1 + δ) ^ i := by positivity
  have hc' : c - ((1 + δ) ^ i - 1) ≤
      ‖exteriorPower.map i (P : E →ₗ[ℝ] E) (exteriorPower.ιMulti ℝ i v)‖ := by
    linarith [h1, hbig]
  have hnn : 0 ≤ c - ((1 + δ) ^ i - 1) := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ htw]
  calc (c - ((1 + δ) ^ i - 1)) * ‖exteriorPower.ιMulti ℝ i v‖
      ≤ (c - ((1 + δ) ^ i - 1)) * (1 + δ) ^ i := mul_le_mul_of_nonneg_left h2 hnn
    _ ≤ ‖exteriorPower.map i (P : E →ₗ[ℝ] E) (exteriorPower.ιMulti ℝ i v)‖ * (1 + δ) ^ i :=
        mul_le_mul_of_nonneg_right hc' htw.le

/-- **Cone perturbation (scaled form)**: the annulus version — `‖v_k − ρ_k·u_k‖ ≤ δ·ρ_k`
with `ρ_k > 0`. -/
theorem cone_perturbation_scaled {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {i : ℕ} (P : E →L[ℝ] E) (hP1 : ∀ x, ‖P x‖ ≤ ‖x‖)
    (hP2 : ∀ x, P (P x) = P x) {δ c : ℝ} (hδ : 0 ≤ δ) (hc : (1 + δ) ^ i - 1 < c)
    (u : Fin i → E) (hu : ∀ k, ‖u k‖ = 1)
    (hbig : c ≤ ‖exteriorPower.map i (P : E →ₗ[ℝ] E) (exteriorPower.ιMulti ℝ i u)‖)
    {ρ : Fin i → ℝ} (hρ : ∀ k, 0 < ρ k) (v : Fin i → E)
    (hv : ∀ k, ‖v k - ρ k • u k‖ ≤ δ * ρ k) :
    ((c - ((1 + δ) ^ i - 1)) / (1 + δ) ^ i) * ‖exteriorPower.ιMulti ℝ i v‖ ≤
      ‖exteriorPower.map i (P : E →ₗ[ℝ] E) (exteriorPower.ιMulti ℝ i v)‖ := by
  classical
  set w : Fin i → E := fun k => (ρ k)⁻¹ • v k with hw
  have hvw : v = fun k => ρ k • w k := by
    funext k
    simp only [hw]
    rw [smul_inv_smul₀ (ne_of_gt (hρ k))]
  have hwn : ∀ k, ‖w k - u k‖ ≤ δ := by
    intro k
    have h1 : w k - u k = (ρ k)⁻¹ • (v k - ρ k • u k) := by
      simp only [hw]
      rw [smul_sub, inv_smul_smul₀ (ne_of_gt (hρ k))]
    rw [h1, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hρ k)]
    calc (ρ k)⁻¹ * ‖v k - ρ k • u k‖ ≤ (ρ k)⁻¹ * (δ * ρ k) :=
          mul_le_mul_of_nonneg_left (hv k) (inv_nonneg.mpr (hρ k).le)
      _ = δ := by
        rw [mul_comm δ (ρ k), ← mul_assoc, inv_mul_cancel₀ (ne_of_gt (hρ k)), one_mul]
  have hkey := cone_perturbation P hP1 hP2 hδ hc u w hu hwn hbig
  rw [hvw]
  set R : ℝ := ∏ k, ρ k with hRdef
  have hRpos : 0 < R := Finset.prod_pos fun k _ => hρ k
  have hI : exteriorPower.ιMulti ℝ i (fun k => ρ k • w k) = R • exteriorPower.ιMulti ℝ i w :=
    AlternatingMap.map_smul_univ (exteriorPower.ιMulti ℝ i) ρ w
  have hM : exteriorPower.map i (P : E →ₗ[ℝ] E)
        (exteriorPower.ιMulti ℝ i (fun k => ρ k • w k)) =
      R • exteriorPower.map i (P : E →ₗ[ℝ] E) (exteriorPower.ιMulti ℝ i w) := by
    rw [hI, map_smul]
  rw [hI]
  simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hRpos]
  calc ((c - ((1 + δ) ^ i - 1)) / (1 + δ) ^ i) * (R * ‖exteriorPower.ιMulti ℝ i w‖)
      = R * (((c - ((1 + δ) ^ i - 1)) / (1 + δ) ^ i) * ‖exteriorPower.ιMulti ℝ i w‖) := by
        ring
    _ ≤ R * ‖exteriorPower.map i (P : E →ₗ[ℝ] E) (exteriorPower.ιMulti ℝ i w)‖ :=
        mul_le_mul_of_nonneg_left hkey hRpos.le

end Submission.ConePerturbation
