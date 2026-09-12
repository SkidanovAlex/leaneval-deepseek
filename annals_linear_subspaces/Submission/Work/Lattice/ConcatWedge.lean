import Mathlib
import Submission.Work.Lattice.Prop5Assembly
import Submission.Commons.Analysis.Real.prod_prefix_le_prod_rpow
import Submission.Commons.Analysis.InnerProductSpace.norm_exteriorPower_map_sub_le
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal
import Submission.Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod

/-!
# The concatenated wedge of a family close to orthonormal `L`-directions

This module isolates the **analytic core of Prop 5's output** (de Saxcé §3), independently of the
way the vectors are produced.

Input: an orthonormal family `u : Fin m → ℝᵈ` of `L = modelX ℓ`, a family `v : Fin m → ℝᵈ`, scales
`M : ℕ → ℝ` (the `i`-th vector has scale `M (i+1)`) and `δ ≥ 0` with

    `‖v i - M (i+1) • u i‖ ≤ δ * M (i+1)`.

Conclusions:

* `concat_dominated` — the `π₊`-**dominance** of the wedge,
  `(2 - (1+δ)^m) ∏ M ≤ ‖π₊(v₁∧⋯∧v_m)‖`;
* `concat_norm_le` — the Hadamard bound `‖v₁∧⋯∧v_m‖ ≤ (1+δ)^m ∏ M`;
* `concat_log_le` — for a family of length `ℓ` with **nondecreasing** scales, the log-wedge of
  every `k`-prefix is at most the `k/ℓ`-fraction of the total log-scale sum plus `k log(1+δ)`;
* `sum_log_prefix_le` — the prefix averaging lemma used by the previous point.

Module `Submission.Work.Lattice.ConcatWedge`, namespace `Submission.ConcatWedge`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Submission.ConcatWedge

open Submission.Prop5Block
open Submission.Prop5Assembly
open Submission.WedgeBlocks
open Submission.WedgeBlockZero
open Submission.ExteriorCoordinates
open Submission.GraysonData

variable {d : ℕ}

/-- **Prefix averaging of the scales** (log form of
`Commons.Analysis.Real.prod_prefix_le_prod_rpow`): for a positive nondecreasing sequence `M`,
`∑_{i<k} log M(i+1) ≤ (k/ℓ) ∑_{i<ℓ} log M(i+1)`. -/
theorem sum_log_prefix_le {ℓ k : ℕ} (hℓ : 0 < ℓ) (hk : k ≤ ℓ) {M : ℕ → ℝ}
    (hpos : ∀ i, 0 < i → i ≤ ℓ → 0 < M i) (hmono : Monotone M) :
    ∑ i ∈ Finset.range k, Real.log (M (i + 1)) ≤
      ((k : ℝ) / (ℓ : ℝ)) * ∑ i ∈ Finset.range ℓ, Real.log (M (i + 1)) := by
  have hprod := Commons.Analysis.Real.prod_prefix_le_prod_rpow (d := ℓ) (k := k) hℓ hk hpos hmono
  have hkpos : ∀ i ∈ Finset.range k, 0 < M (i + 1) := fun i hi =>
    hpos (i + 1) (Nat.succ_pos i) (by have := Finset.mem_range.mp hi; omega)
  have hℓpos : ∀ i ∈ Finset.range ℓ, 0 < M (i + 1) := fun i hi =>
    hpos (i + 1) (Nat.succ_pos i) (Finset.mem_range.mp hi)
  have hA : 0 < ∏ i ∈ Finset.range k, M (i + 1) := Finset.prod_pos hkpos
  have hB : 0 < ∏ i ∈ Finset.range ℓ, M (i + 1) := Finset.prod_pos hℓpos
  have hlog := Real.log_le_log hA hprod
  rw [Real.log_prod (fun i hi => ne_of_gt (hkpos i hi))] at hlog
  rw [Real.log_rpow hB] at hlog
  rw [Real.log_prod (fun i hi => ne_of_gt (hℓpos i hi))] at hlog
  exact hlog

/-- **The `π₊`-dominance of a concatenated family.**  If `u` is an orthonormal family of
`L = modelX ℓ` and `v i` is within relative error `δ` of `M(i+1) • u i`, then the block-`0` part
of `v₁∧⋯∧v_m` dominates with the constant `2 - (1+δ)^m`. -/
theorem concat_dominated {m ℓ : ℕ} (hm : 0 < m) {u v : Fin m → E d} {M : ℕ → ℝ} {δ : ℝ}
    (huON : Orthonormal ℝ u) (huL : ∀ i, u i ∈ modelX (d := d) ℓ)
    (hM : ∀ i : Fin m, 0 < M (i.val + 1)) (hδ0 : 0 ≤ δ)
    (hv : ∀ i : Fin m, ‖v i - M (i.val + 1) • u i‖ ≤ δ * M (i.val + 1)) :
    (2 - (1 + δ) ^ m) * (∏ i : Fin m, M (i.val + 1)) ≤
      ‖blockElem (d := d) (k := m) (ℓ := ℓ) (exteriorPower.ιMulti ℝ m v) 0‖ := by
  classical
  -- the projections of the `v i` are close to the scaled orthonormal directions
  have hpert : ∀ i : Fin m,
      ‖modelProj (d := d) ℓ (v i) - M (i.val + 1) • u i‖ ≤ δ * M (i.val + 1) := by
    intro i
    have h1 : modelProj (d := d) ℓ (v i) - M (i.val + 1) • u i =
        modelProj (d := d) ℓ (v i - M (i.val + 1) • u i) := by
      rw [map_sub, map_smul, modelProj_fixes_mem ℓ (huL i)]
    rw [h1]
    exact le_trans (norm_modelProj_le ℓ _) (hv i)
  -- the normalised projected family
  set w : Fin m → E d := fun i => (M (i.val + 1))⁻¹ • (modelProj (d := d) ℓ (v i)) with hwdef
  have hwclose : ∀ i : Fin m, ‖w i - u i‖ ≤ δ := by
    intro i
    have hMi : 0 < M (i.val + 1) := hM i
    have h1 : w i - u i =
        (M (i.val + 1))⁻¹ • (modelProj (d := d) ℓ (v i) - M (i.val + 1) • u i) := by
      simp only [hwdef]
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hMi.ne', one_smul]
    rw [h1, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hMi]
    calc (M (i.val + 1))⁻¹ * ‖modelProj (d := d) ℓ (v i) - M (i.val + 1) • u i‖
        ≤ (M (i.val + 1))⁻¹ * (δ * M (i.val + 1)) :=
          mul_le_mul_of_nonneg_left (hpert i) (inv_nonneg.mpr hMi.le)
      _ = δ := by
          rw [mul_comm δ, ← mul_assoc, inv_mul_cancel₀ hMi.ne', one_mul]
  -- the projected family is a scaled version of `w`
  have hscaled : (fun i : Fin m => modelProj (d := d) ℓ (v i)) =
      (fun i : Fin m => M (i.val + 1) • w i) := by
    funext i
    simp only [hwdef]
    rw [smul_smul, mul_inv_cancel₀ (hM i).ne', one_smul]
  have hwedge : exteriorPower.ιMulti ℝ m (fun i : Fin m => modelProj (d := d) ℓ (v i)) =
      (∏ i : Fin m, M (i.val + 1)) • exteriorPower.ιMulti ℝ m w := by
    rw [hscaled, AlternatingMap.map_smul_univ]
  have hnormw : ‖exteriorPower.ιMulti ℝ m (fun i : Fin m => modelProj (d := d) ℓ (v i))‖ =
      (∏ i : Fin m, M (i.val + 1)) * ‖exteriorPower.ιMulti ℝ m w‖ := by
    rw [hwedge, norm_smul, Real.norm_eq_abs, abs_of_pos (Finset.prod_pos (fun i _ => hM i))]
  -- the orthonormal side has norm `1`
  have hu1 : ‖exteriorPower.ιMulti ℝ m u‖ = 1 :=
    Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal u huON hm
  have hPu : exteriorPower.map m ((modelProjCL d ℓ : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d)
      (exteriorPower.ιMulti ℝ m u) = exteriorPower.ιMulti ℝ m u := by
    rw [modelProjCL_coe, exteriorPower.map_apply_ιMulti]
    congr 1
    funext i
    exact modelProj_fixes_mem ℓ (huL i)
  have hPw : exteriorPower.map m ((modelProjCL d ℓ : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d)
      (exteriorPower.ιMulti ℝ m w) = exteriorPower.ιMulti ℝ m w := by
    rw [modelProjCL_coe, exteriorPower.map_apply_ιMulti]
    congr 1
    funext i
    simp only [Function.comp_apply, hwdef, map_smul, modelProj_idem]
  -- the perturbation estimate
  have hlow := Commons.Analysis.InnerProductSpace.norm_exteriorPower_map_sub_le
    (E := E d) (modelProjCL d ℓ) (fun x => norm_modelProj_le ℓ x)
    (fun x => modelProj_idem ℓ x) hδ0 u w (fun i => huON.norm_eq_one i) hwclose
  rw [hPu, hu1, hPw] at hlow
  -- identify the block-`0` part
  have hblk : blockElem (d := d) (k := m) (ℓ := ℓ) (exteriorPower.ιMulti ℝ m v) 0 =
      exteriorPower.ιMulti ℝ m (fun i : Fin m => modelProj (d := d) ℓ (v i)) := by
    rw [blockElem_zero_eq_map_modelProj (d := d) (k := m) (ℓ := ℓ),
      exteriorPower.map_apply_ιMulti]
    rfl
  rw [hblk, hnormw]
  have hprodpos : 0 < ∏ i : Fin m, M (i.val + 1) := Finset.prod_pos (fun i _ => hM i)
  nlinarith [hlow, hprodpos]

/-- **Hadamard bound for a perturbed family.** -/
theorem concat_norm_le {m : ℕ} {v : Fin m → E d} {M : ℕ → ℝ} {δ : ℝ}
    (hvnorm : ∀ i : Fin m, ‖v i‖ ≤ M (i.val + 1) * (1 + δ)) :
    ‖exteriorPower.ιMulti ℝ m v‖ ≤ (∏ i : Fin m, M (i.val + 1)) * (1 + δ) ^ m := by
  calc ‖exteriorPower.ιMulti ℝ m v‖ ≤ ∏ i : Fin m, ‖v i‖ :=
        Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod v
    _ ≤ ∏ i : Fin m, (M (i.val + 1) * (1 + δ)) :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hvnorm i)
    _ = (∏ i : Fin m, M (i.val + 1)) * (1 + δ) ^ m := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
        simp

/-- **The log-wedge of a `k`-prefix.**  For a family of length `ℓ` with nondecreasing positive
scales and `δ ≥ 0`, the log-norm of the `k`-fold wedge of the prefix is at most the `k/ℓ`-fraction
of the total log-scale sum plus `k log (1+δ)`. -/
theorem concat_log_le {ℓ : ℕ} (hℓ : 0 < ℓ) {v : Fin ℓ → E d} {M : ℕ → ℝ} {δ : ℝ}
    (hM : ∀ i, 0 < i → i ≤ ℓ → 0 < M i) (hMmono : Monotone M) (hδ0 : 0 ≤ δ)
    (hvnorm : ∀ i : Fin ℓ, ‖v i‖ ≤ M (i.val + 1) * (1 + δ)) {k : ℕ} (hk : k ≤ ℓ)
    (hpos : 0 < ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => v (Fin.castLE hk i))‖) :
    Real.log ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => v (Fin.castLE hk i))‖ ≤
      ((k : ℝ) / (ℓ : ℝ)) * (∑ i ∈ Finset.range ℓ, Real.log (M (i + 1))) +
        (k : ℝ) * Real.log (1 + δ) := by
  classical
  have h1 : ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => v (Fin.castLE hk i))‖ ≤
      (∏ i : Fin k, M (i.val + 1)) * (1 + δ) ^ k := by
    exact concat_norm_le (M := M) (δ := δ)
      (fun i => hvnorm (Fin.castLE hk i))
  have h2 := Real.log_le_log hpos h1
  have hkpos : ∀ i ∈ Finset.range k, 0 < M (i + 1) := fun i hi =>
    hM (i + 1) (Nat.succ_pos i) (by have := Finset.mem_range.mp hi; omega)
  have hP : 0 < ∏ i ∈ Finset.range k, M (i + 1) := Finset.prod_pos hkpos
  have h3 : Real.log ((∏ i : Fin k, M (i.val + 1)) * (1 + δ) ^ k) =
      (∑ i ∈ Finset.range k, Real.log (M (i + 1))) + (k : ℝ) * Real.log (1 + δ) := by
    rw [Fin.prod_univ_eq_prod_range (fun i => M (i + 1)) k]
    rw [Real.log_mul (ne_of_gt hP) (by positivity)]
    rw [Real.log_pow]
    rw [Real.log_prod (fun i hi => ne_of_gt (hkpos i hi))]
  rw [h3] at h2
  have h4 := sum_log_prefix_le (ℓ := ℓ) (k := k) hℓ hk hM hMmono
  linarith [h2, h4]

end Submission.ConcatWedge

end
