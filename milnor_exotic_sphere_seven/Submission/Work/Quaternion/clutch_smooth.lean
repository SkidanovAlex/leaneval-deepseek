import Mathlib
import Submission.Work.Milnor.QuatSphere

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Topology
open Metric (sphere)

namespace Work.Quaternion

noncomputable section

open Submission.Milnor

/-- Quaternion conjugation `star : ℍ → ℍ` is an isometry, hence continuous; it is also `ℝ`-linear,
so it is a continuous linear map. -/
def starCLM : Quaternion ℝ →L[ℝ] Quaternion ℝ where
  toFun := star
  map_add' := star_add
  map_smul' := Quaternion.star_smul
  cont := (show Isometry (star : Quaternion ℝ → Quaternion ℝ) from fun x y => by
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, ← star_sub, Quaternion.norm_star]).continuous

theorem contMDiff_star :
    ContMDiff 𝓘(ℝ, Quaternion ℝ) 𝓘(ℝ, Quaternion ℝ) ∞ (star : Quaternion ℝ → Quaternion ℝ) :=
  starCLM.contDiff.contMDiff

instance : ContMDiffMul 𝓘(ℝ, Quaternion ℝ) ∞ (Quaternion ℝ) where
  contMDiff_mul := by
    rw [contMDiff_iff]
    refine ⟨continuous_mul, fun x y => ?_⟩
    simp only [mfld_simps, chartAt_self_eq]
    rw [contDiffOn_univ]
    exact contDiff_mul

/-- A point of the unit sphere is nonzero. -/
theorem coe_ne_zero (x : QS3) : (x : Quaternion ℝ) ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [norm_coe]; exact one_ne_zero)

/-- On the unit sphere, inversion is quaternion conjugation. -/
theorem coe_inv_eq_star (x : QS3) : (x : Quaternion ℝ)⁻¹ = star (x : Quaternion ℝ) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [Quaternion.self_mul_star, Quaternion.normSq_eq_norm_mul_self, norm_coe, mul_one, Quaternion.coe_one]

/-- Inversion is smooth on the unit sphere. -/
theorem contMDiff_coe_inv :
    ContMDiff (𝓡 3) 𝓘(ℝ, Quaternion ℝ) ∞ (fun x : QS3 => (x : Quaternion ℝ)⁻¹) := by
  have h : (fun x : QS3 => (x : Quaternion ℝ)⁻¹) = fun x : QS3 => star (x : Quaternion ℝ) := by
    funext x
    exact coe_inv_eq_star x
  rw [h]
  exact contMDiff_star.comp contMDiff_coe_sphere

/-- The map `p ↦ (p.1 : ℍ) ^ k` is smooth, for every integer `k`. -/
theorem contMDiff_coe_zpow (k : ℤ) :
    ContMDiff ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ∞
      (fun p : QS3 × QS3 => (p.1 : Quaternion ℝ) ^ k) := by
  have hf : ContMDiff ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ∞
      (fun p : QS3 × QS3 => (p.1 : Quaternion ℝ)) :=
    contMDiff_coe_sphere.comp contMDiff_fst
  have hfi : ContMDiff ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ∞
      (fun p : QS3 × QS3 => ((p.1 : Quaternion ℝ))⁻¹) :=
    contMDiff_coe_inv.comp contMDiff_fst
  have hnz : ∀ p : QS3 × QS3, (p.1 : Quaternion ℝ) ≠ 0 := fun p => coe_ne_zero p.1
  induction k using Int.induction_on with
  | zero => simpa using contMDiff_const
  | succ n ih =>
      have h : (fun p : QS3 × QS3 => (p.1 : Quaternion ℝ) ^ ((n : ℤ) + 1)) =
          fun p : QS3 × QS3 => (p.1 : Quaternion ℝ) ^ (n : ℤ) * (p.1 : Quaternion ℝ) := by
        funext p
        rw [zpow_add_one₀ (hnz p)]
      rw [h]
      exact ih.mul hf
  | pred n ih =>
      have h : (fun p : QS3 × QS3 => (p.1 : Quaternion ℝ) ^ (-(n : ℤ) - 1)) =
          fun p : QS3 × QS3 => (p.1 : Quaternion ℝ) ^ (-(n : ℤ)) * (p.1 : Quaternion ℝ)⁻¹ := by
        funext p
        rw [zpow_sub_one₀ (hnz p)]
      rw [h]
      exact ih.mul hfi

open scoped Manifold ContDiff Topology in
open Submission.Milnor in
theorem clutch_smooth (k : ℤ) :
    ContMDiff ((𝓡 3).prod (𝓡 3)) (𝓡 3) ∞ (fun p : QS3 × QS3 => clutch k p) := by
  have h2 : ContMDiff ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ∞
      (fun p : QS3 × QS3 => (p.2 : Quaternion ℝ)) :=
    contMDiff_coe_sphere.comp contMDiff_snd
  have hfi : ContMDiff ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ∞
      (fun p : QS3 × QS3 => (((p.1 : Quaternion ℝ))⁻¹)) :=
    contMDiff_coe_inv.comp contMDiff_fst
  have hF : ContMDiff ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ∞
      (fun p : QS3 × QS3 => clutchVal k p.1 p.2) :=
    ((contMDiff_coe_zpow k).mul h2).mul hfi
  have hmem : ∀ p : QS3 × QS3, clutchVal k p.1 p.2 ∈ sphere (0 : Quaternion ℝ) 1 := fun p => by
    rw [Metric.mem_sphere, dist_zero_right]
    exact norm_clutchVal k p.1 p.2
  refine (hF.codRestrict_sphere hmem).congr ?_
  intro p
  exact Subtype.ext rfl

end

end Work.Quaternion
