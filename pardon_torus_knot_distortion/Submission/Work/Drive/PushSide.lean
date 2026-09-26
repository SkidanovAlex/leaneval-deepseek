import Mathlib
import Submission.Work.Drive.CollarPushDefs

/-!
# Which side of the torus? The sign of the level function

The level function of the challenge is *explicit*:
`levP ψ x = ‖meridVec (ψ.symm x)‖` (`Work.Drive.levP`,
`Work.Drive.levP_eq_one_iff`); its level set `{1}` is the torus `F = ψ '' Σ`.  The standard torus
splits `ℝ³` into the open solid torus `solidTorus = {‖meridVec ·‖ < 1}` and the exterior
`torusExterior = {1 < ‖meridVec ·‖}`
(`Work.CoreTopology.mem_solidTorus_iff_norm_meridVec`,
`Work.CoreTopology.mem_torusExterior_iff_norm_meridVec`,
`Work.CoreTopology.isPreconnected_subset_solidTorus_or_torusExterior`).

Consequently **the sign of `levP ψ - 1` is constant on every connected subset of `ℝ³` avoiding
`F`**: a connected set off `F` lies in one of the two sides of the torus, and the sign of the
level is exactly the side.  This is the one-sidedness lemma that any "push the level off `F`"
argument needs, in the sharp form that it applies to *sets* (not just to paths).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive

open Work.CoreTopology

noncomputable section

/-- The level function of the transported torus, evaluated at a transported point. -/
theorem levP_psi_norm (ψ : R3 ≃ₜ R3) (x : R3) : levP ψ (ψ x) = ‖meridVec x‖ := by
  simp only [levP, levStd, Homeomorph.symm_apply_apply]

/-- **The level function of the challenge is the meridian radius, one side at a time.** -/
theorem levP_lt_one_iff (ψ : R3 ≃ₜ R3) (x : R3) :
    levP ψ x < 1 ↔ ψ.symm x ∈ solidTorus := by
  have h : levP ψ x = ‖meridVec (ψ.symm x)‖ := by simp only [levP, levStd]
  rw [h, mem_solidTorus_iff_norm_meridVec]

theorem one_lt_levP_iff (ψ : R3 ≃ₜ R3) (x : R3) :
    1 < levP ψ x ↔ ψ.symm x ∈ torusExterior := by
  have h : levP ψ x = ‖meridVec (ψ.symm x)‖ := by simp only [levP, levStd]
  rw [h, mem_torusExterior_iff_norm_meridVec]

/-- **One-sidedness of the level function.**  A preconnected subset of `ℝ³` on which `levP ψ`
never takes the value `1` (i.e. which misses the torus `F`) lies entirely on one side of it: the
sign of `levP ψ - 1` is constant on it. -/
theorem levP_sign_const (ψ : R3 ≃ₜ R3) (s : Set R3) (hs : IsPreconnected s)
    (hav : ∀ x ∈ s, levP ψ x ≠ 1) :
    (∀ x ∈ s, levP ψ x < 1) ∨ (∀ x ∈ s, 1 < levP ψ x) := by
  have hconn : IsPreconnected (ψ.symm '' s) := hs.image ψ.symm ψ.symm.continuous.continuousOn
  have havoid : (ψ.symm '' s) ⊆ (standard.carrier)ᶜ := by
    rintro z ⟨w, hw, rfl⟩ hz
    refine hav w hw ?_
    rw [show w = ψ (ψ.symm w) from (Homeomorph.apply_symm_apply ψ w).symm, levP_psi_norm]
    exact norm_meridVec_eq_one_iff.mpr hz
  rcases isPreconnected_subset_solidTorus_or_torusExterior hconn havoid with h | h
  · left
    intro x hx
    have h1 := h ⟨x, hx, rfl⟩
    rw [mem_solidTorus_iff_norm_meridVec] at h1
    have h2 : levP ψ x = ‖meridVec (ψ.symm x)‖ := by simp only [levP, levStd]
    rw [h2]; exact h1
  · right
    intro x hx
    have h1 := h ⟨x, hx, rfl⟩
    rw [mem_torusExterior_iff_norm_meridVec] at h1
    have h2 : levP ψ x = ‖meridVec (ψ.symm x)‖ := by simp only [levP, levStd]
    rw [h2]; exact h1

/-- The sign of `levP ψ - 1` is non-zero on every preconnected set avoiding `F`, with a single
sign: the product form needed by the push arguments. -/
theorem levP_sign_mul_pos (ψ : R3 ≃ₜ R3) (s : Set R3) (hs : IsPreconnected s)
    (hav : ∀ x ∈ s, levP ψ x ≠ 1) {x y : R3} (hx : x ∈ s) (hy : y ∈ s) :
    0 < (levP ψ x - 1) * (levP ψ y - 1) := by
  rcases levP_sign_const ψ s hs hav with h | h
  · have h1 := h x hx; have h2 := h y hy
    nlinarith
  · have h1 := h x hx; have h2 := h y hy
    nlinarith

end

end Work.Drive
