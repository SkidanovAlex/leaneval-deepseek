/-
# `fakeLower_of_Fstar` — a pointwise lower bound on the physical vorticity

This module proves `Work.FTS.Physical.RegPkg.fakeLower_of_Fstar`: if, at every fake time `τ ≥ 0`,
the full self-similar profile `F = F_* + g` is *somewhere* bounded below in modulus by
`3α/100 > 0`, then the physical vorticity

  `ω(x,τ) = A(τ)⁻¹ · F(ρ(x)^{3α}/B(τ), θ(x), τ) · e_θ(x)`

is bounded below in modulus by `(3α/100)/A(τ)` **at a suitable point** `x` (depending on `τ`).

This is a purely pointwise statement: no regularity, no integrability, no support condition is
needed.  The content is that the map sending the self-similar coordinates `(z,θ)` to a physical
point `x` is *surjective onto* the half plane `z > 0`, `θ ∈ [0,π/2)`: given `z > 0` and
`0 ≤ θ < π/2` and a clock value `B(τ) > 0`, the point

  `x = !₂[ρ cos θ, 0, ρ sin θ]`,   `ρ = (B(τ)·z)^{1/(3α)}`,

has `radial x = ρ cos θ > 0` (so `e_θ(x)` is a *unit* vector), `θ(x) = θ` and
`ρ(x)^{3α}/B(τ) = z`.  Evaluating `ω` there and taking norms gives

  `‖ω(x,τ)‖ = A(τ)⁻¹ · |F_*(3α, z, θ) + g(z,θ,τ)| · ‖e_θ(x)‖ ≥ A(τ)⁻¹ · 3α/100`.

The two ingredients are the coordinate computation (`polarPoint_coords` below) and the norm of a
scalar multiple of a unit vector.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.Regularity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Physical.RegPkg

/-- **The self-similar half plane is covered by physical space.**  For `B > 0`, `z > 0` and
`0 ≤ θ < π/2`, the point `x = ρ·(cos θ, 0, sin θ)` with `ρ = (B z)^{1/p} > 0` satisfies
`radial x ≠ 0` (so that `e_θ(x)` is a unit vector), `θ(x) = θ` (the polar angle of `x` is exactly
`θ`), and `ρ(x)^p/B = z` (the self-similar variable `ρ(x)^p` rescaled by the clock is exactly
`z`). -/
theorem polarPoint_coords {p B z θ : ℝ} (hp : 0 < p) (hB : 0 < B) (hz : 0 < z)
    (hθ0 : 0 ≤ θ) (hθlt : θ < Real.pi / 2) :
    ∃ x : Work.Cyl.R3, Work.Cyl.radial x ≠ 0 ∧ Work.Cyl.theta x = θ ∧
      Work.Cyl.rho x ^ p / B = z := by
  have hBz : 0 < B * z := mul_pos hB hz
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθlt⟩
  have hρ : 0 < (B * z) ^ (1 / p) := Real.rpow_pos_of_pos hBz _
  have hρp : ((B * z) ^ (1 / p)) ^ p = B * z := by
    rw [← Real.rpow_mul hBz.le, one_div, inv_mul_cancel₀ (ne_of_gt hp), Real.rpow_one]
  let x : Work.Cyl.R3 := !₂[(B * z) ^ (1 / p) * Real.cos θ, 0, (B * z) ^ (1 / p) * Real.sin θ]
  have hx0 : x 0 = (B * z) ^ (1 / p) * Real.cos θ := by simp [x]
  have hx1 : x 1 = 0 := by simp [x]
  have hx2 : x 2 = (B * z) ^ (1 / p) * Real.sin θ := by simp [x]
  have hradSq : Work.Cyl.radSq x = ((B * z) ^ (1 / p) * Real.cos θ) ^ 2 := by
    simp [Work.Cyl.radSq, hx0, hx1]
  have haxial : Work.Cyl.axial x = (B * z) ^ (1 / p) * Real.sin θ := by
    simp [Work.Cyl.axial, hx2]
  have hradial : Work.Cyl.radial x = (B * z) ^ (1 / p) * Real.cos θ := by
    rw [Work.Cyl.radial, hradSq, Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos hρ hcos)]
  refine ⟨x, ne_of_gt (by rw [hradial]; exact mul_pos hρ hcos), ?_, ?_⟩
  · rw [Work.Cyl.theta, hradial, haxial]
    have htan : (B * z) ^ (1 / p) * Real.sin θ / ((B * z) ^ (1 / p) * Real.cos θ)
        = Real.tan θ := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp
    rw [htan, Real.arctan_tan (by linarith [Real.pi_pos]) hθlt]
  · rw [Work.Cyl.rho, hradSq, haxial]
    have hsq : ((B * z) ^ (1 / p) * Real.cos θ) ^ 2
        + ((B * z) ^ (1 / p) * Real.sin θ) ^ 2 = ((B * z) ^ (1 / p)) ^ 2 := by
      rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_pos hρ, hρp,
      mul_div_cancel_left₀ z (ne_of_gt hB)]

/-- **A pointwise lower bound for the physical vorticity, from a pointwise lower bound on the
profile `F = F_* + g`.**  If at every fake time `τ ≥ 0` the full profile is bounded below in
modulus by `3α/100` at some point `z > 0`, `θ ∈ Iθ`, `θ < π/2` of the self-similar half plane,
then the physical vorticity is bounded below in modulus by `(3α/100)/A(τ)` at a point depending
on `τ`. -/
theorem fakeLower_of_Fstar {α : ℝ} (hα : 0 < α) {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (hApos : ∀ τ : ℝ, 0 ≤ τ → 0 < A τ) (hBpos : ∀ τ : ℝ, 0 ≤ τ → 0 < B τ)
    (hF : ∀ τ : ℝ, 0 ≤ τ → ∃ z : ℝ, 0 < z ∧ ∃ θ : ℝ, θ ∈ Work.Spaces.Iθ ∧ θ < Real.pi / 2 ∧
      3 * α / 100 ≤ |Work.Construction.Fstar (3 * α) z θ + g z θ τ|) :
    ∃ c : ℝ, 0 < c ∧ ∀ τ : ℝ, 0 ≤ τ → ∃ x : Work.FTS.Regularity.R3,
      c / A τ ≤ ‖Work.FTS.Regularity.physVort α A B g x τ‖ := by
  refine ⟨3 * α / 100, by linarith, ?_⟩
  intro τ hτ
  obtain ⟨z, hz, θ, hθmem, hθlt, hbound⟩ := hF τ hτ
  have hθ0 : 0 ≤ θ := hθmem.1
  have hp : 0 < Work.FTS.Regularity.pExp α := by
    rw [Work.FTS.Regularity.pExp]; linarith
  obtain ⟨x, hrne, hth, hrz⟩ :=
    polarPoint_coords (p := Work.FTS.Regularity.pExp α) (B := B τ) hp (hBpos τ hτ) hz hθ0 hθlt
  refine ⟨x, ?_⟩
  have hA : 0 < A τ := hApos τ hτ
  have hprof : Work.ConstructionInstance.profile (Work.FTS.Regularity.pExp α)
      (Work.FTS.Regularity.gSlice g τ) (Work.Cyl.rho x ^ Work.FTS.Regularity.pExp α / B τ)
      (Work.Cyl.theta x) = Work.Construction.Fstar (3 * α) z θ + g z θ τ := by
    rw [hth, hrz, Work.ConstructionInstance.profile_of_nonneg hθ0]
    rfl
  have hnorm : ‖Work.FTS.Regularity.physVort α A B g x τ‖
      = (A τ)⁻¹ * |Work.Construction.Fstar (3 * α) z θ + g z θ τ| := by
    rw [Work.FTS.Regularity.physVort, Work.ConstructionInstance.omegaSz,
      norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hA), hprof, Work.Cyl.norm_eTheta x hrne, mul_one]
  rw [hnorm, show (3 * α / 100) / A τ = (A τ)⁻¹ * (3 * α / 100) by ring]
  exact mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hA.le)

end Work.FTS.Physical.RegPkg
