/-
# `Work.ConstructionInstance.Basic` — elementary properties of the self-similar vorticity

The first layer on top of `Defs.lean`:

* the bound `‖e_θ(x)‖ ≤ 1` (including the axis, where `e_θ = 0`);
* the **profile bound** `|F(z,θ)| ≤ 20·p·Γ(p/3,θ) + Cg` from the explicit bound of `F_*`
  (`Fstar_abs_le`) and the `L^∞` bound `Cg` of the perturbation `g` (which the `Spaces` area
  delivers from `Work.Spaces.Linf_H2`: `‖g‖_∞ = supAbs g ≤ 100/√(γ-1)·‖g‖_{H²} ≤ Cα²`), i.e.
  the deliverable's `‖F‖_∞ ≤ ‖F_*‖_∞ + ‖g‖_{H²}` via `Linf_H2`;
* the resulting `L^∞` bound `‖omegaS p g x‖ ≤ M` of the self-similar vorticity.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.ConstructionInstance.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-! ## The frame vector `e_θ` is bounded by one -/

theorem norm_eTheta_le_one (x : R3) : ‖Work.Cyl.eTheta x‖ ≤ 1 := by
  rcases eq_or_ne (Work.Cyl.radial x) 0 with h | h
  · have h1 : (1 : ℝ) / Work.Cyl.radial x = 0 := by rw [h, div_zero]
    have hz : Work.Cyl.eTheta x = 0 := by rw [Work.Cyl.eTheta, h1, zero_smul]
    rw [hz, norm_zero]; norm_num
  · rw [Work.Cyl.norm_eTheta x h]

/-! ## The profile bound -/

/-- **The `L^∞` bound of the profile** on the closed quadrant:
`|F(z,θ)| ≤ 20p·Γ(p/3,θ) + Cg` for `0 < p ≤ 1`, `z ≥ 0`, `θ ∈ [0,π/2]`. -/
theorem profile_abs_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ} {Cg : ℝ}
    (hg : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    (z : ℝ) (hz : 0 ≤ z) (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    |profile p g z θ| ≤ 20 * p * Gamma (p / 3) θ + Cg := by
  rw [profile_of_nonneg hθ.1]
  calc |Work.Construction.Fstar p z θ + g z θ|
      ≤ |Work.Construction.Fstar p z θ| + |g z θ| := abs_add_le _ _
    _ ≤ 20 * p * Gamma (p / 3) θ + Cg :=
        add_le_add (Fstar_abs_le hp hp1 hz hθ) (hg z θ hz hθ)

/-- **A global `L^∞` bound of the profile**, for `θ` in the range of `Work.Cyl.theta`
(`|θ| ≤ π/2`); the odd branch is reduced to the positive one by the definition of `profile`. -/
theorem profile_abs_le_of_abs {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ} {Cg : ℝ}
    (hg : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    (z : ℝ) (hz : 0 ≤ z) (θ : ℝ) (hθ : |θ| ≤ Real.pi / 2) :
    |profile p g z θ| ≤ 20 * p * Gamma (p / 3) |θ| + Cg := by
  rcases lt_or_ge θ 0 with h | h
  · have h' : -θ ∈ Work.Spaces.Iθ := by
      rw [abs_of_neg h] at hθ
      exact ⟨by linarith, hθ⟩
    rw [profile_of_neg (not_le.mpr h), abs_neg, abs_of_neg h, ← profile_of_nonneg h'.1]
    exact profile_abs_le hp hp1 hg z hz (-θ) h'
  · rw [abs_of_nonneg h] at hθ ⊢
    exact profile_abs_le hp hp1 hg z hz θ ⟨h, hθ⟩

/-! ## The `L^∞` bound of the self-similar vorticity -/

/-- **`‖omegaS p g x‖ ≤ M`**: the profile bound times `‖e_θ‖ ≤ 1`, using that
`|Work.Cyl.theta x| ∈ [0,π/2]` and the bound `M` of the profile. -/
theorem omegaS_norm_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ} {Cg M : ℝ}
    (hg : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg) (hCg : 0 ≤ Cg)
    (hM : ∀ θ ∈ Work.Spaces.Iθ, 20 * p * Gamma (p / 3) θ + Cg ≤ M) (x : R3) :
    ‖omegaS p g x‖ ≤ M := by
  rw [omegaS_apply', norm_smul, Real.norm_eq_abs]
  have hθ_abs : |Work.Cyl.theta x| ≤ Real.pi / 2 := by
    rw [abs_le]
    exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _),
      le_of_lt (Real.arctan_lt_pi_div_two _)⟩
  have hθmem : |Work.Cyl.theta x| ∈ Work.Spaces.Iθ := ⟨abs_nonneg _, hθ_abs⟩
  have hbdd := profile_abs_le_of_abs (p := p) hp hp1 hg (Work.Cyl.rho x ^ p)
    (Real.rpow_nonneg (Real.sqrt_nonneg _) p) (Work.Cyl.theta x) hθ_abs
  have hnn : 0 ≤ 20 * p * Gamma (p / 3) |Work.Cyl.theta x| + Cg :=
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hp.le) (Gamma_nonneg hθmem)) hCg
  calc |profile p g (Work.Cyl.rho x ^ p) (Work.Cyl.theta x)| * ‖Work.Cyl.eTheta x‖
      ≤ (20 * p * Gamma (p / 3) |Work.Cyl.theta x| + Cg) * 1 :=
        mul_le_mul hbdd (norm_eTheta_le_one x) (norm_nonneg _) hnn
    _ ≤ M := by
        have := hM _ hθmem
        linarith

/-! ## The pure `F_*` field is a multiple of the model field -/

/-- **`omegaS p 0 = (p/c(p)) • omegaStar (p/3)`**: with `g = 0` the self-similar vorticity is
exactly the model field of `Defs.omegaStar` (the `ρ^{3β}`-field, `β = p/3`) times the constant
`p/c(p)`.  Consequently every Hölder statement about the model field transfers to the pure `F_*`
part of the construction, and every failure of regularity of the model field transfers to it as
well (`Refute.lean`). -/
theorem omegaS_zero_eq_of_theta_nonneg (p : ℝ) {x : R3} (hθ : 0 ≤ Work.Cyl.theta x) :
    omegaS p (fun _ _ => 0) x = (p / Work.Spaces.c p) • omegaStar (p / 3) x := by
  have hval : Work.Construction.Fstar p (Work.Cyl.rho x ^ p) (Work.Cyl.theta x)
      = p / Work.Spaces.c p * (Gamma (p / 3) (Work.Cyl.theta x)
          * Work.FM.Fstar (Work.Cyl.rho x ^ (3 * (p / 3)))) := by
    rw [Work.Construction.Fstar, Gamma_div_three, ← Gamma_div_three (p := p)]
    ring
  rw [omegaS_apply', profile_of_nonneg hθ, add_zero, omegaStar_apply, smul_smul, ← hval]

/-- `θ(x) ≥ 0` on the closed half space `x₃ ≥ 0`. -/
theorem theta_nonneg_of_axial_nonneg {x : R3} (hx : 0 ≤ x 2) : 0 ≤ Work.Cyl.theta x := by
  rw [Work.Cyl.theta, Real.arctan_nonneg, Work.Cyl.axial]
  exact div_nonneg hx (Real.sqrt_nonneg _)

/-- **`omegaS p 0 = (p/c(p)) • omegaStar (p/3)` on the closed half space `x₃ ≥ 0`**: with `g = 0`
the self-similar vorticity is exactly the model field of `Defs.omegaStar` (the `ρ^{3β}`-field,
`β = p/3`) times the constant `p/c(p)`.  (Away from that half space the profile's odd extension
differs from `Γ` by the constant `cos((p/3)π)`, since `Real.rpow` evaluates a negative base through
`cos`; the model statement `holder_omegaStar` is therefore the half-space model of the pure `F_*`
part.) -/
theorem omegaS_zero_eq_of_axial_nonneg (p : ℝ) {x : R3} (hx : 0 ≤ x 2) :
    omegaS p (fun _ _ => 0) x = (p / Work.Spaces.c p) • omegaStar (p / 3) x :=
  omegaS_zero_eq_of_theta_nonneg p (theta_nonneg_of_axial_nonneg hx)

end Work.ConstructionInstance
