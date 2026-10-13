/-
# Uniform boundedness of the physical vorticity of a `RegPkg` profile

The physical vorticity of the route is

  `physVort α A B g x τ = A(τ)⁻¹ • F(ρ(x)^{3α}/B(τ), θ(x), τ) • e_θ(x)`,

with `F = F_* + g` the full self-similar profile.  This module proves that it is *uniformly
bounded* on the strip `τ ∈ [0,S]` and all of `ℝ³`: the clock `A` is bounded away from `0`
(`hAb`), the perturbation `g` is bounded (`Jet`, `hg`), and the leading profile `F_*` is bounded
by `20·(3α)·Γ(θ) ≤ 20·(3α)` (`Work.ConstructionInstance.Fstar_abs_le` and `Γ ≤ 1`).  The
azimuthal field `e_θ` is a unit vector (and `0` on the axis), so nothing else is needed — in
particular the compact support of the profile is *not* used here.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.Regularity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set

namespace Work.FTS.Regularity

/-- The azimuthal vector field `e_θ` is a unit vector, and `0` on the axis (`radial x = 0`). -/
theorem norm_eTheta_le_one (x : R3) : ‖Work.Cyl.eTheta x‖ ≤ 1 := by
  by_cases h : Work.Cyl.radial x = 0
  · simp [Work.Cyl.eTheta, h]
  · rw [Work.Cyl.norm_eTheta x h]

/-- The polar angle `θ(x) = arctan(x₃/r)` satisfies `|θ(x)| ∈ [0,π/2]`. -/
theorem abs_theta_mem_Iθ (y : R3) : |Work.Cyl.theta y| ∈ Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ, Set.mem_Icc]
  have h := Real.arctan_mem_Ioo (Work.Cyl.axial y / Work.Cyl.radial y)
  rw [Work.Cyl.theta]
  exact ⟨abs_nonneg _, le_of_lt (abs_lt.mpr ⟨h.1, h.2⟩)⟩

/-- **Pointwise bound of the self-similar profile.**  For `z ≥ 0`, `|θ| ∈ Iθ` and `τ` in the
strip, `|F(z,θ,τ)| ≤ 20·(3α) + N`, where `N` bounds the perturbation `g`. -/
theorem abs_profile_le {α S N : ℝ} {g : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hN : ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S → |g z θ τ| ≤ N)
    {z θ τ : ℝ} (hz : 0 ≤ z) (hθ : |θ| ∈ Work.Spaces.Iθ) (hτ : τ ∈ Set.Icc 0 S) :
    |Work.ConstructionInstance.profile (pExp α) (gSlice g τ) z θ| ≤ 20 * pExp α + N := by
  have hp : 0 < pExp α := pExp_pos hα
  have hp1 : pExp α ≤ 1 := pExp_le_one hα13
  have key : ∀ θ' ∈ Work.Spaces.Iθ,
      |Work.Construction.Fstar (pExp α) z θ' + g z θ' τ| ≤ 20 * pExp α + N := by
    intro θ' hθ'
    have h1 := Work.ConstructionInstance.Fstar_abs_le hp hp1 hz hθ'
    have hp3 : 0 ≤ pExp α / 3 := (div_pos hp (by norm_num)).le
    have hG1 := Work.ConstructionInstance.Gamma_le_one (β := pExp α / 3) hp3 hθ'
    have hG0 := Work.ConstructionInstance.Gamma_nonneg (β := pExp α / 3) hθ'
    have h2 : 20 * pExp α * Work.ConstructionInstance.Gamma (pExp α / 3) θ'
        ≤ 20 * pExp α := by nlinarith
    have h3 := hN z θ' τ hz hθ' hτ
    calc |Work.Construction.Fstar (pExp α) z θ' + g z θ' τ|
        ≤ |Work.Construction.Fstar (pExp α) z θ'| + |g z θ' τ| := abs_add_le _ _
      _ ≤ 20 * pExp α + N := add_le_add (le_trans h1 h2) h3
  rw [Work.ConstructionInstance.profile]
  split_ifs with h
  · exact key θ (by simpa [abs_of_nonneg h] using hθ)
  · rw [abs_neg]
    exact key (-θ) (by simpa [abs_of_neg (not_le.mp h)] using hθ)

/-- **THE PHYSICAL VORTICITY IS UNIFORMLY BOUNDED ON THE STRIP.** -/
theorem physVort_bound {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.Regularity.RegPkg α S A B g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ y : Work.FTS.Regularity.R3,
      ‖Work.FTS.Regularity.physVort α A B g y τ‖ ≤ M := by
  obtain ⟨a₀, a₁, ha₀, hA⟩ := h.hAb
  obtain ⟨N, hN⟩ := h.hg
  have hN0 : 0 ≤ N := hN.1
  have hpN : 0 ≤ 20 * pExp α + N := by
    have hp := pExp_pos h.hα
    linarith
  refine ⟨(1 / a₀) * (20 * pExp α + N), by positivity, fun τ hτ y => ?_⟩
  have hAτ : 0 < A τ := h.hA τ hτ
  have hBτ : 0 < B τ := h.hB τ hτ
  have hz0 : 0 ≤ Work.Cyl.rho y ^ pExp α / B τ :=
    div_nonneg (Real.rpow_nonneg (Work.Cyl.rho_nonneg y) _) hBτ.le
  have hprof := abs_profile_le h.hα h.hα13
    (fun z θ σ hz hθ hσ => hN.abs_le hz hθ hσ) hz0 (abs_theta_mem_Iθ y) hτ
  have hAinv : |(A τ)⁻¹| ≤ 1 / a₀ := by
    rw [abs_of_pos (inv_pos.mpr hAτ), one_div]
    exact (inv_le_inv₀ hAτ ha₀).mpr (hA τ hτ).1
  have he : ‖Work.Cyl.eTheta y‖ ≤ 1 := norm_eTheta_le_one y
  have hinner : |Work.ConstructionInstance.profile (pExp α) (gSlice g τ)
        (Work.Cyl.rho y ^ pExp α / B τ) (Work.Cyl.theta y)| * ‖Work.Cyl.eTheta y‖
      ≤ 20 * pExp α + N := by
    calc |Work.ConstructionInstance.profile (pExp α) (gSlice g τ)
          (Work.Cyl.rho y ^ pExp α / B τ) (Work.Cyl.theta y)| * ‖Work.Cyl.eTheta y‖
        ≤ (20 * pExp α + N) * 1 :=
          mul_le_mul hprof he (norm_nonneg _) hpN
      _ = 20 * pExp α + N := mul_one _
  calc ‖Work.FTS.Regularity.physVort α A B g y τ‖
      = ‖(A τ)⁻¹ • (Work.ConstructionInstance.profile (pExp α) (gSlice g τ)
            (Work.Cyl.rho y ^ pExp α / B τ) (Work.Cyl.theta y) • Work.Cyl.eTheta y)‖ := by
        rw [physVort_apply, Work.ConstructionInstance.omegaSz_apply]
    _ = |(A τ)⁻¹| * (|Work.ConstructionInstance.profile (pExp α) (gSlice g τ)
            (Work.Cyl.rho y ^ pExp α / B τ) (Work.Cyl.theta y)| * ‖Work.Cyl.eTheta y‖) := by
        simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ (1 / a₀) * (20 * pExp α + N) :=
        mul_le_mul hAinv hinner (by positivity) (by positivity)

end Work.FTS.Regularity
