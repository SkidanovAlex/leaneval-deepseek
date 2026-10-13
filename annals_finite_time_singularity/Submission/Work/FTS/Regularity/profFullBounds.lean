/-
# `Work.FTS.Regularity.profFullBounds` — the uniform `L^∞` bound of the full profile

The full self-similar profile of the route is `F = F_* + g` (`profFull`), with
`F_*(z,θ) = α(Γ(θ)/c)·2z/(1+z)²` the paper's stationary profile and `g = F - F_*` the
modulation.  The regularity package `RegPkg` bounds the perturbation,
`|g z θ τ| ≤ Cv` (`RegPkg.abs_le_Cv`, from the angular vanishing `|g| ≤ Cv·Γ(θ)` and
`Γ ≤ 1`), and the explicit profile bound `|F_*| ≤ 20p·Γ(p/3)` of
`Work.ConstructionInstance.Fstar_abs_le` bounds the stationary part; since `Γ ≤ 1` on
`Iθ`, the sum is bounded by `20·(3α) + Cv` uniformly on the whole strip.

This is the `L^∞` input of the physical transfer: the profile bound is what makes the
weighted norms (`HkNorm`, `WlInf`) of the reconstruction honest, and (together with the
compact support `hsupp`) it is what keeps the physical vorticity in `L^∞`.
-/
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.FTS.Regularity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Regularity

/-- **The uniform bound of the full profile `F = F_* + g`.**  For every regularity package
`RegPkg α S A B g` there is a constant `M ≥ 0` with `|F(z,θ,τ)| ≤ M` for all `τ ∈ [0,S]`,
`z ≥ 0` and `θ ∈ Iθ`.  Since `pExp α = 3α ≤ 1` and `Γ ≤ 1` on `Iθ`, the explicit choice
`M = 20·(3α) + Cv` works, where `Cv` is the `L^∞` bound of `g` extracted from the angular
vanishing datum. -/
theorem profFullBounds {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg α S A B g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |profFull α g z θ τ| ≤ M := by
  obtain ⟨Cv, hCv0, hCv⟩ := h.abs_le_Cv
  have hp : 0 < pExp α := h.pExp_pos
  have hp1 : pExp α ≤ 1 := h.pExp_le_one
  refine ⟨20 * pExp α + Cv, by positivity, fun τ hτ z θ hz hθ => ?_⟩
  have hGam1 : Gamma (pExp α / 3) θ ≤ 1 :=
    Work.ConstructionInstance.Gamma_le_one (by positivity) hθ
  have hF := Work.ConstructionInstance.Fstar_abs_le hp hp1 hz hθ
  have hG := hCv τ hτ z θ hz hθ
  rw [profFull_apply]
  calc |Work.Construction.Fstar (pExp α) z θ + g z θ τ|
      ≤ |Work.Construction.Fstar (pExp α) z θ| + |g z θ τ| := abs_add_le _ _
    _ ≤ 20 * pExp α * Gamma (pExp α / 3) θ + Cv := add_le_add hF hG
    _ ≤ 20 * pExp α + Cv := by
        have h1 : 20 * pExp α * Gamma (pExp α / 3) θ ≤ 20 * pExp α := by
          simpa using mul_le_mul_of_nonneg_left hGam1 (show (0 : ℝ) ≤ 20 * pExp α by positivity)
        linarith

end Work.FTS.Regularity
