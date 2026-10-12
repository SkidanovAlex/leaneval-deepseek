import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Submission.Work.BoseBoxFock.L1Tails.chiBasicFacts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The derivative of `χ_ℓ · G(·, y)` vanishes outside the half-ball

The corpus window `χ_ℓ = chiC ℓ` is supported in the open ball of radius `ℓ/2`
(`chiScale_ne_zero_iff`, `chiScale_eq_zero_of_half_le_norm` in `chiBasicFacts`), so
`w' ↦ χ_ℓ w' · G w' y` vanishes identically on the closed exterior of that ball.  This module
proves that its Fréchet derivative at every point of that exterior is `0`.

The two geometric regimes are handled separately:

* `‖w‖ > ℓ/2`: the complement of the *closed* ball is open, so the function is locally the constant
  `0` near `w` and its derivative vanishes by local constancy;
* `‖w‖ = ℓ/2`: the function is differentiable and vanishes on the closed exterior, and a smooth
  function vanishing on the exterior of a ball has vanishing derivative at the boundary — the
  exterior half-space `{v | 0 ≤ ⟪w, v⟫}` spans the whole space and along it the difference
  quotient vanishes identically (proved in `chiBasicFacts` as `fderiv_eq_zero_of_norm_eq`).

The general statement of the two regimes is factored out as `fderiv_eq_zero_of_le_norm`.
-/

noncomputable section

open Filter
open scoped Topology ContDiff

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- **A function vanishing on the closed exterior of a ball has vanishing derivative there.**
If `f x = 0` for every `x` with `R ≤ ‖x‖` and `f` is differentiable at a point `x₀` with
`R ≤ ‖x₀‖`, then `fderiv ℝ f x₀ = 0`.

(This combines the boundary case `‖x₀‖ = R` — flatness of the zero extension, proved in
`chiBasicFacts` as `fderiv_eq_zero_of_norm_eq` — with the strict case `R < ‖x₀‖`, where `f` is
locally constant `0` because `{x | R < ‖x‖}` is an open neighbourhood of `x₀`.) -/
theorem fderiv_eq_zero_of_le_norm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} {x₀ : E3} {f : E3 → F}
    (hd : DifferentiableAt ℝ f x₀) (hx : R ≤ ‖x₀‖)
    (hzero : ∀ x, R ≤ ‖x‖ → f x = 0) : fderiv ℝ f x₀ = 0 := by
  rcases lt_or_eq_of_le hx with hlt | heq
  · -- strictly outside the closed ball: `f` is locally `0`
    have hev : f =ᶠ[nhds x₀] Function.const _ (0 : F) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hlt] with z hz
      exact hzero z hz.le
    simpa using Filter.EventuallyEq.fderiv_eq hev
  · -- on the boundary sphere: flatness of the zero extension
    exact fderiv_eq_zero_of_norm_eq heq.symm hd hzero

/-- **The target.**  The map `w' ↦ χ_ℓ(w') · G(w', y)` has zero Fréchet derivative at every point
of the closed exterior of the ball of radius `ℓ/2`. -/
theorem fderiv_chiC_mul_eq_zero_of_half_le_norm {ℓ : ℝ} (hℓ : 0 < ℓ)
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G))
    {w y : EuclideanSpace ℝ (Fin 3)} (hw : ℓ / 2 ≤ ‖w‖) :
    fderiv ℝ (fun w' => Work.BoseBoxFock.L1Tails.chiC ℓ w' * G w' y) w = 0 := by
  -- the section `w' ↦ G w' y` of the smooth kernel is smooth
  have hsec : ContDiff ℝ (⊤ : ℕ∞) (fun w' : E3 => G w' y) :=
    hG.comp (contDiff_id.prodMk contDiff_const)
  -- hence the product is differentiable at `w`
  have hd : DifferentiableAt ℝ (fun w' => Work.BoseBoxFock.L1Tails.chiC ℓ w' * G w' y) w :=
    ((contDiff_chiC ℓ).mul hsec).differentiable (by simp) |>.differentiableAt
  -- and it vanishes on the closed exterior of the ball of radius `ℓ/2`
  have hzero : ∀ x : E3, ℓ / 2 ≤ ‖x‖ → chiC ℓ x * G x y = 0 := by
    intro x hx
    have h1 : Submission.BoseGases.chiScale ℓ x = 0 := chiScale_eq_zero_of_half_le_norm hℓ hx
    simp only [chiC, h1, Complex.ofReal_zero, zero_mul]
  exact fderiv_eq_zero_of_le_norm (F := ℂ) hd hw hzero

end Work.BoseBoxFock.L1Tails
