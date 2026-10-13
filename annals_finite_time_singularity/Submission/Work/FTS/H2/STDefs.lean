/-
Copyright: work module for the Elgindi finite-time singularity project.

# Definitions for `SpecialTransport`

Elgindi's Proposition `SpecialTransport` (§`H2`, tex 1126) is the estimate

  `|(f ∂_θ g, g)_{ℋ⁴}| ≤ C/√(γ-1) |∂_θ f|_{𝒲^{4,∞}} |g|²_{ℋ⁴}`

for `∂_θ f ∈ 𝒲^{4,∞}` and `g ∈ ℋ⁴`, where `f` vanishes at the two angular boundaries.  Writing
`f ∂_θ g = h · D_θ g` with the multiplier `h = f / sin(2θ)`, the pairing integrand
`H4PairInt α (h D_θ g) g` splits into

* the "hard" part `T1Hard α h g`: the five order-`5` terms in which *all* derivatives fall on
  the `g`-block (these are handled by integration by parts in `θ`, exactly as in `Transport1`);
* the "easy" part `STEasy α f g`: everything else, in which at least one derivative falls on
  the bounded multiplier `h` and can therefore be estimated pointwise.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.H2.T1Defs
import Submission.Work.FTS.H2.STBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false

/-- The multiplier `h = f / sin(2θ)` of `SpecialTransport`. -/
def hsf (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => f z θ / Real.sin (2 * θ)

/-- The "easy" part of the `SpecialTransport` pairing integrand: everything except the five
order-five terms collected in `T1Hard α (hsf f) g`. -/
def STEasy (α : ℝ) (f g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => H4PairInt α (fun z θ => hsf f z θ * Spaces.Dth g z θ) g z θ
    - T1Hard α (hsf f) g z θ

/-- Pointwise, the pairing integrand is the sum of its easy and hard parts. -/
theorem H4PairInt_eq_STEasy_add_hard (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    H4PairInt α (fun z θ => hsf f z θ * Spaces.Dth g z θ) g z θ
      = STEasy α f g z θ + T1Hard α (hsf f) g z θ := by
  simp only [STEasy]
  ring

/-- Multiplication by `sin(2θ)` undoes the division defining `hsf`, on the closed angular
interval, for functions vanishing at the two angular boundaries. -/
theorem hsf_mul_sin {f : ℝ → ℝ → ℝ} (hvt : Spaces.VanishTheta f) {z θ : ℝ}
    (hθ : θ ∈ Spaces.Iθ) :
    hsf f z θ * Real.sin (2 * θ) = f z θ := by
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · rw [← h0]; simp [hsf, hvt.1 z]
  rcases eq_or_lt_of_le hθ.2 with h1 | h1
  · rw [h1]
    rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
    simp [hsf, hvt.2 z]
  · have hs : Real.sin (2 * θ) ≠ 0 := ne_of_gt (sin_two_pos_of_Ioo ⟨h0, h1⟩)
    show f z θ / Real.sin (2 * θ) * Real.sin (2 * θ) = f z θ
    field_simp

end Work.FTS.H2
