/-
Copyright: work module for the Elgindi finite-time singularity project.

# Definitions and the pointwise identity of Step 3 of the honest level-`0` estimate

Shared vocabulary of `Submission/Work/FTS/EllipticEst/Honest/step3Angle.lean` and of the
delegated pieces `Honest.step3PsiBar`, `Honest.step3PMem`:

* `uOf Ψ = ∂_θ(tan θ · Ψ)` — the angular term of Step 3;
* `POf Ψ = sin θ · ∂_θ(Ψ/cos θ)` — the `I₄`-quantity;
* `GOf Ψ = z ∂_z Ψ`, `AOf Ψ = z² ∂_zzΨ` — the first and second order radial quantities.

The pointwise identity `uOf Ψ = Ψ + POf Ψ` on the open quadrant is `pth_tan_mul_eq_open`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.Honest.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The angular term `u = ∂_θ(tan θ · Ψ)` of Step 3. -/
def uOf (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ)

/-- The `I₄`-quantity `P = sin θ · ∂_θ(Ψ/cos θ)` whose norm the positivity `I_{4,2}` controls. -/
def POf (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ

/-- The first-order radial quantity `G = z ∂_z Ψ`. -/
def GOf (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz Ψ z θ

/-- The second-order radial quantity `A = z² ∂_zzΨ`. -/
def AOf (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ

/-! ## The pointwise identity `u = Ψ + P` on the open quadrant -/

/-- **The pointwise identity.**  If the `θ`-slice of `Ψ` at `z` is differentiable at `θ` and
`cos θ ≠ 0`, then

  `∂_θ(tan θ · Ψ) = Ψ + sin θ · ∂_θ(Ψ/cos θ)`,

because `tan θ · Ψ = sin θ · (Ψ / cos θ)` and `∂_θ(sin θ · Ψ̄) = cos θ · Ψ̄ + sin θ · Ψ̄'`
with `cos θ · (Ψ/cos θ) = Ψ`. -/
theorem pth_tan_mul_eq_of_diff {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ} (hc : Real.cos θ ≠ 0)
    (hdΨ : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ) :
    Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
      = Ψ z θ + Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ := by
  have htan : HasDerivAt Real.tan (1 / Real.cos θ ^ 2) θ := Real.hasDerivAt_tan hc
  have hmul := htan.mul hdΨ.hasDerivAt
  have hdiv := hdΨ.hasDerivAt.div (Real.hasDerivAt_cos θ) hc
  have hfuneq : (Real.tan * fun θ' => Ψ z θ') = (fun θ' => Real.tan θ' * Ψ z θ') := rfl
  have hdmul : deriv (fun θ' => Real.tan θ' * Ψ z θ') θ
      = 1 / Real.cos θ ^ 2 * Ψ z θ + Real.tan θ * deriv (fun θ' => Ψ z θ') θ := by
    rw [← hfuneq]; exact hmul.deriv
  have hddiv : deriv (fun θ' => Ψ z θ' / Real.cos θ') θ
      = (deriv (fun θ' => Ψ z θ') θ * Real.cos θ - Ψ z θ * (-Real.sin θ))
        / Real.cos θ ^ 2 := hdiv.deriv
  simp only [Work.Spaces.pth]
  rw [hdmul, hddiv, Real.tan_eq_sin_div_cos]
  have hs : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  field_simp
  ring_nf
  linear_combination (-(Ψ z θ)) * hs

/-- The same identity for a function `C^∞` on the open quadrant, in the hypothesis shape of
`Hon`. -/
theorem pth_tan_mul_eq_open {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
      = Ψ z θ + Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ := by
  have hmem : (z, θ) ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)) := ⟨hz, hθ0, hθ1⟩
  have hopen : IsOpen (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hdiff : DifferentiableAt ℝ (Function.uncurry Ψ) (z, θ) :=
    ((hsm 1).contDiffAt (hopen.mem_nhds hmem)).differentiableAt (by norm_num)
  refine pth_tan_mul_eq_of_diff ?_ ?_
  · exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  · exact Work.Spaces.differentiableAt_curry_right hdiff

end Work.FTS.EllipticEst.Honest
