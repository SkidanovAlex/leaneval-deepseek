/-
Copyright: work module for the Elgindi finite-time singularity project.

# Operators and smoothness classes for the mixed Leibniz rule

This file collects the definitions used to prove the two-operator (Leibniz)
rule for `D_z^j D_θ^i`:

* `quadU`, the open quadrant `(-1,∞) × (0,π/2)` on which `SmoothInt` functions
  are `C^∞`;
* `SmoothU`, the class of uncurried functions `C^∞` on `quadU`;
* `Zb`, `Tb`, the operators `D_z`, `D_θ` acting on uncurried functions;
* `SmoothZ`, the class of functions of `z` alone `C^∞` on `(-1,∞)`, and
  `Zop`, the one-dimensional operator `z ↦ z·u'(z)`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.DerivLikeDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.Spaces

/-- The open quadrant `(-1,∞) × (0,π/2)`. -/
def quadU : Set (ℝ × ℝ) := Set.Ioi (-1) ×ˢ Set.Ioo 0 (π/2)

lemma isOpen_quadU : IsOpen quadU := isOpen_Ioi.prod isOpen_Ioo

/-- The class of uncurried functions which are `C^∞` on the open quadrant. -/
def SmoothU (F : ℝ × ℝ → ℝ) : Prop := ContDiffOn ℝ ⊤ F quadU

/-- The class of functions of one variable `C^∞` on `(-1,∞)`. -/
def SmoothZ (u : ℝ → ℝ) : Prop := ContDiffOn ℝ ⊤ u (Set.Ioi (-1))

/-- The operator `D_z` acting on uncurried functions. -/
def Zb (F : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => p.1 * deriv (fun z' => F (z', p.2)) p.1

/-- The operator `D_θ` acting on uncurried functions. -/
def Tb (F : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => Real.sin (2 * p.2) * deriv (fun θ' => F (p.1, θ')) p.2

/-- The one-dimensional operator `z ↦ z·u'(z)` underlying `D_z`. -/
def Zop (u : ℝ → ℝ) : ℝ → ℝ := fun z => z * deriv u z

theorem SmoothU_FunClass : FunClass (X := ℝ × ℝ) SmoothU where
  add := fun A B hA hB => hA.add hB
  mul := fun A B hA hB => hA.mul hB
  smul := fun c A hA => by
    show ContDiffOn ℝ ⊤ (fun p => c * A p) quadU
    exact ContDiffOn.const_smul c hA

theorem SmoothZ_FunClass : FunClass (X := ℝ) SmoothZ where
  add := fun A B hA hB => hA.add hB
  mul := fun A B hA hB => hA.mul hB
  smul := fun c A hA => by
    show ContDiffOn ℝ ⊤ (fun p => c * A p) (Set.Ioi (-1))
    exact ContDiffOn.const_smul c hA

end Work.Spaces
