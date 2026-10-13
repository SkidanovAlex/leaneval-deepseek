import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXT.omega_facts
import Submission.Work.FTS_RegExport.RXT.logcoord_facts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! # `Work.FTS.RegExportIface.RXT.logcoord_facts` — leaf T5a (module `LeafAux.logcoord_facts`)

The leaf statement of `Submission/Work/FTS/RegExportIface/RXT/Leaves.lean`, **proved**.

This module deliberately does **not** import `Leaves` (which imports it), so the cycle is broken.
The proof is an assembly of two already-proved facts from the `Work.FTS_RegExport` mirror area,
both of which live in modules that do not depend on `Leaves`:

* `Work.FTS_RegExport.RXT.logcoord_facts` — the logarithmic angular coordinate `ψ ↦ arctan eᵝ`
  (range, derivative) and the existence of the coordinates `(s, ψ)` for `(z, θ)` in the open
  quadrant;
* `Work.FTS_RegExport.RXT.omega_facts` — positivity of `ω α z θ = z²Γ(α,θ)/(1+z)²` on the open
  quadrant and its two partial derivatives `∂_z ω = ω·2/(z(1+z))`,
  `∂_θ ω = ω·2α·c2m θ/sin 2θ`.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS.RegExportIface.RXT

set_option autoImplicit false
set_option linter.unusedVariables false

variable {α : ℝ}

theorem logcoord_facts (hα : 0 < α) :
    (∀ ψ : ℝ, 0 < Real.arctan (Real.exp ψ) ∧ Real.arctan (Real.exp ψ) < π / 2) ∧
    (∀ ψ : ℝ, HasDerivAt (fun ψ' => Real.arctan (Real.exp ψ'))
      (Real.sin (2 * Real.arctan (Real.exp ψ)) / 2) ψ) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → ∃ s ψ : ℝ, Real.exp s = z ∧ Real.arctan (Real.exp ψ) = θ) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → 0 < ω α z θ) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      HasDerivAt (fun z' => ω α z' θ) (ω α z θ * (2 / (z * (1 + z)))) z) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      HasDerivAt (fun θ' => ω α z θ') (ω α z θ * (2 * α * Work.Construction.c2m θ
        / Real.sin (2 * θ))) θ) := by
  obtain ⟨h1, _h2, h3, h4, h5, _h6, _h7⟩ := Work.FTS_RegExport.RXT.logcoord_facts
  obtain ⟨hw1, hw2, hw3⟩ := Work.FTS_RegExport.RXT.omega_facts α hα
  exact ⟨h1, h3, (fun z θ hz hθ hθ' => by
    obtain ⟨s, hs⟩ := h4 z hz
    obtain ⟨ψ, hψ⟩ := h5 θ hθ hθ'
    exact ⟨s, ψ, hs, hψ⟩), hw1, hw2, hw3⟩

end Work.FTS.RegExportIface.RXT
