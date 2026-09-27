import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.levYcFormula

/-!
# Vocabulary for `Work.Mostow.cuspHoroballsMargulis`

The Margulis cusp construction measures, at each parabolic fixed point `ξ`, how far a parabolic
element `γ` of the stabiliser displaces the *flat* horosphere at `ξ`:

* `flatDisp ξ γ` is the infimum of the flat displacements `‖yc ξ u - yc ξ (γ • u)‖` over `u`;
* `muInf Γ ξ` is the infimum of `flatDisp ξ γ` over the parabolic `γ ∈ Γ` fixing `ξ`;
* `htEps Γ ε ξ` is the horoball level `log (cEps ε) - log (muInf Γ ξ)`, where
  `cEps ε = √(2 (cosh ε - 1))` is the reciprocity constant of the Margulis construction.

The horoball `horoball ξ (htEps Γ ε ξ)` then contains every point moved by less than `ε` by a
parabolic element of `Γ` fixing `ξ`, and for `ε` below a Margulis threshold the horoballs at the
parabolic fixed points `parFixed Γ` are pairwise disjoint.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- The set of flat displacements of `u` under `γ`, measured in the `yc`-coordinates at `ξ`. -/
def flatDispSet (ξ : E n) (γ : PO n 1) : Set ℝ :=
  Set.range (fun u : E n => ‖yc ξ u - yc ξ (γ • u)‖)

/-- The infimum of the flat displacement of `γ` along the horospheres at `ξ`. -/
def flatDisp (ξ : E n) (γ : PO n 1) : ℝ := sInf (flatDispSet ξ γ)

/-- The infimum of `flatDisp ξ γ` over parabolic `γ ∈ Γ` fixing `ξ`. -/
def muInf (Γ : Subgroup (PO n 1)) (ξ : E n) : ℝ :=
  sInf { r : ℝ |
    ∃ (γ : Γ), IsParabolic (γ : PO n 1) ∧ bd (γ : PO n 1) ξ = ξ ∧
      flatDisp ξ (γ : PO n 1) = r }

/-- The reciprocity constant `√(2 (cosh ε - 1))`. -/
def cEps (ε : ℝ) : ℝ := Real.sqrt (2 * (Real.cosh ε - 1))

/-- The horoball height of the Margulis cusp construction at `ξ`. -/
def htEps (Γ : Subgroup (PO n 1)) (ε : ℝ) (ξ : E n) : ℝ :=
  Real.log (cEps ε) - Real.log (muInf Γ ξ)

end

end Work.Mostow
