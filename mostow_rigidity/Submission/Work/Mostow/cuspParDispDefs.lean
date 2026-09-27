import Mathlib
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.cuspHoroDefs
import Submission.Work.Mostow.cuspThinRegionDefs

/-!
# The flat displacement of the parabolics of a cusp stabiliser

For `Γ ≤ PO(n,1)`, `ξ ∈ Sph n` and a flat coordinate `y ∈ E n` we collect here the two basic
notions of the Margulis cusp analysis:

* `parDisp Γ ξ y` — the infimum of the flat displacements `‖y - flatAct ξ γ y‖` over the
  *parabolic* elements `γ ∈ Γ` fixing `ξ`;
* `parShort Γ ξ r y` — the set of such elements whose flat displacement at `y` is `< r`.

The key relation (proved elsewhere, `cuspThinRegion_eq_parDisp`) is that the Margulis region
`cuspThinRegion Γ ξ ε` is the set of points whose horospherical level times `parDisp` is below the
constant `cEps ε`; hence a *horoball* at `ξ` lies inside the Margulis region as soon as `parDisp`
is bounded on the flat space.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

variable {n : ℕ}

/-- The infimum of the flat displacements at `y` of the parabolic elements of `Γ` which fix `ξ`. -/
noncomputable def parDisp (Γ : Subgroup (PO n 1)) (ξ y : E n) : ℝ :=
  sInf {r : ℝ | ∃ γ : Γ, IsParabolic (γ : PO n 1) ∧ bd (γ : PO n 1) ξ = ξ ∧
    r = ‖y - flatAct ξ (γ : PO n 1) y‖}

/-- The parabolic elements of `Γ` fixing `ξ` whose flat displacement at `y` is less than `r`. -/
def parShort (Γ : Subgroup (PO n 1)) (ξ : E n) (r : ℝ) (y : E n) : Set Γ :=
  {γ | IsParabolic (γ : PO n 1) ∧ bd (γ : PO n 1) ξ = ξ ∧
    ‖y - flatAct ξ (γ : PO n 1) y‖ < r}

@[simp] lemma mem_parShort {Γ : Subgroup (PO n 1)} {ξ y : E n} {r : ℝ} {γ : Γ} :
    γ ∈ parShort Γ ξ r y ↔ IsParabolic (γ : PO n 1) ∧ bd (γ : PO n 1) ξ = ξ ∧
      ‖y - flatAct ξ (γ : PO n 1) y‖ < r := Iff.rfl

end

end Work.Mostow
