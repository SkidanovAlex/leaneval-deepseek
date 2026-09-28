import Mathlib
import Submission.Work.Stems.wangOddStepSphere
import Submission.Work.Stems.isHurewiczFibration_homotopyFibreFst
import Submission.Work.Stems.fibreOfHomeomorphLoopSpace
import Submission.Work.Stems.product_ratH_vanishing

/-!
# The odd step of the `C2` layer for the cover of a sphere

`Work.Stems.isZero_ratH_sphereFibration'` (`Submission/Work/Stems/wangOddStepSphere.lean`) gives the
vanishing of the total space of a Hurewicz fibration `p : E → Sᵇ` from the vanishing of its fibre,
with the two fibrewise trivialities discharged by contractibility.  This file instantiates it at the
fibration of the `C2` odd step: for a map `g : Sᵇ → Z`, the projection

  `Work.RatHurewicz.homotopyFibreFst g ∞ : homotopyFibre g ∞ → Sᵇ`

of the homotopy fibre of `g` (a Hurewicz fibration by
`Work.Stems.isHurewiczFibration_homotopyFibreFst`) has fibre over `∞` the *loop space*
`Path (g ∞) (g ∞)` (`Work.Stems.fibreOfHomeomorphLoopSpace`).  So:

> if `ΩZ` has vanishing rational homology in degrees `0 < t ≤ T`, `t ≠ b-1`, then the homotopy fibre
> of `g` has vanishing rational homology in degrees `b+1 ≤ t ≤ min T (2b-2)`.

For the odd step of `C2` one takes `g` to be the **bottom cell** `Sᵇ → K(ℤ,b)` (so that
`homotopyFibre g ∞` is the `b`-connected cover of `Sᵇ`, and `ΩZ ≅ K(ℤ,b-1)` is a rational sphere
below `2b-3` by the *even* step of `C2`), and concludes that the cover is rationally acyclic in the
range; `Work.Serre.SerreE3a` then makes `K(ℤ,b)` a rational sphere, i.e. closes the odd step.  See
`Submission/Work/Stems/C2ODD_PLAN.md` (§3 records the one remaining input, the multiplicativity of
the Wang transgression beyond the range of the exactness argument).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Stems

noncomputable section

/-- **The Wang odd step for the homotopy fibre of a map into a space with a loop-space fibre.** -/
theorem isZero_ratH_homotopyFibre {b : ℕ} (hb : 2 ≤ b) {Z : Type} [TopologicalSpace Z]
    (g : C(Work.StemsB.SphModel b, Z)) (T : ℕ)
    (hfib : ∀ t : ℕ, 0 < t → t ≤ T → t ≠ b - 1 →
      Subsingleton ↥(Work.Serre.ratH (TopCat.of (Path (g OnePoint.infty) (g OnePoint.infty))) t)) :
    ∀ t : ℕ, b + 1 ≤ t → t ≤ T → t ≤ 2 * b - 2 →
      Subsingleton ↥(Work.Serre.ratH
        (TopCat.of (Work.RatHurewicz.homotopyFibre g OnePoint.infty)) t) := by
  -- the fibre of the projection is the loop space
  have hfib' : ∀ t : ℕ, 0 < t → t ≤ T → t ≠ b - 1 →
      Subsingleton ↥(Work.Serre.ratH
        (Work.StemsB.wangCohFsp b (Work.RatHurewicz.homotopyFibreFst g OnePoint.infty)) t) := by
    intro t h1 h2 h3
    obtain ⟨e⟩ := Work.Stems.fibreOfHomeomorphLoopSpace g OnePoint.infty
    have h := Work.Stems.isZero_ratH_of_homeomorph e t
      (ModuleCat.isZero_iff_subsingleton.mpr (hfib t h1 h2 h3))
    exact ModuleCat.isZero_iff_subsingleton.mp h
  exact Work.Stems.isZero_ratH_sphereFibration' b hb
    (Work.RatHurewicz.homotopyFibre g OnePoint.infty)
    (Work.RatHurewicz.homotopyFibreFst g OnePoint.infty)
    (Work.Stems.isHurewiczFibration_homotopyFibreFst g OnePoint.infty) T hfib'

end

end Work.Stems
