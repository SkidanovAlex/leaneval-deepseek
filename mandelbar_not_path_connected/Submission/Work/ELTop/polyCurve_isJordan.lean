/-
# The ray polygon is a Jordan curve

`Work.EL.polyCurve ps R`, the boundary of the ray polygon of an admissible list of co-landing
pairs `ps` at level `R`, is the image of the circle under the parametrization
`Work.ELTop.cycParam D R`, where `D` is the cyclic lift of the angle data of `ps`: the blocks
`k = 0, -1, …, 1-m` run through the ray pieces (up along `A k`, down along `B (k-1)`) and the
equipotential arcs at level `R` over the near arcs `[B (k-1), A k]`.

The parametrization is continuous and `1`-periodic, and it is injective on the fundamental
domain `[0,1)` because the blocks are simple and pairwise disjoint (the congruence argument in
the window `[B 0 - 1, A 0]` of length `< 1`).  Hence, by
`isJordanCurve_range_liftIco`, the polygon is a Jordan curve.
-/
import Mathlib
import Submission.Work.ELTop.PolyCurve.Defs
import Submission.Work.ELTop.PolyCurve.Blocks
import Submission.Work.ELTop.PolyCurve.Cont
import Submission.Work.ELTop.PolyCurve.Inject
import Submission.Work.ELTop.PolyCurve.MatchesLemmas
import Submission.Work.ELTop.isJordanCurve_range_liftIco
import Submission.Work.ELTop.PolyCurve.exists_cycLift
import Submission.Work.ELTop.PolyCurve.image_cycParam

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.ELTop

theorem polyCurve_isJordan {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps) {R : ℝ} (hR : 1 < R) :
    Work.Top.IsJordanCurve (Work.EL.polyCurve ps R) := by
  obtain ⟨D, hM⟩ := PolyCurve.exists_cycLift hN ps hA
  have hL : ∀ k : ℤ, Work.EL.LandsN hN (D.A k) (D.Y k) ∧
      Work.EL.LandsN hN (D.B k) (D.Y k) := by
    intro k
    obtain ⟨i, q, hAk, hBk, hYk⟩ := hM.exists_of_mem k
    constructor
    · rw [hAk, hYk]
      exact LandsN_add_int hN (ps.get i).lands_a q
    · rw [hBk, hYk]
      exact LandsN_add_int hN (ps.get i).lands_b q
  have hJ : Work.Top.IsJordanCurve (cycParam D R '' Set.Ico 0 1) := by
    simpa using (isJordanCurve_range_liftIco (F := cycParam D R) (a := 0)
      (by simpa using D.cycParam_add_one hR 0)
      (by simpa using D.continuousOn_cycParam hR hL)
      (by simpa using D.injOn_cycParam hR))
  rw [PolyCurve.image_cycParam D ps hM hR] at hJ
  exact hJ

end Work.ELTop
