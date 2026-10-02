/-
# T2′ in the exact form of the contract, and for two boundary pairs

`Work.ELTop.polyRegion_eq_inter_pairSideNear` is the equality
`polyRegion ps R = ⋂_{P ∈ ps} pairSideNear P ∩ {pot hN · < log R}` under the extra (but
automatic) hypothesis that no pair of the polygon has congruent angles.  This file removes that
hypothesis (`polyRegion_eq_iInter_pairSideNear`, using
`Work.ELTop.arcLen_ne_zero_of_polyAdmissible`) and records the two-pair form used by the nests
(`polyRegion_pair_eq_pairSideNear_inter`).
-/
import Submission.Work.ELTop.polyRegion_eq_inter_pairSideNear
import Submission.Work.ELTop.arcLen_ne_zero_of_polyAdmissible

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELTop

/-- **T2′ of the contract**, with exactly the contract's hypotheses: the region of a ray polygon
is the intersection of the near sides of its pairs with the sublevel set of the potential. -/
theorem polyRegion_eq_iInter_pairSideNear {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps)
    {R : ℝ} (hR : 1 < R) (hC : Work.Top.IsJordanCurve (Work.EL.polyCurve ps R)) :
    Work.EL.polyRegion ps R =
      ({z : ℂ | ∀ P ∈ ps, z ∈ Work.EL.pairSideNear P} ∩
        {z : ℂ | Work.EL.pot hN z < Real.log R}) :=
  polyRegion_eq_inter_pairSideNear hN hJ ps hA
    (fun P hP => by
      obtain ⟨h1, -, h3⟩ := arcLen_ne_zero_of_polyAdmissible hA P hP
      rw [h3]
      exact ne_of_gt (by linarith))
    hR hC

/-- T2′ for a polygon with two boundary pairs, in the form in which the nests state it. -/
theorem polyRegion_pair_eq_pairSideNear_inter {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (P Q : Work.EL.CoPair hN) (hA : Work.EL.PolyAdmissible [P, Q])
    {R : ℝ} (hR : 1 < R) (hC : Work.Top.IsJordanCurve (Work.EL.polyCurve [P, Q] R)) :
    Work.EL.polyRegion [P, Q] R =
      (Work.EL.pairSideNear P ∩ Work.EL.pairSideNear Q ∩
        {z : ℂ | Work.EL.pot hN z < Real.log R}) := by
  rw [polyRegion_eq_iInter_pairSideNear hN hJ [P, Q] hA hR hC]
  ext z
  simp only [List.mem_cons, List.not_mem_nil, IsEmpty.forall_iff, forall_eq_or_imp, true_and,
    Set.mem_setOf_eq, Set.mem_inter_iff]
  tauto

end Work.ELTop
