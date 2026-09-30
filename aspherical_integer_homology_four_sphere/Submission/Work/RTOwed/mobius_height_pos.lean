import Mathlib
import Submission.Work.RTOwed.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

/-- **The Möbius transformation of a Lorentz matrix preserves the upper half space.**  A Lorentz
matrix `A` (with `Aᵀ J A = J` and `A 4 4 > 0`) carries the upper sheet of the hyperboloid into
itself (`Work.HypModel.mulVec_mem_upperSheet`); the lift `P = A *ᵥ hypOfUHS q` of a point `q` of the
upper half space therefore lies on the upper sheet, where the height difference `P₄ − P₃` is
positive (`Work.HypModel.upperSheet_four_sub_three_pos`).  Since the height of `mobius A q` is the
reciprocal `(P₄ − P₃)⁻¹`, it is positive as well. -/
theorem mobius_height_pos {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : Work.HypModel.IsLorentzMat A)
    {q : Work.FoldInst.E4} (hq : 0 < q 3) : 0 < (Work.HypModel.mobius A q) 3 := by
  have hP : Work.HypModel.hypOfUHS q ∈ Work.HypModel.upperSheet :=
    Work.HypModel.hypOfUHS_bijOn.1 hq
  have hQ : A.mulVec (Work.HypModel.hypOfUHS q) ∈ Work.HypModel.upperSheet :=
    Work.HypModel.mulVec_mem_upperSheet hA hP
  have hpos : 0 < (A.mulVec (Work.HypModel.hypOfUHS q)) 4 -
      (A.mulVec (Work.HypModel.hypOfUHS q)) 3 :=
    Work.HypModel.upperSheet_four_sub_three_pos hQ
  rw [Work.HypModel.mobius, Work.HypModel.uhsOfHyp_apply_three]
  exact inv_pos.mpr hpos

end Work.RTOwed
