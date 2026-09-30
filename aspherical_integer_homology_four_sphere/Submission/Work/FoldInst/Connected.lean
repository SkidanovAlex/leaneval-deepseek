/-
# `M̄` is connected

`M̄` is the quotient of the two copies `ZMod 2 × Q̄`; each copy maps onto a connected set (the
continuous image of the convex, nonempty polytope `Q̄`), and the two copies meet in `M̄`
(`Work.FoldInst.copies_meet`).  Hence `M̄` is connected — one of the topological instances the
`Space/` area needs.
-/
import Mathlib
import Submission.Work.FoldInst.Quotient
import Submission.Work.FoldInst.copies_meet
import Submission.Work.FoldInst.Qbar_geometry

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set

namespace Work.FoldInst

/-- Every element of `ZMod 2` is `0` or `1`. -/
theorem zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c; decide

/-- The quotient map is continuous. -/
theorem continuous_mk : Continuous (mk : Xbar → Mbar) := continuous_quotient_mk'

instance instPreconnectedSpaceQbar : PreconnectedSpace Qbar :=
  isPreconnected_iff_preconnectedSpace.mp
    (Qbar_geometry.2.1.isConnected Qbar_geometry.2.2.2.1).isPreconnected

/-- The "copy `c`" slice of `Xbar` is preconnected: it is the image of the polytope `Q̄`. -/
theorem isPreconnected_copy (c : ZMod 2) : IsPreconnected {z : Xbar | z.1 = c} := by
  have hcont : Continuous fun q : Qbar => (c, q) := continuous_const.prodMk continuous_id
  have himg : {z : Xbar | z.1 = c} = Set.range (fun q : Qbar => (c, q)) := by
    ext z
    constructor
    · intro hz; exact ⟨z.2, by rw [← hz]⟩
    · rintro ⟨q, rfl⟩; rfl
  rw [himg]
  exact isPreconnected_range hcont

/-- The union `mk '' {z | z.1 = 0} ∪ mk '' {z | z.1 = 1}` is all of `M̄`. -/
theorem mk_copy_union : (univ : Set Mbar)
    = mk '' {z : Xbar | z.1 = 0} ∪ mk '' {z : Xbar | z.1 = 1} := by
  ext p
  constructor
  · intro _
    obtain ⟨z, rfl⟩ := Quotient.exists_rep p
    rcases zmod2_eq_zero_or_one z.1 with h | h
    · exact Or.inl ⟨z, h, rfl⟩
    · exact Or.inr ⟨z, h, rfl⟩
  · intro _; exact mem_univ _

/-- **`M̄` is connected.**  The two copies of `Q̄` cover `M̄`, each maps onto a preconnected set,
and they meet at the point identified by the side pairing of `copies_meet`. -/
instance instConnectedSpaceMbar : ConnectedSpace Mbar := by
  obtain ⟨x, y, hx, hy, hxy⟩ := copies_meet
  have hmeet : (mk '' {z : Xbar | z.1 = 0} ∩ mk '' {z : Xbar | z.1 = 1}).Nonempty :=
    ⟨mk x, ⟨⟨x, hx, rfl⟩, ⟨y, hy, (Quotient.sound hxy).symm⟩⟩⟩
  have hpre : IsPreconnected (univ : Set Mbar) := by
    rw [mk_copy_union]
    exact IsPreconnected.union' hmeet ((isPreconnected_copy 0).image _ continuous_mk.continuousOn)
      ((isPreconnected_copy 1).image _ continuous_mk.continuousOn)
  exact { toPreconnectedSpace := ⟨hpre⟩, toNonempty := ⟨mk x⟩ }

end Work.FoldInst
