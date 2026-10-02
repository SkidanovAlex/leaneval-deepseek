import Mathlib
import Submission.Work.ThomBordism.LeadChapter.CollarChartCore

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `collarChart_left_inv`

The left-inverse half of the collar-chart statement `chapter_collarChart` (S4): for a point `q` of
the level set in the source of the collar chart (i.e. with collar coordinate below `deltaC εcl` and
whose downward projection is identified with the piece `a`), the collar lift `collarW` of
`toFunC q` is `q` again.

The point is that on `srcC T` the clamp in `collZ` is the identity, and the chart value
`tail 8 (toFunC q)` inverts through the piece chart `chartE T.a T.i` to `pieceOf T q`, so that the
`BdryId`-inverse appearing in `collarPiece` collapses back to the projection of `q`. -/

namespace Work.ThomBordism

open Work.ThomBordism.LeadChapter

noncomputable section

variable {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
  {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]

/-- The clamped collar lift, unfolded: the clamp in `collZ` only affects the collar coordinate. -/
theorem collarVec_eq (T : CollarData k D ι Fam) (z : EuclideanHalfSpace 9) :
    collarVec T z = Work.PTGeometric.consVec (clampC T.εcl (z.1 0))
      (Work.PTGeometric.tailVec (((T.h.symm ⟨T.a, (chartE T.a T.i).symm
        (Work.PTGeometric.tail 8 z.1)⟩).1).1)) := by
  rw [collarVec, collarPiece, collZ_apply_zero, tail_collZ]
  simp only [chartE]

theorem collarChart_left_inv {k : ℕ}
    {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]
    (T : Work.ThomBordism.LeadChapter.CollarData k D ι Fam)
    (q : Work.ThomBordism.LeadChapter.DataLW T)
    (hq : q ∈ Work.ThomBordism.LeadChapter.srcC T) :
    Work.ThomBordism.LeadChapter.collarW T (Work.ThomBordism.LeadChapter.toFunC T q) = q := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  show collarVec T (toFunC T q) = q.1.1.1
  have htgt : (toFunC T q).1 0 = q.1.1.1 0 := toFunC_apply_zero T q hq
  have htail : Work.PTGeometric.tail 8 (toFunC T q).1 = chartE T.a T.i (pieceOf T q hq) :=
    tail_toFunC T q hq
  have hclamp : clampC T.εcl (q.1.1.1 0) = q.1.1.1 0 := by
    refine clampC_eq_self q.1.1.2 ?_
    exact le_of_lt (lt_of_lt_of_le hq.1 (deltaC_le_min (le_of_lt T.hεcl)))
  have hsym : (chartE T.a T.i).symm (Work.PTGeometric.tail 8 (toFunC T q).1) = pieceOf T q hq := by
    rw [htail, (chartE T.a T.i).left_inv (pieceOf_mem T q hq)]
  have hsub : T.h.symm ⟨T.a, pieceOf T q hq⟩
      = ⟨projPt (q.1.1), projPt_mem_bdryDom T hq.1⟩ := by
    have h1 : Sigma.mk T.a (pieceOf T q hq)
        = T.h ⟨projPt (q.1.1), projPt_mem_bdryDom T hq.1⟩ :=
      fibreHomeo_mk (Fam := Fam) T.a _
    simpa using congrArg T.h.symm h1
  have hsub2 : T.h.symm ⟨T.a, (chartE T.a T.i).symm (Work.PTGeometric.tail 8 (toFunC T q).1)⟩
      = ⟨projPt (q.1.1), projPt_mem_bdryDom T hq.1⟩ := by
    rw [hsym, hsub]
  have htailvec : Work.PTGeometric.tailVec
        (((T.h.symm ⟨T.a, (chartE T.a T.i).symm
          (Work.PTGeometric.tail 8 (toFunC T q).1)⟩).1).1)
      = Work.PTGeometric.tailVec (q.1.1.1) := by
    rw [hsub2]
    rw [show (((⟨projPt (q.1.1), projPt_mem_bdryDom T hq.1⟩
        : ↥(bdryDom T.G T.m T.hpow)).1).1) = (projPt (q.1.1) : SrcHS k).1 from rfl,
      projPt_coe]
    rw [Work.PTGeometric.tailVec, Work.PTGeometric.tailVec_apply_zero, zero_smul, sub_zero]
  rw [collarVec_eq]
  rw [htgt, hclamp, htailvec]
  exact Work.PTGeometric.consVec_tailVec q.1.1.1

end

end Work.ThomBordism
