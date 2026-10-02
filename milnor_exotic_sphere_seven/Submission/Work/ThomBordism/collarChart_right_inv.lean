import Mathlib
import Submission.Work.ThomBordism.LeadChapter.CollarChartCore

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.ThomBordism.collarChart_right_inv`

The right inverse law of the collar chart of the level set at a piece: the chart
`toFunC` of `CollarChartCore` sends the collar lift `collarW` of a point `z` of the
target back to `z`.

The proof is a direct computation:
* `collarW T z` is clamped, so on the target `tgtC` (where `0 ≤ z 0 < δ ≤ min (1/4) εcl`)
  the clamp is the identity and `(collarW T z).1.1.1 0 = z.1 0`;
* the downward projection of `collarW T z` is the boundary zero
  `collBdry T z = (h.symm ⟨a, φᵢ⁻¹ (tail z)⟩).1`, so it lies over the piece `a` with chart `i`;
* hence `pieceOf (collarW T z) = φᵢ⁻¹ (tail z)` and `toFunC (collarW T z) = z` by the
  head/tail algebra of `hsCons`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
open scoped Manifold ContDiff Topology
open CategoryTheory Function Set Classical

namespace Work.ThomBordism

open Work.ThomBordism.LeadChapter Work.PTGeometric

/-- If the representative `s` of a point of the range of `Sigma.mk a` has value `⟨a, y⟩`, then
`fibreHomeo a s = y`.  (The membership proof is irrelevant.) -/
theorem fibreHomeo_eq_of {m : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}
    (a : Fin m × ι)
    {s : ↥(Set.range (Sigma.mk (β := fun c : Fin m × ι => (Fam c.2).pt) a))}
    {y : (Fam a.2).pt} (h : s.1 = ⟨a, y⟩) :
    fibreHomeo (Fam := Fam) a s = y := by
  have h1 : s = ⟨⟨a, y⟩, Set.mem_range_self y⟩ := Subtype.ext h
  rw [h1]
  exact fibreHomeo_apply a y

theorem collarChart_right_inv {k : ℕ}
    {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]
    (T : Work.ThomBordism.LeadChapter.CollarData k D ι Fam)
    {z : EuclideanHalfSpace 9}
    (hz : z ∈ Work.ThomBordism.LeadChapter.tgtC T.εcl T.a T.i) :
    Work.ThomBordism.LeadChapter.toFunC T (Work.ThomBordism.LeadChapter.collarW T z) = z := by
  -- (0) the clamp is the identity on the target
  have hw0 : (collarW T z).1.1.1 0 = z.1 0 := by
    rw [collarW_apply_zero]
    refine clampC_eq_self z.2 ?_
    exact le_trans (le_of_lt hz.1) (deltaC_le_min (le_of_lt T.hεcl))
  have hdelta : (collarW T z).1.1.1 0 < deltaC T.εcl := by rw [hw0]; exact hz.1
  -- (1) the collar lift lies in the source of the chart
  have hmem : projPt ((collarW T z).1.1) ∈ TOfam T := by
    have hc : projPt ((collarW T z).1.1) ∈ bdryDom T.G T.m T.hpow :=
      projPt_mem_bdryDom T hdelta
    rw [mem_Ofam_iff hc]
    have hpt : projPt ((collarW T z).1.1) = collBdry T z := by
      refine Subtype.ext ?_
      show Work.PTGeometric.tailVec ((collarW T z).1.1).1 = (collBdry T z).1
      have h : ((collarW T z).1.1).1 = collarVec T z := rfl
      rw [h]
      exact collarVec_tail' T z
    have hcb : collBdry T z ∈ bdryDom T.G T.m T.hpow :=
      ⟨collBdry_mem T z, collBdry_apply_zero T z⟩
    have hcongr : T.h ⟨projPt ((collarW T z).1.1), hc⟩ = T.h ⟨collBdry T z, hcb⟩ :=
      congrArg T.h (Subtype.ext hpt)
    have hs : T.h ⟨collBdry T z, hcb⟩
        = ⟨T.a, (chartE T.a T.i).symm (Work.PTGeometric.tail 8 z.1)⟩ := by
      have h1 : (⟨collBdry T z, hcb⟩ : ↥(bdryDom T.G T.m T.hpow))
          = T.h.symm ⟨T.a, (chartE T.a T.i).symm (Work.PTGeometric.tail 8 z.1)⟩ :=
        Subtype.ext rfl
      exact (congrArg T.h h1).trans (T.h.apply_symm_apply _)
    rw [hcongr, hs]
    exact ⟨(chartE T.a T.i).symm (Work.PTGeometric.tail 8 z.1),
      (chartE T.a T.i).map_target hz.2, rfl⟩
  have hq : collarW T z ∈ srcC T := ⟨hdelta, hmem⟩
  -- (2) the boundary identification of the projection
  have hs : T.h ⟨projPt ((collarW T z).1.1), projPt_mem_bdryDom T hdelta⟩
      = ⟨T.a, (chartE T.a T.i).symm (Work.PTGeometric.tail 8 z.1)⟩ := by
    have hcb : collBdry T z ∈ bdryDom T.G T.m T.hpow :=
      ⟨collBdry_mem T z, collBdry_apply_zero T z⟩
    have hpt : projPt ((collarW T z).1.1) = collBdry T z := by
      refine Subtype.ext ?_
      show Work.PTGeometric.tailVec ((collarW T z).1.1).1 = (collBdry T z).1
      have h : ((collarW T z).1.1).1 = collarVec T z := rfl
      rw [h]
      exact collarVec_tail' T z
    have hcongr : T.h ⟨projPt ((collarW T z).1.1), projPt_mem_bdryDom T hdelta⟩
        = T.h ⟨collBdry T z, hcb⟩ := congrArg T.h (Subtype.ext hpt)
    have hs2 : T.h ⟨collBdry T z, hcb⟩
        = ⟨T.a, (chartE T.a T.i).symm (Work.PTGeometric.tail 8 z.1)⟩ := by
      have h1 : (⟨collBdry T z, hcb⟩ : ↥(bdryDom T.G T.m T.hpow))
          = T.h.symm ⟨T.a, (chartE T.a T.i).symm (Work.PTGeometric.tail 8 z.1)⟩ :=
        Subtype.ext rfl
      exact (congrArg T.h h1).trans (T.h.apply_symm_apply _)
    exact hcongr.trans hs2
  have hpiece : pieceOf T (collarW T z) hq
      = (chartE T.a T.i).symm (Work.PTGeometric.tail 8 z.1) := by
    rw [pieceOf_eq]
    exact fibreHomeo_eq_of T.a (h := hs)
  -- (3) the chart value
  rw [toFunC_apply T (collarW T z) hq]
  trans Work.ThomBordism.LeadChapter.hsCons (z.1 0) z.2 (Work.PTGeometric.tail 8 z.1)
  · refine (hsCons_eq_iff (collarW T z).1.1.2 z.2).mpr ⟨hw0, ?_⟩
    rw [hpiece]
    exact (chartE T.a T.i).right_inv hz.2
  · exact eq_hsCons z

end Work.ThomBordism
