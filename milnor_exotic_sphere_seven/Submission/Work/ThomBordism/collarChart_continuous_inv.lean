import Mathlib
import Submission.Work.ThomBordism.LeadChapter.CollarChartCore

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# S4 (`chapter_collarChart`): continuity of the collar lift `collarW`

`collarW T` is the inverse of the collar chart `toFunC T`; here we prove that it is continuous on
its target `tgtC T.εcl T.a T.i`, directly from the definition `collarPiece …` (no route through the
partial homeomorphism `ψ` is needed): on `tgtC` the clamp `clampC` is the identity, so the collar
lift is the composition of the continuous chart-inverse `(chartE a i).symm` with the boundary
identification homeomorphism `T.h.symm`.
-/

namespace Work.ThomBordism

open scoped Manifold ContDiff Topology
open Work.ThomBordism.LeadChapter
open Work.PTGeometric

theorem collarChart_continuous_inv {k : ℕ}
    {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]
    (T : Work.ThomBordism.LeadChapter.CollarData k D ι Fam) :
    ContinuousOn (Work.ThomBordism.LeadChapter.collarW T)
      (Work.ThomBordism.LeadChapter.tgtC T.εcl T.a T.i) := by
  set s := tgtC T.εcl T.a T.i with hs
  have hpiece : ContinuousOn (fun z : EuclideanHalfSpace 9 =>
      collarPiece T.G T.m T.hpow T.h T.a T.i z.1) s := by
    have htail : ContinuousOn (fun z : EuclideanHalfSpace 9 => tail 8 z.1) s :=
      (continuous_tail 8).comp_continuousOn continuous_subtype_val.continuousOn
    have hsymm : ContinuousOn (fun z : EuclideanHalfSpace 9 =>
        (chartE T.a T.i).symm (tail 8 z.1)) s :=
      (chartE T.a T.i).continuousOn_invFun.comp htail (fun z hz => hz.2)
    have hsig : ContinuousOn (fun z : EuclideanHalfSpace 9 =>
        (⟨T.a, (chartE T.a T.i).symm (tail 8 z.1)⟩ :
          Σ c : Fin T.m × ι, (Fam c.2).pt)) s :=
      (continuous_sigmaMk (σ := fun c : Fin T.m × ι => (Fam c.2).pt) (i := T.a)).comp_continuousOn hsymm
    have hH : ContinuousOn (fun z : EuclideanHalfSpace 9 =>
        T.h.symm (⟨T.a, (chartE T.a T.i).symm (tail 8 z.1)⟩ :
          Σ c : Fin T.m × ι, (Fam c.2).pt)) s :=
      T.h.symm.continuous.comp_continuousOn hsig
    have hvec : ContinuousOn (fun z : EuclideanHalfSpace 9 =>
        (((T.h.symm (⟨T.a, (chartE T.a T.i).symm (tail 8 z.1)⟩ :
          Σ c : Fin T.m × ι, (Fam c.2).pt)).1).1)) s :=
      (continuous_subtype_val.comp continuous_subtype_val).comp_continuousOn hH
    have htv : ContinuousOn (fun z : EuclideanHalfSpace 9 =>
        tailVec (((T.h.symm (⟨T.a, (chartE T.a T.i).symm (tail 8 z.1)⟩ :
          Σ c : Fin T.m × ι, (Fam c.2).pt)).1).1)) s :=
      continuous_tailVec.comp_continuousOn hvec
    have hz0 : ContinuousOn (fun z : EuclideanHalfSpace 9 => z.1 0) s :=
      (by fun_prop : Continuous (fun z : EuclideanHalfSpace 9 => z.1 0)).continuousOn
    have hpair : ContinuousOn (fun z : EuclideanHalfSpace 9 =>
        (z.1 0, tailVec (((T.h.symm (⟨T.a, (chartE T.a T.i).symm (tail 8 z.1)⟩ :
          Σ c : Fin T.m × ι, (Fam c.2).pt)).1).1))) s :=
      hz0.prodMk htv
    exact continuous_consVec.comp_continuousOn hpair
  have hclamp : ∀ z ∈ s, collZ T.εcl z = z.1 := by
    intro z hz
    have h0 : 0 ≤ z.1 0 := z.2
    have ht : z.1 0 ≤ min (1 / 4) T.εcl :=
      le_trans (le_of_lt hz.1) (deltaC_le_min (le_of_lt T.hεcl))
    exact collZ_eq_of h0 ht
  have hEq : Set.EqOn
      (fun z : EuclideanHalfSpace 9 => collarPiece T.G T.m T.hpow T.h T.a T.i (collZ T.εcl z))
      (fun z : EuclideanHalfSpace 9 => collarPiece T.G T.m T.hpow T.h T.a T.i z.1) s :=
    fun z hz => by
      show collarPiece T.G T.m T.hpow T.h T.a T.i (collZ T.εcl z) =
        collarPiece T.G T.m T.hpow T.h T.a T.i z.1
      rw [hclamp z hz]
  have hvecOn : ContinuousOn (fun z : EuclideanHalfSpace 9 =>
      collarPiece T.G T.m T.hpow T.h T.a T.i (collZ T.εcl z)) s :=
    hpiece.congr hEq
  have hvec : Continuous (fun z : ↥s => collarVec T z.1) :=
    (continuousOn_iff_continuous_domRestrict).mp (by
      simpa only [collarVec] using hvecOn)
  rw [continuousOn_iff_continuous_domRestrict]
  show Continuous (fun z : ↥s => collarW T z.1)
  have h1 : Continuous (fun z : ↥s =>
      (⟨collarVec T z.1, collarVec_nonneg T z.1⟩ : SrcHS k)) :=
    hvec.subtype_mk (fun z => collarVec_nonneg T z.1)
  have h2 : Continuous (fun z : ↥s =>
      (⟨⟨collarVec T z.1, collarVec_nonneg T z.1⟩,
        (sourcePhi_spec T.G T.m T.hpow T.hphi).2.1 (collarHS_mem T z.1)⟩ : DataM T)) :=
    h1.subtype_mk (fun z => (sourcePhi_spec T.G T.m T.hpow T.hphi).2.1 (collarHS_mem T z.1))
  have h3 : Continuous (fun z : ↥s =>
      (⟨⟨⟨collarVec T z.1, collarVec_nonneg T z.1⟩,
        (sourcePhi_spec T.G T.m T.hpow T.hphi).2.1 (collarHS_mem T z.1)⟩,
        w_collarReg T z.1⟩ : DataLW T)) :=
    h2.subtype_mk (fun z => w_collarReg T z.1)
  exact h3

end Work.ThomBordism
