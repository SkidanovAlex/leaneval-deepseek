import Mathlib
import Submission.Work.ThomBordism.LeadChapter.CollarChartCore

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `collarChart_continuous_toFun`

The collar chart `toFunC T` of the level set at a piece is continuous on its source `srcC T`.

The source `srcC T` is the open set of the level set `{w = 0}` consisting of the points of the
`δ`-collar whose downward projection `projPt` is identified with the piece `T.a` (through the chart
`T.i`) by the boundary homeomorphism `T.h`.  On `srcC T` the chart is

`q ↦ hsCons (q₀) (q ∈ ∂) (φᵢ (pieceOf q))`,

i.e. it records the collar height `q₀` and the piece coordinate `φᵢ` of the boundary point obtained
from `projPt q` by `T.h`.  Both ingredients are continuous:

* `q ↦ q₀` is a coordinate function;
* `q ↦ φᵢ (pieceOf q)` is `φᵢ` (continuous on its source, an open partial homeomorphism) composed
  with `pieceOf`, which is the composition of `projPt`, the homeomorphism `T.h`, the embedding of
  the fibre `Σ a, (Fam a).pt` over `T.a`, and the fibre homeomorphism `fibreHomeo T.a`;
* `hsCons` is built from `euCons`, which is continuous.

Nothing here uses the specific geometry of the piece: only that `T.h` is a homeomorphism and that
`chartE` is an open partial homeomorphism.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open CategoryTheory Function Set

namespace Work.ThomBordism

open Work.ThomBordism.LeadChapter Work.PTGeometric

noncomputable section

/-- **The collar chart is continuous on its source.**

On the source `srcC T` the chart reads `q ↦ hsCons q₀ (φᵢ (pieceOf q))`; the collar coordinate is a
coordinate function, and `pieceOf` is a composition of `projPt`, the boundary homeomorphism `T.h`,
the fibre embedding and the fibre homeomorphism, so it is continuous. -/
theorem collarChart_continuous_toFun {k : ℕ}
    {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]
    (T : Work.ThomBordism.LeadChapter.CollarData k D ι Fam) :
    ContinuousOn (Work.ThomBordism.LeadChapter.toFunC T)
      (Work.ThomBordism.LeadChapter.srcC T) := by
  rw [continuousOn_iff_continuous_domRestrict]
  -- the collar coordinate `q ↦ q₀`
  have hcoord : Continuous (fun q : ↥(srcC T) => q.1.1.1.1 0) := by fun_prop
  -- the downward projection `q ↦ projPt q`
  have hproj : Continuous (fun q : ↥(srcC T) => projPt (q.1.1.1)) :=
    continuous_projPt.comp (by fun_prop)
  -- its value lies in the domain of the boundary identification
  have hbdry : Continuous (fun q : ↥(srcC T) =>
      (⟨projPt (q.1.1.1), projPt_mem_bdryDom T q.2.1⟩ : ↥(bdryDom T.G T.m T.hpow))) :=
    hproj.subtype_mk (fun q => projPt_mem_bdryDom T q.2.1)
  -- the boundary point through the identification `T.h`
  have hhom : Continuous (fun q : ↥(srcC T) =>
      T.h ⟨projPt (q.1.1.1), projPt_mem_bdryDom T q.2.1⟩) :=
    T.h.continuous.comp hbdry
  -- its fibre over the piece `T.a`
  have hrange : Continuous (fun q : ↥(srcC T) =>
      (⟨T.h ⟨projPt (q.1.1.1), projPt_mem_bdryDom T q.2.1⟩,
        UaC_mem_range ((mem_Ofam_iff (projPt_mem_bdryDom T q.2.1)).mp q.2.2)⟩ :
        ↥(Set.range (Sigma.mk (β := fun c : Fin T.m × ι => (Fam c.2).pt) T.a)))) :=
    hhom.subtype_mk
      (fun q => UaC_mem_range ((mem_Ofam_iff (projPt_mem_bdryDom T q.2.1)).mp q.2.2))
  -- the piece point
  have hpiece : Continuous (fun q : ↥(srcC T) => pieceOf T q.1 q.2) :=
    (fibreHomeo (Fam := Fam) T.a).continuous.comp hrange
  -- the piece chart, continuous on its (open) source
  have hchart : ContinuousOn (chartE T.a T.i) (chartE T.a T.i).source :=
    (chartE T.a T.i).continuousOn_toFun
  have hchartpiece : Continuous (fun q : ↥(srcC T) => chartE T.a T.i (pieceOf T q.1 q.2)) :=
    continuousOn_univ.mp (hchart.comp hpiece.continuousOn (fun q _ => pieceOf_mem T q.1 q.2))
  -- the ambient vector of the chart value
  have heuc : Continuous (fun q : ↥(srcC T) =>
      euCons (q.1.1.1.1 0) (chartE T.a T.i (pieceOf T q.1 q.2))) :=
    continuous_euCons.comp (hcoord.prodMk hchartpiece)
  -- the chart value itself
  have hF : Continuous (fun q : ↥(srcC T) =>
      hsCons (q.1.1.1.1 0) q.1.1.1.2 (chartE T.a T.i (pieceOf T q.1 q.2))) :=
    heuc.subtype_mk (fun q => by rw [euCons_zero]; exact q.1.1.1.2)
  exact hF.congr (fun q => (toFunC_apply T q.1 q.2).symm)

end

end Work.ThomBordism
