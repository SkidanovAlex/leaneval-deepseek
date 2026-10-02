import Mathlib
import Submission.Work.ThomBordism.KeyLocal.chartDefs
import Submission.Work.ThomBordism.KeyLocal.tubeTanReading
import Submission.Work.ThomBordism.KeyLocal.chartCoh_eq_frameSign_smul

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000

namespace Work.ThomBordism.KeyLocal

/-- **(T1) with the admissible class `o` in place of the chart class.**

`chartCoh` is the `frameSign`-multiple of any class `o` which pairs to `1` with the local fundamental
class (`Work.ThomBordism.KeyLocal.chartCoh_eq_frameSign_smul`), and the tangential reading
`Work.ThomBordism.KeyLocal.tubeTanReading` computes the tube-restriction of `chartCoh`.  Combining
them gives the tube-restriction of `o`: it is the same `±`-multiple of the pullback of the model
class `tau` along the tangential coordinate map `tChartA`. -/
theorem tubeTanReadingO {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (i : Work.ThomBordism.PontryaginThom.CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i)
    (o : Work.Thom.RelCoh ℤ 8 V.pt (Work.ThomBordism.FrameSigns.punct V x))
    (ho : Work.Tubular.relKronH (TopCat.of V.pt) (Work.ThomBordism.FrameSigns.punct V x) 8 o
        (Work.Orient.locClass (TopCat.of V.pt) 8 V.c x) = 1)
    (hmemV : ∀ y ∈ Work.ThomBordism.KeyLocal.tubeFootPunct E C ND i x,
      (Work.ThomBordism.FrameSigns.srcIncl V i.1) (Work.ThomBordism.KeyLocal.tubeFootSrc E C ND i y)
        ∈ Work.ThomBordism.FrameSigns.punct V x)
    (hmem8 : ∀ y ∈ Work.ThomBordism.KeyLocal.tubeFootPunct E C ND i x,
      Work.ThomBordism.KeyLocal.tChartA E C ND i x hx y ∈ Work.ThomBordism.FrameSigns.E8p) :
    (Work.Thom.relCohMap ((Work.ThomBordism.FrameSigns.srcIncl V i.1).comp
        (Work.ThomBordism.KeyLocal.tubeFootSrc E C ND i))
        (Work.ThomBordism.KeyLocal.tubeFootPunct E C ND i x)
        (Work.ThomBordism.FrameSigns.punct V x) hmemV ℤ 8).hom o
      = (if 0 < Work.ThomBordism.FrameSigns.pairVal V i.1 x (ND.baseSet_sub i.1 i.2 x hx)
          then (1 : ℤ) else -1) •
        (Work.Thom.relCohMap (Work.ThomBordism.KeyLocal.tChartA E C ND i x hx)
          (Work.ThomBordism.KeyLocal.tubeFootPunct E C ND i x)
          Work.ThomBordism.FrameSigns.E8p hmem8 ℤ 8).hom Work.ThomBordism.FrameSigns.tau := by
  classical
  -- the membership bookkeeping for the two maps into the normal total space
  have hincmem : ∀ y ∈ Work.ThomBordism.KeyLocal.tubeFootPunct E C ND i x,
      Work.ThomBordism.KeyLocal.tubeBaseSetIncl E C ND i y
        ∈ Work.ThomBordism.KeyLocal.normalPunctAt E x := fun y hy => by
    show Work.Tubular.NormalTotal.proj (C.inv (y : ↥C.U).1) ≠ x
    exact hy
  have hprojmem : ∀ p ∈ Work.ThomBordism.KeyLocal.normalPunctAt E x,
      (⟨Work.Tubular.NormalTotal.proj, Work.Tubular.NormalTotal.continuous_proj E⟩ :
        C(Work.Tubular.NormalTotal E, V.pt)) p ∈ Work.ThomBordism.FrameSigns.punct V x :=
    fun p hp => hp
  have hcomp1 : ∀ y ∈ Work.ThomBordism.KeyLocal.tubeFootPunct E C ND i x,
      ((⟨Work.Tubular.NormalTotal.proj, Work.Tubular.NormalTotal.continuous_proj E⟩ :
        C(Work.Tubular.NormalTotal E, V.pt)).comp
        (Work.ThomBordism.KeyLocal.tubeBaseSetIncl E C ND i)) y
        ∈ Work.ThomBordism.FrameSigns.punct V x :=
    fun y hy => hprojmem _ (hincmem y hy)
  -- the two composites into the manifold agree
  have hmap2 : ((⟨Work.Tubular.NormalTotal.proj, Work.Tubular.NormalTotal.continuous_proj E⟩ :
        C(Work.Tubular.NormalTotal E, V.pt)).comp
      (Work.ThomBordism.KeyLocal.tubeBaseSetIncl E C ND i))
      = (Work.ThomBordism.FrameSigns.srcIncl V i.1).comp
          (Work.ThomBordism.KeyLocal.tubeFootSrc E C ND i) := by
    apply ContinuousMap.ext
    intro y
    rfl
  -- the tangential reading of the chart class, in the shape of the target
  have key : (Work.Thom.relCohMap ((Work.ThomBordism.FrameSigns.srcIncl V i.1).comp
        (Work.ThomBordism.KeyLocal.tubeFootSrc E C ND i))
        (Work.ThomBordism.KeyLocal.tubeFootPunct E C ND i x)
        (Work.ThomBordism.FrameSigns.punct V x) hmemV ℤ 8).hom
        (Work.ThomBordism.FrameSigns.chartCoh V i.1 x (ND.baseSet_sub i.1 i.2 x hx))
      = (Work.Thom.relCohMap (Work.ThomBordism.KeyLocal.tChartA E C ND i x hx)
          (Work.ThomBordism.KeyLocal.tubeFootPunct E C ND i x)
          Work.ThomBordism.FrameSigns.E8p hmem8 ℤ 8).hom Work.ThomBordism.FrameSigns.tau := by
    rw [← Work.Thom.relCohMap_congrA (Work.ThomBordism.KeyLocal.tubeFootPunct E C ND i x)
      (Work.ThomBordism.FrameSigns.punct V x) hmap2 hcomp1 hmemV ℤ 8]
    rw [← Work.Thom.relCohMap_compA_apply (Work.ThomBordism.KeyLocal.tubeFootPunct E C ND i x)
      (Work.ThomBordism.KeyLocal.normalPunctAt E x) (Work.ThomBordism.FrameSigns.punct V x)
      (Work.ThomBordism.KeyLocal.tubeBaseSetIncl E C ND i)
      (⟨Work.Tubular.NormalTotal.proj, Work.Tubular.NormalTotal.continuous_proj E⟩ :
        C(Work.Tubular.NormalTotal E, V.pt)) hincmem hprojmem hcomp1 ℤ 8
      (Work.ThomBordism.FrameSigns.chartCoh V i.1 x (ND.baseSet_sub i.1 i.2 x hx))]
    simpa [Work.ThomBordism.KeyLocal.tChartA] using
      (Work.ThomBordism.KeyLocal.tubeTanReading (V := V) (k := k) E C ND i x hx)
  -- conversion of `o` into the chart class, in the two possible signs of `pairVal`
  by_cases hpos : 0 < Work.ThomBordism.FrameSigns.pairVal V i.1 x (ND.baseSet_sub i.1 i.2 x hx)
  · have hchart : Work.ThomBordism.FrameSigns.chartCoh V i.1 x (ND.baseSet_sub i.1 i.2 x hx)
        = o := by
      rw [Work.ThomBordism.KeyLocal.chartCoh_eq_frameSign_smul V i.1
        (ND.baseSet_sub i.1 i.2 x hx) o ho, if_pos hpos, one_smul]
    rw [if_pos hpos, one_smul, ← hchart]
    exact key
  · have hchart : Work.ThomBordism.FrameSigns.chartCoh V i.1 x (ND.baseSet_sub i.1 i.2 x hx)
        = -o := by
      rw [Work.ThomBordism.KeyLocal.chartCoh_eq_frameSign_smul V i.1
        (ND.baseSet_sub i.1 i.2 x hx) o ho, if_neg hpos]
      simp
    have ho' : o = - Work.ThomBordism.FrameSigns.chartCoh V i.1 x
        (ND.baseSet_sub i.1 i.2 x hx) := by
      rw [hchart, neg_neg]
    rw [if_neg hpos, ho', map_neg, key]
    simp

end Work.ThomBordism.KeyLocal
