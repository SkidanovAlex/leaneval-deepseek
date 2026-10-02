import Submission.Work.ThomBordism.KeyLocal.tubeSets

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory

namespace Work.ThomBordism.KeyLocal

noncomputable section

open Work.Tubular Work.ThomBordism.PontryaginThom

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The tangential reading of the tube** (piece (T1) of the last-mile plan).

The restriction to the part of the tube over the chart `i` of the normal datum, of the pullback
`π^*(chartCoh V i.1 x hx)` of the chart class to the normal total space, is the pullback of the
model class `tau` of `(ℝ⁸, ℝ⁸∖0)` along the translated chart composed with the foot map of the
tube.  (The chart class is the `frameSign`-multiple of the admissible class
`Work.ThomBordism.KeyLocal`'s `o_x`, and `tau` is a `±1`-multiple of `stdModelGen 8`; those two
conversions are the sign bookkeeping of the plan.)

Proof: functoriality of `relCohMap` twice and the defining property of the chart class
`Work.ThomBordism.FrameSigns.chartCoh_spec`. -/
theorem tubeTanReading (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i) :
    (Work.Thom.relCohMap (tubeBaseSetIncl E C ND i) (tubeFootPunct E C ND i x)
        (normalPunctAt E x)
        (fun y hy => by
          show NormalTotal.proj (C.inv (y : ↥C.U).1) ≠ x
          exact hy) ℤ 8).hom
      ((Work.Thom.relCohMap
          (⟨NormalTotal.proj, NormalTotal.continuous_proj E⟩ :
            C(NormalTotal E, V.pt)) (normalPunctAt E x) (FrameSigns.punct V x)
          (fun p hp => hp) ℤ 8).hom
        (FrameSigns.chartCoh V i.1 x (ND.baseSet_sub i.1 i.2 x hx)))
    = (Work.Thom.relCohMap
        ((FrameSigns.chartTrans V i.1 x (ND.baseSet_sub i.1 i.2 x hx)).comp
          (tubeFootSrc E C ND i)) (tubeFootPunct E C ND i x) FrameSigns.E8p
        (fun y hy => FrameSigns.chartTrans_mem V i.1 x (ND.baseSet_sub i.1 i.2 x hx)
          (tubeFootSrc E C ND i y) (tubeFootSrc_mem E C ND i y hy)) ℤ 8).hom
      FrameSigns.tau := by
  classical
  set hxS : x ∈ FrameSigns.src V i.1 := ND.baseSet_sub i.1 i.2 x hx with hhxS
  -- the pair conditions
  have hincmem : ∀ y ∈ tubeFootPunct E C ND i x,
      tubeBaseSetIncl E C ND i y ∈ normalPunctAt E x := fun y hy => by
    show NormalTotal.proj (C.inv (y : ↥C.U).1) ≠ x
    exact hy
  have hprojmem : ∀ p ∈ normalPunctAt E x,
      (⟨NormalTotal.proj, NormalTotal.continuous_proj E⟩ : C(NormalTotal E, V.pt)) p
        ∈ FrameSigns.punct V x := fun p hp => hp
  have hcomp1 : ∀ y ∈ tubeFootPunct E C ND i x,
      ((⟨NormalTotal.proj, NormalTotal.continuous_proj E⟩ : C(NormalTotal E, V.pt)).comp
        (tubeBaseSetIncl E C ND i)) y ∈ FrameSigns.punct V x :=
    fun y hy => hprojmem _ (hincmem y hy)
  -- `proj ∘ inc = srcIncl ∘ fsrc`
  have hmap2 : ((⟨NormalTotal.proj, NormalTotal.continuous_proj E⟩ : C(NormalTotal E, V.pt)).comp
      (tubeBaseSetIncl E C ND i))
      = (FrameSigns.srcIncl V i.1).comp (tubeFootSrc E C ND i) := by
    apply ContinuousMap.ext; intro y; rfl
  have hsrcmem : ∀ y ∈ tubeFootPunct E C ND i x,
      (FrameSigns.srcIncl V i.1) ((tubeFootSrc E C ND i) y) ∈ FrameSigns.punct V x :=
    fun y hy => FrameSigns.punctSrc_mem V i.1 x _ (tubeFootSrc_mem E C ND i y hy)
  have hfsrcmem : ∀ y ∈ tubeFootPunct E C ND i x,
      ((FrameSigns.srcIncl V i.1).comp (tubeFootSrc E C ND i)) y ∈ FrameSigns.punct V x :=
    hsrcmem
  have hctmem : ∀ z ∈ FrameSigns.punctSrc V i.1 x,
      FrameSigns.chartTrans V i.1 x hxS z ∈ FrameSigns.E8p :=
    FrameSigns.chartTrans_mem V i.1 x hxS
  -- Step 1: functoriality of the outer pullbacks
  rw [Work.Thom.relCohMap_compA_apply (A := tubeFootPunct E C ND i x)
    (B := normalPunctAt E x) (C := FrameSigns.punct V x) (tubeBaseSetIncl E C ND i)
    (⟨NormalTotal.proj, NormalTotal.continuous_proj E⟩ : C(NormalTotal E, V.pt))
    hincmem hprojmem hcomp1 ℤ 8
    (FrameSigns.chartCoh V i.1 x hxS)]
  rw [show (Work.Thom.relCohMap
        (((⟨NormalTotal.proj, NormalTotal.continuous_proj E⟩ : C(NormalTotal E, V.pt)).comp
          (tubeBaseSetIncl E C ND i))) (tubeFootPunct E C ND i x) (FrameSigns.punct V x)
        hcomp1 ℤ 8)
      = (Work.Thom.relCohMap ((FrameSigns.srcIncl V i.1).comp (tubeFootSrc E C ND i))
          (tubeFootPunct E C ND i x) (FrameSigns.punct V x) hfsrcmem ℤ 8) from
    Work.Thom.relCohMap_congrA (tubeFootPunct E C ND i x) (FrameSigns.punct V x) hmap2
      hcomp1 hfsrcmem ℤ 8]
  rw [← Work.Thom.relCohMap_compA_apply (A := tubeFootPunct E C ND i x)
    (B := FrameSigns.punctSrc V i.1 x) (C := FrameSigns.punct V x) (tubeFootSrc E C ND i)
    (FrameSigns.srcIncl V i.1) (tubeFootSrc_mem E C ND i) (FrameSigns.punctSrc_mem V i.1 x)
    hfsrcmem ℤ 8 (FrameSigns.chartCoh V i.1 x hxS)]
  -- Step 3: the defining property of the chart class
  rw [show (Work.Thom.relCohMap (FrameSigns.srcIncl V i.1) (FrameSigns.punctSrc V i.1 x)
        (FrameSigns.punct V x) (FrameSigns.punctSrc_mem V i.1 x) ℤ 8).hom
        (FrameSigns.chartCoh V i.1 x hxS)
      = (Work.Thom.relCohMap (FrameSigns.chartTrans V i.1 x hxS)
          (FrameSigns.punctSrc V i.1 x) FrameSigns.E8p
          (FrameSigns.chartTrans_mem V i.1 x hxS) ℤ 8).hom FrameSigns.tau from
    FrameSigns.chartCoh_spec V i.1 (x := x) hxS]
  -- Step 4: functoriality again
  rw [← Work.Thom.relCohMap_compA_apply (A := tubeFootPunct E C ND i x)
    (B := FrameSigns.punctSrc V i.1 x) (C := FrameSigns.E8p) (tubeFootSrc E C ND i)
    (FrameSigns.chartTrans V i.1 x hxS) (tubeFootSrc_mem E C ND i) hctmem
    (fun y hy => hctmem _ (tubeFootSrc_mem E C ND i y hy)) ℤ 8 FrameSigns.tau]

end

end Work.ThomBordism.KeyLocal
