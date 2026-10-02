import Mathlib
import Submission.Work.ThomBordism.FrameSigns.Charts
import Submission.Work.ThomBordism.FrameSigns.germPullbackLocal
import Submission.Work.ThomBordism.FrameSigns.chartTrans_germ
import Submission.Work.Thom.ATools
import Submission.Work.Cohomology.capRelAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory

namespace Work.ThomBordism.FrameSigns

noncomputable section

/-! ## The overlap of two chart sources -/

/-- The overlap of the sources of two charts of the finite cover. -/
def ovl (V : Man8) (i j : ChartIdx V) : Set V.pt := src V i ∩ src V j

/-- The punctured overlap, as a subset of the overlap. -/
def ovlP (V : Man8) (i j : ChartIdx V) (x : V.pt) : Set ↥(ovl V i j) := {z | (z : V.pt) ≠ x}

/-- The inclusion of the overlap into `V`. -/
def ovlIncl (V : Man8) (i j : ChartIdx V) : C(↥(ovl V i j), V.pt) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion of the overlap into the first chart source. -/
def ovlInclFst (V : Man8) (i j : ChartIdx V) : C(↥(ovl V i j), ↥(src V i)) :=
  ⟨fun z => ⟨z.1, z.2.1⟩, Continuous.subtype_mk continuous_subtype_val (fun z => z.2.1)⟩

/-- The inclusion of the overlap into the second chart source. -/
def ovlInclSnd (V : Man8) (i j : ChartIdx V) : C(↥(ovl V i j), ↥(src V j)) :=
  ⟨fun z => ⟨z.1, z.2.2⟩, Continuous.subtype_mk continuous_subtype_val (fun z => z.2.2)⟩

/-! ## Two bookkeeping lemmas about the pullback of relative cohomology -/

/-- The pullback of relative cohomology does not depend on the proof that the first set is carried
into the second (applied form). -/
theorem relCohMap_hcongrA_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y) (h h' : ∀ x ∈ A, f x ∈ B) (R : Type) [CommRing R]
    (n : ℕ) (x : Work.Thom.RelCoh R n Y B) :
    (Work.Thom.relCohMap f A B h R n).hom x = (Work.Thom.relCohMap f A B h' R n).hom x :=
  congrArg (fun φ => φ.hom x) (Work.Thom.relCohMap_hcongrA f A B h h' R n)

/-- The pullback of relative cohomology only depends on the underlying continuous map (applied
form). -/
theorem relCohMap_congrA_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f f' : C(X, Y)} (h : f = f') (A : Set X) (B : Set Y)
    (hf : ∀ x ∈ A, f x ∈ B) (hf' : ∀ x ∈ A, f' x ∈ B) (R : Type) [CommRing R]
    (n : ℕ) (x : Work.Thom.RelCoh R n Y B) :
    (Work.Thom.relCohMap f A B hf R n).hom x = (Work.Thom.relCohMap f' A B hf' R n).hom x :=
  congrArg (fun φ => φ.hom x) (Work.Thom.relCohMap_congrA A B h hf hf' R n)

/-! ## The defining property of the chart class -/

/-- **The defining property of `chartCoh`**: the pullback of the chart class along the inclusion of
the chart source is the pullback of the model class `τ` along the translated chart. -/
theorem chartCoh_spec (V : Man8) (k : ChartIdx V) {x : V.pt} (hk : x ∈ src V k) :
    (Work.Thom.relCohMap (srcIncl V k) (punctSrc V k x) (punct V x)
        (punctSrc_mem V k x) ℤ 8).hom (chartCoh V k x hk)
      = (Work.Thom.relCohMap (chartTrans V k x hk) (punctSrc V k x) E8p
          (chartTrans_mem V k x hk) ℤ 8).hom tau := by
  haveI : CategoryTheory.IsIso (Work.Thom.relCohMap (srcIncl V k) (punctSrc V k x)
      (punct V x) (punctSrc_mem V k x) ℤ 8) := isIso_exc V k x hk
  have h := congrArg (fun φ => φ.hom ((Work.Thom.relCohMap (chartTrans V k x hk)
      (punctSrc V k x) E8p (chartTrans_mem V k x hk) ℤ 8).hom tau))
    (CategoryTheory.IsIso.inv_hom_id (Work.Thom.relCohMap (srcIncl V k) (punctSrc V k x)
      (punct V x) (punctSrc_mem V k x) ℤ 8))
  rw [chartCoh]
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply]
    using h

/-! ## The restriction of the chart class to a subset of the chart source -/

/-- **The restriction of `chartCoh` to a subset of a chart source.**  For `A ⊆ src V k`, the
pullback of `chartCoh V k x hk` to the pair `(↥A, A ∖ {x})` is the pullback of the model class `τ`
along the translated chart `k` composed with the inclusion of `A`. -/
theorem chartCoh_restrict {V : Man8} {k : ChartIdx V} {x : V.pt} (hk : x ∈ src V k)
    {A : Set V.pt} (inclA : C(↥A, ↥(src V k)))
    (hinclA : ∀ z : ↥A, (inclA z : V.pt) = z.1)
    (hmemA : ∀ z ∈ {z : ↥A | (z : V.pt) ≠ x}, (inclA z : V.pt) ≠ x)
    (hpair : ∀ z ∈ {z : ↥A | (z : V.pt) ≠ x}, (chartTrans V k x hk).comp inclA z ∈ E8p) :
    (Work.Thom.relCohMap ⟨Subtype.val, continuous_subtype_val⟩ {z : ↥A | (z : V.pt) ≠ x}
        (punct V x) (fun z hz => hz) ℤ 8).hom (chartCoh V k x hk)
      = (Work.Thom.relCohMap ((chartTrans V k x hk).comp inclA)
          {z : ↥A | (z : V.pt) ≠ x} E8p hpair ℤ 8).hom tau := by
  have hcoh := chartCoh_spec V k hk
  have hcomp_mem : ∀ z ∈ {z : ↥A | (z : V.pt) ≠ x},
      ((srcIncl V k).comp inclA) z ∈ punct V x := fun z hz => hmemA z hz
  -- the two factorisations
  have hfe : (Work.Thom.relCohMap (srcIncl V k) (punctSrc V k x) (punct V x)
        (punctSrc_mem V k x) ℤ 8)
      ≫ (Work.Thom.relCohMap inclA {z : ↥A | (z : V.pt) ≠ x} (punctSrc V k x)
          hmemA ℤ 8)
      = (Work.Thom.relCohMap ⟨Subtype.val, continuous_subtype_val⟩
          {z : ↥A | (z : V.pt) ≠ x} (punct V x) (fun z hz => hz) ℤ 8) := by
    rw [Work.Thom.relCohMap_compA {z : ↥A | (z : V.pt) ≠ x} (punctSrc V k x) (punct V x)
      inclA (srcIncl V k) hmemA (punctSrc_mem V k x) hcomp_mem ℤ 8]
    exact Work.Thom.relCohMap_congrA {z : ↥A | (z : V.pt) ≠ x} (punct V x)
      (by ext z; exact hinclA z) hcomp_mem (fun z hz => hz) ℤ 8
  have hge : (Work.Thom.relCohMap (chartTrans V k x hk) (punctSrc V k x) E8p
        (chartTrans_mem V k x hk) ℤ 8)
      ≫ (Work.Thom.relCohMap inclA {z : ↥A | (z : V.pt) ≠ x} (punctSrc V k x)
          hmemA ℤ 8)
      = (Work.Thom.relCohMap ((chartTrans V k x hk).comp inclA)
          {z : ↥A | (z : V.pt) ≠ x} E8p hpair ℤ 8) :=
    Work.Thom.relCohMap_compA {z : ↥A | (z : V.pt) ≠ x} (punctSrc V k x) E8p inclA
      (chartTrans V k x hk) hmemA (chartTrans_mem V k x hk) hpair ℤ 8
  calc (Work.Thom.relCohMap ⟨Subtype.val, continuous_subtype_val⟩ {z : ↥A | (z : V.pt) ≠ x}
        (punct V x) (fun z hz => hz) ℤ 8).hom (chartCoh V k x hk)
      = ((Work.Thom.relCohMap (srcIncl V k) (punctSrc V k x) (punct V x)
            (punctSrc_mem V k x) ℤ 8)
          ≫ (Work.Thom.relCohMap inclA {z : ↥A | (z : V.pt) ≠ x} (punctSrc V k x)
              hmemA ℤ 8)).hom (chartCoh V k x hk) := by rw [hfe]
    _ = (Work.Thom.relCohMap inclA {z : ↥A | (z : V.pt) ≠ x} (punctSrc V k x)
            hmemA ℤ 8).hom
          ((Work.Thom.relCohMap (srcIncl V k) (punctSrc V k x) (punct V x)
            (punctSrc_mem V k x) ℤ 8).hom (chartCoh V k x hk)) := by
        rw [ModuleCat.hom_comp, LinearMap.comp_apply]
    _ = (Work.Thom.relCohMap inclA {z : ↥A | (z : V.pt) ≠ x} (punctSrc V k x)
            hmemA ℤ 8).hom
          ((Work.Thom.relCohMap (chartTrans V k x hk) (punctSrc V k x) E8p
            (chartTrans_mem V k x hk) ℤ 8).hom tau) := by rw [hcoh]
    _ = ((Work.Thom.relCohMap (chartTrans V k x hk) (punctSrc V k x) E8p
            (chartTrans_mem V k x hk) ℤ 8)
          ≫ (Work.Thom.relCohMap inclA {z : ↥A | (z : V.pt) ≠ x} (punctSrc V k x)
              hmemA ℤ 8)).hom tau := by
        rw [ModuleCat.hom_comp, LinearMap.comp_apply]
    _ = (Work.Thom.relCohMap ((chartTrans V k x hk).comp inclA)
          {z : ↥A | (z : V.pt) ≠ x} E8p hpair ℤ 8).hom tau := by rw [hge]

/-- **The comparison of the chart classes at a common point of two charts.**

The two classes `chartCoh V i x hi` and `chartCoh V j x hj` in `H⁸(V, V∖{x}; ℤ)` differ by the sign
of the determinant of the derivative of the chart change.

Route.  Let `M := TopCat.of V.pt` and let `exc_ij` be the excision isomorphism
`H⁸(M, punct V x) ≅ H⁸(↥(src V i ∩ src V j), (src V i ∩ src V j)∖{x})` (`capRel_excision_isIso` with
`U = src V i ∩ src V j`, open, `A = punct V x`, open, and `U ∪ A = univ` since `x` lies in `U`).
By the defining property of `chartCoh` (the inverse of `isIso_exc`), the naturality of the inverse
of a natural isomorphism (the forward square commutes by `relCohMap_compA`), and `relCohMap_compA`,
`exc_ij (chartCoh V i x hi)` is the pullback of `τ` along `chartTrans V i x hi` restricted to the
overlap; hence it suffices to compare `(chartTrans V i x hi)^*τ` and `(chartTrans V j x hj)^*τ` on
`H⁸(↥(src V i ∩ src V j), ∖{x})`.

For `z` in that overlap, `germFun V i j x (chartTrans V i x hi z) = chartTrans V j x hj z`
(rewrite with `(chartOf V i).1.left_inv z.2` and `mod_cast`-style `sub_add_cancel`), i.e. the two
restricted maps are related by the transition germ.  The companion
`Work.ThomBordism.FrameSigns.chartTrans_germ`
(`Submission/Work/ThomBordism/FrameSigns/chartTrans_germ.lean`) supplies, on `W := germSet V i j x`,
the hypotheses of `Work.ThomBordism.FrameSigns.germPullback`
(`Submission/Work/ThomBordism/FrameSigns/germPullback.lean`) for `germFun V i j x`, with derivative
`L := fderiv ℝ (fun y => chartMap V j ((chartOf V i).1.symm y)) ((chartOf V i).1 x)` bijective;
`germPullback` therefore gives `(germFun)^*τ = (if 0 < det L then 1 else -1) • (incl)^*τ` on
`H⁸(germSet, germSet ∖ {0})`, where `incl` is the inclusion of `germSet` into `ℝ⁸`; composing with
`(chartTrans V i x hi)^*` and using `incl ∘ chartTrans = chartTrans` (as maps into `ℝ⁸`) gives the
claim.  Injectivity of `exc_ij` concludes. -/
theorem chartCoh_compare (V : Man8) (i j : ChartIdx V) {x : V.pt}
    (hi : x ∈ src V i) (hj : x ∈ src V j) :
    chartCoh V i x hi = (if 0 < LinearMap.det (ContinuousLinearMap.toLinearMap
        (fderiv ℝ (fun y => chartMap V j ((chartOf V i).1.symm y)) ((chartOf V i).1 x)))
      then (1 : ℤ) else -1) • chartCoh V j x hj := by
  let L : E8 →L[ℝ] E8 :=
    fderiv ℝ (fun y => chartMap V j ((chartOf V i).1.symm y)) ((chartOf V i).1 x)
  let s : ℤ := if 0 < LinearMap.det L.toLinearMap then (1 : ℤ) else -1
  show chartCoh V i x hi = s • chartCoh V j x hj
  -- the overlap of the two chart sources, and the excision isomorphism on it
  have hxov : x ∈ ovl V i j := ⟨hi, hj⟩
  have hU : IsOpen (ovl V i j) := (chartOf V i).1.open_source.inter (chartOf V j).1.open_source
  have hcov : ovl V i j ∪ punct V x = Set.univ := by
    ext y
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases hy : y ∈ ovl V i j
    · exact Or.inl hy
    · exact Or.inr (by simp only [punct, Set.mem_setOf_eq]; intro hyx; exact hy (hyx ▸ hxov))
  let H : Work.Thom.RelCoh ℤ 8 V.pt (punct V x) ⟶
      Work.Thom.RelCoh ℤ 8 ↥(ovl V i j) (ovlP V i j x) :=
    Work.Thom.relCohMap (ovlIncl V i j) (ovlP V i j x) (punct V x) (fun z hz => hz) ℤ 8
  have hIsoH : CategoryTheory.IsIso H := by
    have key := Work.Cohomology.capRel_excision_isIso (TopCat.of V.pt) (ovl V i j) (punct V x)
      hU (isOpen_punct V x) hcov 8 (fun z hz => hz)
    exact key
  have hHinj : Function.Injective H.hom := (ConcreteCategory.bijective_of_isIso H).1
  -- the transition germ is a germ diffeomorphism
  obtain ⟨hWop, hW0, hFc, hFnz, hdF, hbij⟩ := chartTrans_germ V i j hi hj
  have hF0 : germFun V i j x 0 = 0 := germFun_zero V i j x hi
  have hdet : LinearMap.det L.toLinearMap ≠ 0 := by
    intro hzero
    obtain ⟨v, hvk, hv0⟩ :=
      (Submodule.ne_bot_iff _).mp ((LinearMap.det_eq_zero_iff_ker_ne_bot).mp hzero)
    have hvk' : L v = 0 := by simpa using hvk
    exact hv0 (hbij.1 (by rw [hvk', map_zero]))
  let W : Set E8 := germSet V i j x
  let Wp : Set ↥W := {z : ↥W | (z : E8) ≠ 0}
  let FW : C(↥W, E8) := ⟨fun z => germFun V i j x (z : E8),
    continuousOn_iff_continuous_domRestrict.mp hFc⟩
  let inW : C(↥W, E8) := ⟨fun z => (z : E8), continuous_subtype_val⟩
  have hFWp : ∀ z ∈ Wp, FW z ∈ E8p := fun z hz => hFnz (z : E8) z.2 hz
  have hinWp : ∀ z ∈ Wp, inW z ∈ E8p := fun z hz => hz
  have hgpT : (Work.Thom.relCohMap FW Wp E8p hFWp ℤ 8).hom tau
      = s • (Work.Thom.relCohMap inW Wp E8p hinWp ℤ 8).hom tau := by
    change (Work.Thom.relCohMap FW Wp E8p hFWp ℤ 8).hom tau
      = (if 0 < LinearMap.det L.toLinearMap then (1 : ℤ) else -1)
        • (Work.Thom.relCohMap inW Wp E8p hinWp ℤ 8).hom tau
    exact germPullbackLocal hWop hW0 (germFun V i j x) hFc hF0 hFnz L hbij hdF hdet tau
  -- the translated charts restricted to the overlap
  let ciE : C(↥(ovl V i j), E8) := (chartTrans V i x hi).comp (ovlInclFst V i j)
  let cjE : C(↥(ovl V i j), E8) := (chartTrans V j x hj).comp (ovlInclSnd V i j)
  have hciP : ∀ z ∈ ovlP V i j x, ciE z ∈ E8p :=
    fun z hz => chartTrans_mem V i x hi (ovlInclFst V i j z) hz
  have hcjP : ∀ z ∈ ovlP V i j x, cjE z ∈ E8p :=
    fun z hz => chartTrans_mem V j x hj (ovlInclSnd V i j z) hz
  -- restriction of the two chart classes to the overlap
  have hRi : H.hom (chartCoh V i x hi)
      = (Work.Thom.relCohMap ciE (ovlP V i j x) E8p hciP ℤ 8).hom tau :=
    chartCoh_restrict (k := i) hi (ovlInclFst V i j) (fun z => rfl) (fun z hz => hz) hciP
  have hRj : H.hom (chartCoh V j x hj)
      = (Work.Thom.relCohMap cjE (ovlP V i j x) E8p hcjP ℤ 8).hom tau :=
    chartCoh_restrict (k := j) hj (ovlInclSnd V i j) (fun z => rfl) (fun z hz => hz) hcjP
  -- the two inclusions of the overlap into the germ set
  have hciWmem : ∀ z : ↥(ovl V i j), ciE z ∈ W := by
    intro z
    have h := germSet_mem V i j x hi z.2
    have h2 : (ovlInclFst V i j z : ↥(src V i)) = ⟨(z : V.pt), z.2.1⟩ := rfl
    show (chartTrans V i x hi) (ovlInclFst V i j z) ∈ W
    rw [h2]
    exact h
  let ciW : C(↥(ovl V i j), ↥W) := ⟨fun z => ⟨ciE z, hciWmem z⟩,
    Continuous.subtype_mk ciE.continuous hciWmem⟩
  have hciWp : ∀ z ∈ ovlP V i j x, ciW z ∈ Wp := fun z hz => hciP z hz
  have hincl_comp : inW.comp ciW = ciE := by
    apply ContinuousMap.ext; intro z; rfl
  have hFW_comp : FW.comp ciW = cjE := by
    apply ContinuousMap.ext
    intro z
    show germFun V i j x (ciE z) = cjE z
    rw [show ciE z = (chartTrans V i x hi) (ovlInclFst V i j z) from rfl,
      germFun_chartTrans V i j x hi (ovlInclFst V i j z)]
    rw [show cjE z = (chartTrans V j x hj) (ovlInclSnd V i j z) from rfl, chartTrans_apply]
    rfl
  -- the two pair conditions of the composites
  have hcompP1 : ∀ z ∈ ovlP V i j x, (inW.comp ciW) z ∈ E8p := fun z hz => hciP z hz
  have hcompP2 : ∀ z ∈ ovlP V i j x, (FW.comp ciW) z ∈ E8p := fun z hz => by
    rw [show (FW.comp ciW) z = cjE z from
      congrArg (fun (ψ : C(↥(ovl V i j), E8)) => ψ z) hFW_comp]
    exact hcjP z hz
  have hs : s * s = 1 := by
    change (if 0 < LinearMap.det L.toLinearMap then (1 : ℤ) else -1) *
      (if 0 < LinearMap.det L.toLinearMap then (1 : ℤ) else -1) = 1
    split_ifs <;> norm_num
  -- the restriction of `chartCoh` to the overlap, in terms of the germ
  have hstep1 : (Work.Thom.relCohMap ciE (ovlP V i j x) E8p hciP ℤ 8).hom tau
      = (Work.Thom.relCohMap ciW (ovlP V i j x) Wp hciWp ℤ 8).hom
          ((Work.Thom.relCohMap inW Wp E8p hinWp ℤ 8).hom tau) := by
    have h := Work.Thom.relCohMap_compA_apply (ovlP V i j x) Wp E8p ciW inW hciWp hinWp
      hcompP1 ℤ 8 tau
    have hmor : (Work.Thom.relCohMap (inW.comp ciW) (ovlP V i j x) E8p hcompP1 ℤ 8)
        = (Work.Thom.relCohMap ciE (ovlP V i j x) E8p hciP ℤ 8) :=
      Work.Thom.relCohMap_congrA (ovlP V i j x) E8p hincl_comp hcompP1 hciP ℤ 8
    rw [h, hmor]
  have hstep2 : (Work.Thom.relCohMap inW Wp E8p hinWp ℤ 8).hom tau
      = s • (Work.Thom.relCohMap FW Wp E8p hFWp ℤ 8).hom tau := by
    rw [hgpT, ← mul_zsmul, hs, one_zsmul]
  have hstep3 : s • (Work.Thom.relCohMap ciW (ovlP V i j x) Wp hciWp ℤ 8).hom
        ((Work.Thom.relCohMap FW Wp E8p hFWp ℤ 8).hom tau)
      = s • (Work.Thom.relCohMap cjE (ovlP V i j x) E8p hcjP ℤ 8).hom tau := by
    congr 1
    have h := Work.Thom.relCohMap_compA_apply (ovlP V i j x) Wp E8p ciW FW hciWp hFWp
      hcompP2 ℤ 8 tau
    have hmor : (Work.Thom.relCohMap (FW.comp ciW) (ovlP V i j x) E8p hcompP2 ℤ 8)
        = (Work.Thom.relCohMap cjE (ovlP V i j x) E8p hcjP ℤ 8) :=
      Work.Thom.relCohMap_congrA (ovlP V i j x) E8p hFW_comp hcompP2 hcjP ℤ 8
    rw [h]
    rw [hmor]
  -- the comparison of the two restricted chart classes
  have hcomp : (Work.Thom.relCohMap ciE (ovlP V i j x) E8p hciP ℤ 8).hom tau
      = s • (Work.Thom.relCohMap cjE (ovlP V i j x) E8p hcjP ℤ 8).hom tau := by
    rw [hstep1, hstep2]
    rw [map_zsmul]
    exact hstep3
  -- conclude by injectivity of the excision isomorphism
  have hfinal : H.hom (chartCoh V i x hi) = H.hom (s • chartCoh V j x hj) := by
    rw [hRi, map_zsmul, hRj]
    exact hcomp
  exact hHinj hfinal

end

end Work.ThomBordism.FrameSigns
