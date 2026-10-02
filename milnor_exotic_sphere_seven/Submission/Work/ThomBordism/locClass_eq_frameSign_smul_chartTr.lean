import Mathlib
import Submission.Work.ThomBordism.FrameSigns.chartCoh_pair_ne_zero
import Submission.Work.ThomBordism.FrameSigns.Assembly
import Submission.Work.PTGeometric.HOFEuclid
import Submission.Work.PTGeometric.HOFXfer
import Submission.Work.ThomBordism.locClass_chartTr_defs
import Submission.Work.ThomBordism.KeyLocal.tau_eq_pm_stdModelGen
import Submission.Work.ThomBordism.modelHalfOrientation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# The local fundamental class is the frame sign times the chart transfer

For a closed oriented smooth `8`-manifold `V`, a chart `i` of the finite cover and a point `x` of its
source, the local class of the fundamental class `V.c` at `x` and the chart transfer of the Euclidean
generator differ by a unit of `ℤ` depending only on the chart: there is a universal constant
`c₀ = ±1` such that

`locClass V x = c₀ · frameSign V i x • chartTr e x hx (eucFam 8 _ (e x))`.

The proof.  Let `T := chartTr e x hx (eucFam 8 _ (e x))`.  Both `T` and the local class generate the
local group `H₈(V, V∖{x}) ≅ ℤ`, so `locClass V x = k • T` with `k = ±1`
(`Work.ThomBordism.KeyLocal.exists_pm_smul_of_span_eq_top`, `Man8.c_fund`,
`Work.ThomBordism.span_chartTr_eucFam`).

Pairing with the chart class `FrameSigns.chartCoh` (recall `FrameSigns.pairVal = ⟨chartCoh, locClass⟩`)

  `pairVal = ⟨chartCoh, k • T⟩ = k · ⟨chartCoh, T⟩`,

and the **universal** value of `⟨chartCoh, T⟩` is computed in `chartCoh_pair_chartTrGen`: it is the
model constant `modelC0 = ⟨τ, eucFam 8 _ 0⟩ = dual0 (eucFam 8 _ 0) = ±1`.  The computation uses

* the naturality of the Kronecker pairing (`FrameSigns.relKronH_natural_srcIncl`,
  `FrameSigns.relKronH_natural_chartTrans`),
* the defining property of the chart class (`FrameSigns.chartCoh_spec`),
* the two identifications of the intermediate class `chartSrcZ` (`srcChain_Z` and `chartTrans_Z`).

Since `k` and `modelC0` are units, `pairVal = k · modelC0` is a unit too, and
`k = modelC0 · sign (pairVal)`; the claim follows.
-/

open CategoryTheory

namespace Work.ThomBordism

noncomputable section

open Work.PTGeometric.HOF

/-! ## The translated chart with the chart source as its domain

`FrameSigns.chartTrans` is a map out of `↥(FrameSigns.src V i)`, while the chart `(chartOf V i).1` has
source `(chartOf V i).1.source`; the two are equal by definition, but the elaborator does not unify
the corresponding `ContinuousMap` types, so we introduce the transparent abbreviation with the
`e.source` spelling. -/
abbrev chartTransSrc (V : Man8) (i : FrameSigns.ChartIdx V) (x : V.pt)
    (hx : x ∈ FrameSigns.src V i) :
    C(↥(FrameSigns.chartOf V i).1.source, EuclideanSpace ℝ (Fin 8)) :=
  FrameSigns.chartTrans V i x hx

/-- **The composite of the inverse chart with the translated chart is the translation by `-e x`.**
Both are maps of the chart target into `ℝ⁸`; their values at `z` are `e (e⁻¹ z) - e x = z - e x`. -/
lemma symmCore_chartTrans_eq (V : Man8) (i : FrameSigns.ChartIdx V) (x : V.pt)
    (hx : x ∈ FrameSigns.src V i) :
    (eSymmCore (W := TopCat.of V.pt) (N := 8) (FrameSigns.chartOf V i).1
      ≫ TopCat.ofHom (chartTransSrc V i x hx))
    = (Work.Cohomology.subtypeIncl (TopCat.of (EuclideanSpace ℝ (Fin 8)))
        (FrameSigns.chartOf V i).1.target
      ≫ (eucSub (-((FrameSigns.chartOf V i).1 x)) : TopCat.of (EuclideanSpace ℝ (Fin 8)) ⟶
          TopCat.of (EuclideanSpace ℝ (Fin 8)))) := by
  apply TopCat.ext
  intro z
  have h1 : (chartTransSrc V i x hx)
        ((eSymmCore (W := TopCat.of V.pt) (N := 8) (FrameSigns.chartOf V i).1) z)
      = FrameSigns.chartMap V i
          ((eSymmCore (W := TopCat.of V.pt) (N := 8) (FrameSigns.chartOf V i).1) z)
        - FrameSigns.chartMap V i x :=
    FrameSigns.chartTrans_apply V i x hx _
  have h2 : FrameSigns.chartMap V i
        ((eSymmCore (W := TopCat.of V.pt) (N := 8) (FrameSigns.chartOf V i).1) z)
      = ((z : ↥((FrameSigns.chartOf V i).1.target)) : EuclideanSpace ℝ (Fin 8)) := by
    show (FrameSigns.chartOf V i).1
      (((eSymmCore (W := TopCat.of V.pt) (N := 8) (FrameSigns.chartOf V i).1) z :
        ↥(FrameSigns.chartOf V i).1.source) : V.pt) = _
    exact (FrameSigns.chartOf V i).1.right_inv z.2
  show (chartTransSrc V i x hx)
        ((eSymmCore (W := TopCat.of V.pt) (N := 8) (FrameSigns.chartOf V i).1) z)
      = eucSub (-(FrameSigns.chartOf V i).1 x)
        (((z : ↥((FrameSigns.chartOf V i).1.target)) : EuclideanSpace ℝ (Fin 8)))
  rw [h1, h2]
  show ((z : ↥((FrameSigns.chartOf V i).1.target)) : EuclideanSpace ℝ (Fin 8))
      - (FrameSigns.chartMap V i x) = eucSub (-(FrameSigns.chartMap V i x))
        (((z : ↥((FrameSigns.chartOf V i).1.target)) : EuclideanSpace ℝ (Fin 8)))
  rw [eucSub_apply]
  abel

/-! ## The translation step -/

/-- The pair condition of the translation `z ↦ z - y` for the pair `({y}, {0})`. -/
lemma eucSub_pairCond (y : EuclideanSpace ℝ (Fin 8)) :
    ∀ z, z ∉ ({y} : Set (EuclideanSpace ℝ (Fin 8))) →
      eucSub (-y) z ∉ ({0} : Set (EuclideanSpace ℝ (Fin 8))) := by
  intro z hz h
  refine hz ?_
  have h1 : z + (-y) = 0 := h
  rwa [add_neg_eq_zero] at h1

/-- **The translation step**: `HOF.eucFam_translation` in the `({y}, {0})` spelling of the pair. -/
lemma eucSub_pair_zero (y : EuclideanSpace ℝ (Fin 8)) :
    RelHmapOf 8 (eucSub (-y)) ({y} : Set (EuclideanSpace ℝ (Fin 8)))
        ({0} : Set (EuclideanSpace ℝ (Fin 8))) (eucSub_pairCond y)
        (eucFam 8 (by norm_num) y)
      = eucFam 8 (by norm_num) 0 := by
  have htr : RelHmapOf 8 (eucSub (-y)) ({y} : Set (EuclideanSpace ℝ (Fin 8)))
      ({y + (-y)} : Set (EuclideanSpace ℝ (Fin 8))) (eucSub_mem (-y) y)
      (eucFam 8 (by norm_num) y) = eucFam 8 (by norm_num) (y + (-y)) :=
    eucFam_translation 8 (by norm_num) (-y) y
  have hcast : ((add_neg_cancel y) ▸ eucFam 8 (by norm_num) (y + (-y)) :
      Work.Orient.LocH (TopCat.of (EuclideanSpace ℝ (Fin 8))) 8 0) = eucFam 8 (by norm_num) 0 :=
    eucFam_cast (by norm_num) (N := 8) (add_neg_cancel y)
  have hrc := RelHmapOf_singleton_cast (Y := TopCat.of (EuclideanSpace ℝ (Fin 8))) (n := 8) (N := 8)
    (eucSub (-y)) ({y} : Set (EuclideanSpace ℝ (Fin 8))) (add_neg_cancel y)
    (eucSub_mem (-y) y) (eucSub_pairCond y) (eucFam 8 (by norm_num) y)
  rw [← hrc, htr]
  exact hcast

/-! ## The two identifications of the intermediate class -/

/-- **The translated chart carries `chartSrcZ` to the Euclidean generator at the origin.** -/
lemma chartTrans_Z (V : Man8) (i : FrameSigns.ChartIdx V) (x : V.pt)
    (hx : x ∈ FrameSigns.src V i) :
    (HomologicalComplex.homologyMap (FrameSigns.chartTransChain V i x hx) 8).hom (chartSrcZ V i x hx)
      = eucFam 8 (by norm_num) 0 := by
  have hpair : ∀ z : ↥(FrameSigns.src V i), z ∉ punctSet (TopCat.of V.pt) (FrameSigns.src V i) x →
      chartTransSrc V i x hx z ∉ ({0} : Set (EuclideanSpace ℝ (Fin 8))) :=
    fun z hz => FrameSigns.chartTrans_mem V i x hx z hz
  have hpairE : ∀ z : ↥((FrameSigns.chartOf V i).1.target), z ∉ punctSet (TopCat.of (Euc 8))
      (FrameSigns.chartOf V i).1.target ((FrameSigns.chartOf V i).1 x) →
      (eSymmCore (W := TopCat.of V.pt) (N := 8) (FrameSigns.chartOf V i).1) z
        ∉ punctSet (TopCat.of V.pt) (FrameSigns.src V i) x :=
    fun _z hz => eSymmCore_pair (W := TopCat.of V.pt) (N := 8) (FrameSigns.chartOf V i).1 x hx hz
  have hcmp : ∀ z : ↥((FrameSigns.chartOf V i).1.target), z ∉ punctSet (TopCat.of (Euc 8))
      (FrameSigns.chartOf V i).1.target ((FrameSigns.chartOf V i).1 x) →
      (eSymmCore (W := TopCat.of V.pt) (N := 8) (FrameSigns.chartOf V i).1
        ≫ TopCat.ofHom (chartTransSrc V i x hx)) z ∉ ({0} : Set (EuclideanSpace ℝ (Fin 8))) := by
    intro z hz
    show chartTransSrc V i x hx
      ((eSymmCore (W := TopCat.of V.pt) (N := 8) (FrameSigns.chartOf V i).1) z)
      ∉ ({0} : Set (EuclideanSpace ℝ (Fin 8)))
    exact hpair _ (hpairE z hz)
  have hsub : ∀ z : ↥((FrameSigns.chartOf V i).1.target), z ∉ punctSet (TopCat.of (Euc 8))
      (FrameSigns.chartOf V i).1.target ((FrameSigns.chartOf V i).1 x) →
      (Work.Cohomology.subtypeIncl (TopCat.of (EuclideanSpace ℝ (Fin 8)))
        (FrameSigns.chartOf V i).1.target) z
        ∉ ({(FrameSigns.chartOf V i).1 x} : Set (EuclideanSpace ℝ (Fin 8))) := fun _z hz => hz
  have hpairS : ∀ z : ↥((FrameSigns.chartOf V i).1.target), z ∉ punctSet (TopCat.of (Euc 8))
      (FrameSigns.chartOf V i).1.target ((FrameSigns.chartOf V i).1 x) →
      (Work.Cohomology.subtypeIncl (TopCat.of (EuclideanSpace ℝ (Fin 8)))
          (FrameSigns.chartOf V i).1.target
        ≫ eucSub (-((FrameSigns.chartOf V i).1 x))) z
        ∉ ({0} : Set (EuclideanSpace ℝ (Fin 8))) :=
    fun z hz => eucSub_pairCond ((FrameSigns.chartOf V i).1 x) z (hsub z hz)
  have hcomp1 := RelHmapOf_comp (n := 8)
    (f := eSymmCore (W := TopCat.of V.pt) (N := 8) (FrameSigns.chartOf V i).1)
    (g := TopCat.ofHom (chartTransSrc V i x hx))
    (K := punctSet (TopCat.of (Euc 8)) (FrameSigns.chartOf V i).1.target
      ((FrameSigns.chartOf V i).1 x))
    (K' := punctSet (TopCat.of V.pt) (FrameSigns.src V i) x)
    (K'' := ({0} : Set (EuclideanSpace ℝ (Fin 8)))) hpairE hpair hcmp
  have hcomp2 := RelHmapOf_comp (n := 8)
    (f := Work.Cohomology.subtypeIncl (TopCat.of (EuclideanSpace ℝ (Fin 8)))
      (FrameSigns.chartOf V i).1.target)
    (g := eucSub (-((FrameSigns.chartOf V i).1 x)))
    (K := punctSet (TopCat.of (Euc 8)) (FrameSigns.chartOf V i).1.target
      ((FrameSigns.chartOf V i).1 x))
    (K' := ({(FrameSigns.chartOf V i).1 x} : Set (EuclideanSpace ℝ (Fin 8))))
    (K'' := ({0} : Set (EuclideanSpace ℝ (Fin 8)))) hsub (eucSub_pairCond _) hpairS
  have hloc : (RelHmapOf 8 (Work.Cohomology.subtypeIncl (TopCat.of (EuclideanSpace ℝ (Fin 8)))
      (FrameSigns.chartOf V i).1.target)
      (punctSet (TopCat.of (Euc 8)) (FrameSigns.chartOf V i).1.target
        ((FrameSigns.chartOf V i).1 x))
      ({(FrameSigns.chartOf V i).1 x} : Set (EuclideanSpace ℝ (Fin 8))) hsub)
      (modelLoc V i x hx) = eucFam 8 (by norm_num) ((FrameSigns.chartOf V i).1 x) :=
    punctIso_excM_symm (TopCat.of (EuclideanSpace ℝ (Fin 8))) 8 (FrameSigns.chartOf V i).1.target
      (FrameSigns.chartOf V i).1.open_target ((FrameSigns.chartOf V i).1 x)
      ((FrameSigns.chartOf V i).1.map_source hx) isClosed_singleton
      (eucFam 8 (by norm_num) ((FrameSigns.chartOf V i).1 x))
  have hchain : (HomologicalComplex.homologyMap (FrameSigns.chartTransChain V i x hx) 8).hom
      = RelHmapOf 8 (TopCat.ofHom (chartTransSrc V i x hx))
          (punctSet (TopCat.of V.pt) (FrameSigns.src V i) x)
          ({0} : Set (EuclideanSpace ℝ (Fin 8))) hpair := rfl
  have hZ : chartSrcZ V i x hx
      = (RelHmapOf 8 (eSymmCore (W := TopCat.of V.pt) (N := 8) (FrameSigns.chartOf V i).1)
          (punctSet (TopCat.of (Euc 8)) (FrameSigns.chartOf V i).1.target
            ((FrameSigns.chartOf V i).1 x))
          (punctSet (TopCat.of V.pt) (FrameSigns.src V i) x) hpairE) (modelLoc V i x hx) := rfl
  have e1 := LinearMap.congr_fun hcomp1 (modelLoc V i x hx)
  have e2 := LinearMap.congr_fun (RelHmapOf_congr (symmCore_chartTrans_eq V i x hx) hcmp hpairS)
    (modelLoc V i x hx)
  have e3 := LinearMap.congr_fun hcomp2 (modelLoc V i x hx)
  rw [LinearMap.comp_apply, hloc] at e3
  refine (congrArg (fun f => f (chartSrcZ V i x hx)) hchain).trans ?_
  refine (congrArg (fun v => (RelHmapOf 8 (TopCat.ofHom (chartTransSrc V i x hx))
      (punctSet (TopCat.of V.pt) (FrameSigns.src V i) x)
      ({0} : Set (EuclideanSpace ℝ (Fin 8))) hpair) v) hZ).trans ?_
  refine e1.trans ?_
  refine e2.trans ?_
  refine e3.symm.trans ?_
  exact eucSub_pair_zero ((FrameSigns.chartOf V i).1 x)

/-! ## The universal pairing -/

/-- **The chart class pairs `1` against the chart transfer, up to the universal model constant.**

The pairing `⟨chartCoh, chartTr e x hx (eucFam (e x))⟩` of the chart class with the chart transfer of
the Euclidean generator is the *same* integer for every chart of every closed oriented smooth
`8`-manifold, namely `⟨τ, eucFam 8 _ 0⟩ = modelC0`.  The proof moves the pairing along the excision
of the chart source and the translated chart (`FrameSigns.relKronH_natural_srcIncl`,
`FrameSigns.relKronH_natural_chartTrans`), using the defining property of `chartCoh`
(`FrameSigns.chartCoh_spec`) and the two identifications `srcChain_Z`, `chartTrans_Z`. -/
lemma chartCoh_pair_chartTrGen (V : Man8) (i : FrameSigns.ChartIdx V) (x : V.pt)
    (hx : x ∈ FrameSigns.src V i) :
    (Work.Tubular.relKronH (TopCat.of V.pt) (FrameSigns.punct V x) 8)
        (FrameSigns.chartCoh V i x hx) (chartTrGen V i x hx) = modelC0 := by
  have h1 := FrameSigns.relKronH_natural_srcIncl V i hx (FrameSigns.chartCoh V i x hx)
    (chartSrcZ V i x hx)
  rw [srcChain_Z V i x hx] at h1
  rw [FrameSigns.chartCoh_spec V i hx] at h1
  rw [FrameSigns.relKronH_natural_chartTrans V i hx FrameSigns.tau (chartSrcZ V i x hx)] at h1
  rw [chartTrans_Z V i x hx] at h1
  rw [FrameSigns.tau_pair] at h1
  exact h1.symm

/-- The universal model constant is a unit: it is the value of the surjective functional `dual0` on
the generator `eucFam 8 _ 0`. -/
lemma modelC0_eq_one_or_neg_one : modelC0 = 1 ∨ modelC0 = -1 := by
  have hgen : Submodule.span ℤ ({eucFam 8 (by norm_num) 0} :
      Set (Work.Orient.LocH (TopCat.of (EuclideanSpace ℝ (Fin 8))) 8 0)) = ⊤ :=
    eucFam_gen 8 (by norm_num) 0
  have h := Work.PTGeometric.HOF.iso_gen_pm_one hgen (FrameSigns.e8).toLinearEquiv
  show FrameSigns.dual0 (eucFam 8 (by norm_num) 0) = 1 ∨ _
  rw [show FrameSigns.dual0 (eucFam 8 (by norm_num) 0)
      = (FrameSigns.e8).toLinearEquiv (eucFam 8 (by norm_num) 0) from rfl]
  exact h

/-! ## The target -/

theorem locClass_eq_frameSign_smul_chartTr :
    ∃ c₀ : ℤ, (c₀ = 1 ∨ c₀ = -1) ∧
      ∀ (V : Work.ThomBordism.Man8) (i : Work.ThomBordism.FrameSigns.ChartIdx V) (x : V.pt)
        (hx : x ∈ Work.ThomBordism.FrameSigns.src V i),
        Work.Orient.locClass (TopCat.of V.pt) 8 V.c x
          = (c₀ * (if 0 < Work.ThomBordism.FrameSigns.pairVal V i x hx then (1 : ℤ) else -1)) •
              Work.PTGeometric.HOF.chartTr (W := TopCat.of V.pt) (N := 8)
                ((Work.ThomBordism.FrameSigns.chartOf V i).1) x hx
                (Work.PTGeometric.HOF.eucFam 8 (by norm_num)
                  ((Work.ThomBordism.FrameSigns.chartOf V i).1 x)) := by
  refine ⟨modelC0, modelC0_eq_one_or_neg_one, ?_⟩
  intro V i x hx
  have hccgen : Submodule.span ℤ ({Work.Orient.locClass (TopCat.of V.pt) 8 V.c x} :
      Set (Work.Orient.LocH (TopCat.of V.pt) 8 x)) = ⊤ := V.c_fund x
  have hTgen : Submodule.span ℤ ({chartTrGen V i x hx} :
      Set (Work.Orient.LocH (TopCat.of V.pt) 8 x)) = ⊤ := by
    show Submodule.span ℤ ({(Work.PTGeometric.HOF.chartTr (W := TopCat.of V.pt) (N := 8)
      (Work.ThomBordism.FrameSigns.chartOf V i).1 x hx
      (Work.PTGeometric.HOF.eucFam 8 (by norm_num)
        ((Work.ThomBordism.FrameSigns.chartOf V i).1 x)))} :
        Set (Work.Orient.LocH (TopCat.of V.pt) 8 x)) = ⊤
    exact span_chartTr_eucFam (W := TopCat.of V.pt) (N := 8) (by norm_num)
      (FrameSigns.chartOf V i).1 x hx
  obtain ⟨ecc⟩ := Work.Cohomology.localHomology 8 (by norm_num) V.pt x
  obtain ⟨k, hkpm, hkT⟩ := KeyLocal.exists_pm_smul_of_span_eq_top ⟨ecc.toLinearEquiv⟩ hccgen hTgen
  have hpair : FrameSigns.pairVal V i x hx = k * modelC0 := by
    show (Work.Tubular.relKronH (TopCat.of V.pt) (FrameSigns.punct V x) 8)
        (FrameSigns.chartCoh V i x hx) (Work.Orient.locClass (TopCat.of V.pt) 8 V.c x)
      = k * modelC0
    rw [hkT, map_zsmul, chartCoh_pair_chartTrGen V i x hx]
    simp only [zsmul_eq_mul, Int.cast_id]
  have hpm : FrameSigns.pairVal V i x hx = 1 ∨ FrameSigns.pairVal V i x hx = -1 := by
    rw [hpair]
    rcases hkpm with h | h <;> rcases modelC0_eq_one_or_neg_one with h' | h' <;>
      rw [h, h'] <;> norm_num
  have hs : (if 0 < FrameSigns.pairVal V i x hx then (1 : ℤ) else -1)
      = FrameSigns.pairVal V i x hx := by
    rcases hpm with h | h <;> rw [h] <;> norm_num
  have hm2 : modelC0 * modelC0 = 1 := by
    rcases modelC0_eq_one_or_neg_one with h | h <;> rw [h] <;> norm_num
  have hk_coeff : k = modelC0 * (if 0 < FrameSigns.pairVal V i x hx then (1 : ℤ) else -1) := by
    rw [hs]
    calc k = k * (modelC0 * modelC0) := by rw [hm2, mul_one]
      _ = (k * modelC0) * modelC0 := by ring
      _ = FrameSigns.pairVal V i x hx * modelC0 := by rw [← hpair]
      _ = modelC0 * FrameSigns.pairVal V i x hx := by ring
  show Work.Orient.locClass (TopCat.of V.pt) 8 V.c x
      = (modelC0 * (if 0 < FrameSigns.pairVal V i x hx then (1 : ℤ) else -1)) •
          chartTrGen V i x hx
  rw [show Work.Orient.locClass (TopCat.of V.pt) 8 V.c x = _ from hkT, hk_coeff]

end

end Work.ThomBordism
