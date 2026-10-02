import Mathlib
import Submission.Work.ThomBordism.FrameSigns.chartCoh_pair_ne_zero
import Submission.Work.ThomBordism.FrameSigns.Assembly
import Submission.Work.ThomBordism.FrameSigns.chartCoh_compare
import Submission.Work.PTGeometric.HOFEuclid
import Submission.Work.PTGeometric.HOFXfer
import Submission.Work.ThomBordism.chartTr_relHmapOf
import Submission.Work.ThomBordism.relHmapOf_injective_of_localHomeo

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
# The comparison of the local fundamental class with the chart transfer

For a closed oriented smooth `8`-manifold `V`, a chart `i` of the finite cover and a point
`x ∈ src V i`, this file sets up the data used to compare

* the local fundamental class `locClass (TopCat.of V.pt) 8 V.c x`, and
* the chart transfer `chartTr e x hx (eucFam 8 _ (e x))` of the Euclidean generator along the chart
  `e = (chartOf V i).1`.

The comparison is made through the relative Kronecker pairing with the chart class
`FrameSigns.chartCoh`, whose defining property (`chartCoh_spec`) is that its image under the
excision isomorphism of the chart source is the pullback of the model class `τ` along the translated
chart.  The main computational content is

* `srcChain_Z` (proved here) and `chartTrans_Z` (in `locClass_chartTr_chartTrans`): the
  intermediate class `chartSrcZ` (the localisation of the Euclidean generator to the chart target,
  pushed forward along the inverse chart) maps to the chart transfer under the excision of the chart
  source, and to `eucFam 8 _ 0` under the translated chart `chartTrans`.

Both are pure `RelHmapOf`-bookkeeping: the composite of the inverse chart and the translated chart is
the translation `eucSub (-e x)` (written on the target), so the second computation reduces to
`FrameSigns.punctIso_excM_symm` and `HOF.eucFam_translation`.
-/

open CategoryTheory

namespace Work.ThomBordism

noncomputable section

open Work.PTGeometric.HOF

/-- The model constant of the comparison: the value of the model class on the model generator. -/
noncomputable def modelC0 : ℤ := FrameSigns.dual0 (eucFam 8 (by norm_num) 0)

/-- The localisation of the Euclidean generator at the image point to the chart target. -/
noncomputable def modelLoc (V : Man8) (i : FrameSigns.ChartIdx V) (x : V.pt)
    (hx : x ∈ FrameSigns.src V i) :
    Work.Orient.RelH (TopCat.of ↥((FrameSigns.chartOf V i).1.target)) 8
      (punctSet (TopCat.of (Euc 8)) (FrameSigns.chartOf V i).1.target
        ((FrameSigns.chartOf V i).1 x)) :=
  (punctIso (TopCat.of (Euc 8)) 8 (FrameSigns.chartOf V i).1.target
      (FrameSigns.chartOf V i).1.open_target ((FrameSigns.chartOf V i).1 x)
      ((FrameSigns.chartOf V i).1.map_source hx) isClosed_singleton).symm
    (eucFam 8 (by norm_num) ((FrameSigns.chartOf V i).1 x))

/-- The chart-source class whose chart image is the Euclidean generator: the localisation of the
Euclidean generator to the chart target, pushed forward along the inverse chart. -/
noncomputable def chartSrcZ (V : Man8) (i : FrameSigns.ChartIdx V) (x : V.pt)
    (hx : x ∈ FrameSigns.src V i) :
    Work.Orient.RelH (TopCat.of ↥(FrameSigns.src V i)) 8
      (punctSet (TopCat.of V.pt) (FrameSigns.src V i) x) :=
  RelHmapOf 8 (eSymmCore (W := TopCat.of V.pt) (N := 8) (FrameSigns.chartOf V i).1)
    (punctSet (TopCat.of (Euc 8)) (FrameSigns.chartOf V i).1.target
      ((FrameSigns.chartOf V i).1 x))
    (punctSet (TopCat.of V.pt) (FrameSigns.src V i) x)
    (fun _z hz => eSymmCore_pair (W := TopCat.of V.pt) (N := 8) (FrameSigns.chartOf V i).1 x hx hz)
    (modelLoc V i x hx)

/-- The chart transfer of the Euclidean generator at `x`. -/
noncomputable def chartTrGen (V : Man8) (i : FrameSigns.ChartIdx V) (x : V.pt)
    (hx : x ∈ FrameSigns.src V i) : Work.Orient.LocH (TopCat.of V.pt) 8 x :=
  chartTr (W := TopCat.of V.pt) (N := 8) (FrameSigns.chartOf V i).1 x hx
    (eucFam 8 (by norm_num) ((FrameSigns.chartOf V i).1 x))

/-- **The excision of the chart source carries `chartSrcZ` to the chart transfer.** -/
lemma srcChain_Z (V : Man8) (i : FrameSigns.ChartIdx V) (x : V.pt)
    (hx : x ∈ FrameSigns.src V i) :
    (HomologicalComplex.homologyMap (FrameSigns.chartSrcChain V i x hx) 8).hom (chartSrcZ V i x hx)
      = chartTrGen V i x hx := by
  have hpairS : ∀ z, z ∉ punctSet (TopCat.of V.pt) (FrameSigns.src V i) x →
      (TopCat.ofHom (FrameSigns.srcIncl V i)) z ∉ ({x} : Set V.pt) := fun _z hz => hz
  have hpairE : ∀ z, z ∉ punctSet (TopCat.of (Euc 8)) (FrameSigns.chartOf V i).1.target
      ((FrameSigns.chartOf V i).1 x) →
      (eSymmCore (W := TopCat.of V.pt) (N := 8) (FrameSigns.chartOf V i).1) z ∉
        punctSet (TopCat.of V.pt) (FrameSigns.src V i) x :=
    fun _z hz => eSymmCore_pair (W := TopCat.of V.pt) (N := 8) (FrameSigns.chartOf V i).1 x hx hz
  have hpairA : ∀ z, z ∉ punctSet (TopCat.of (Euc 8)) (FrameSigns.chartOf V i).1.target
      ((FrameSigns.chartOf V i).1 x) →
      (eSymmA (W := TopCat.of V.pt) (N := 8) (FrameSigns.chartOf V i).1) z ∉ ({x} : Set V.pt) :=
    fun _z hz => eSymmA_pair (W := TopCat.of V.pt) (N := 8) (FrameSigns.chartOf V i).1 x hx hz
  have hcomp := RelHmapOf_comp (n := 8)
    (f := eSymmCore (W := TopCat.of V.pt) (N := 8) (FrameSigns.chartOf V i).1)
    (g := TopCat.ofHom (FrameSigns.srcIncl V i))
    (K := punctSet (TopCat.of (Euc 8)) (FrameSigns.chartOf V i).1.target
      ((FrameSigns.chartOf V i).1 x))
    (K' := punctSet (TopCat.of V.pt) (FrameSigns.src V i) x)
    (K'' := ({x} : Set V.pt)) hpairE hpairS hpairA
  have hmap : eSymmCore (W := TopCat.of V.pt) (N := 8) (FrameSigns.chartOf V i).1
      ≫ TopCat.ofHom (FrameSigns.srcIncl V i)
      = eSymmA (W := TopCat.of V.pt) (N := 8) (FrameSigns.chartOf V i).1 := by
    rw [eSymmA_eq]; rfl
  have h1 := LinearMap.congr_fun hcomp (modelLoc V i x hx)
  have h3 : (RelHmapOf 8 (eSymmCore (W := TopCat.of V.pt) (N := 8) (FrameSigns.chartOf V i).1
        ≫ TopCat.ofHom (FrameSigns.srcIncl V i))
        (punctSet (TopCat.of (Euc 8)) (FrameSigns.chartOf V i).1.target
          ((FrameSigns.chartOf V i).1 x))
        ({x} : Set V.pt) hpairA) (modelLoc V i x hx)
      = (RelHmapOf 8 (eSymmA (W := TopCat.of V.pt) (N := 8) (FrameSigns.chartOf V i).1)
        (punctSet (TopCat.of (Euc 8)) (FrameSigns.chartOf V i).1.target
          ((FrameSigns.chartOf V i).1 x))
        ({x} : Set V.pt) hpairA) (modelLoc V i x hx) :=
    LinearMap.congr_fun (RelHmapOf_congr hmap hpairA hpairA) (modelLoc V i x hx)
  exact h1.trans h3

end

end Work.ThomBordism
