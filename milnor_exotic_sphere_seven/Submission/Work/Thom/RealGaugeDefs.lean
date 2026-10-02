import Mathlib
import Submission.Work.Thom.realThomClassOf_natural
import Submission.Work.Gen.RealIsoGaugeDefs
import Submission.Work.Thom.isOrientedOver_of_det_pos

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The chart gauge of an isomorphism of two *real* bundles with fibre `ℝⁿ`

This module is the real companion of `Submission/Work/Gen/RealIsoGaugeDefs.lean`, which treats an
isomorphism of the *realifications* of two complex bundles (with fibre `EuclideanSpace ℂ (Fin m)`).
Here the bundles are directly real bundles with fibre `EuclideanSpace ℝ (Fin n)` -- in particular
`n` may be odd -- and the isomorphism `e` carries an arbitrary real-linear fibrewise isomorphism.

For such an `e`, and for a chart `i` of `Z`, a chart `i'` of `Z'` and a set
`W ⊆ Z.baseSet i ∩ Z'.baseSet i'`, we build the fibrewise gauge

* `Work.Thom.realGaugeIso Z Z' e i i' hWi hWi' : ↥W → Gauge n`, the composite

  `ℝⁿ --(Z.coordChange i)--> ℝⁿ --e.hom x--> ℝⁿ --(Z'.coordChange i')--> ℝⁿ`

  of the two chart changes and the isomorphism, with defining formula
  `Work.Thom.realGaugeIso_apply`;

* `Work.Thom.chartPairCover Z Z' : ι × ι' → Set B`, the common refinement of the two chart covers,
  `(i, i') ↦ Z.baseSet i ∩ Z'.baseSet i'`.

The gauge is the difference between the two chart trivialisations read through `e`; the local input
of the isomorphism-invariance of the Thom class is that an *orientation preserving* gauge fixes the
model class `Work.Thom.Mpun` (`Work.Thom.Mpun_gaugeEnd_invariant`).  The three facts about
`realGaugeIso` that this requires -- continuity, the intertwining identity with the chart
homeomorphisms, and the positivity of its determinant -- are the content of
`Submission/Work/Thom/realGaugeIso_facts.lean`.
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {n : ℕ} {ι ι' : Type}

/-- **The fibrewise linear gauge comparing the chart `i` of `Z` with the chart `i'` of `Z'`
through the bundle isomorphism `e`**, on `W ⊆ Z.baseSet i ∩ Z'.baseSet i'`. -/
def realGaugeIso (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι)
    (Z' : RealBundle B (EuclideanSpace ℝ (Fin n)) ι')
    (e : BundleIso Z Z') (i : ι) (i' : ι') {W : Set B}
    (_hWi : W ⊆ Z.baseSet i) (_hWi' : W ⊆ Z'.baseSet i') : ↥W → Gauge n :=
  fun x =>
    (Z'.coordChange (Z'.indexAt (x : B)) i' (x : B)).comp
      ((LinearMap.toContinuousLinearMap (𝕜 := ℝ)
          (show EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) from
            e.hom (x : B))).comp
        (Z.coordChange i (Z.indexAt (x : B)) (x : B)))

/-- The defining formula of `Work.Thom.realGaugeIso`. -/
theorem realGaugeIso_apply (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι)
    (Z' : RealBundle B (EuclideanSpace ℝ (Fin n)) ι')
    (e : BundleIso Z Z') (i : ι) (i' : ι') {W : Set B}
    (hWi : W ⊆ Z.baseSet i) (hWi' : W ⊆ Z'.baseSet i') (x : ↥W)
    (v : EuclideanSpace ℝ (Fin n)) :
    realGaugeIso Z Z' e i i' hWi hWi' x v =
      Z'.coordChange (Z'.indexAt (x : B)) i' (x : B)
        (e.hom (x : B) (Z.coordChange i (Z.indexAt (x : B)) (x : B) v)) := by
  rw [realGaugeIso]
  rfl

/-- **The common refinement of the two chart covers** of two real bundles over a common base,
indexed by `ι × ι'`. -/
def chartPairCover (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι)
    (Z' : RealBundle B (EuclideanSpace ℝ (Fin n)) ι') : ι × ι' → Set B :=
  fun p => Z.baseSet p.1 ∩ Z'.baseSet p.2

@[simp] theorem chartPairCover_apply (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι)
    (Z' : RealBundle B (EuclideanSpace ℝ (Fin n)) ι') (p : ι × ι') :
    chartPairCover Z Z' p = Z.baseSet p.1 ∩ Z'.baseSet p.2 := rfl

/-- The chart classes of `Z` and of `Z'` and the isomorphism `e` interact through the gauge; the
statement below records the shape of the resulting comparison of local Thom data. -/
theorem realGaugeIso_chartPairCover_subset_left
    (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι)
    (Z' : RealBundle B (EuclideanSpace ℝ (Fin n)) ι') (p : ι × ι') :
    chartPairCover Z Z' p ⊆ Z.baseSet p.1 := Set.inter_subset_left

theorem realGaugeIso_chartPairCover_subset_right
    (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι)
    (Z' : RealBundle B (EuclideanSpace ℝ (Fin n)) ι') (p : ι × ι') :
    chartPairCover Z Z' p ⊆ Z'.baseSet p.2 := Set.inter_subset_right

end

end Work.Thom
