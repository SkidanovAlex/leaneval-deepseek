import Mathlib
import Submission.Work.Thom.BundleIsoGauge

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
# The piece map and the chart gauge of a *real* isomorphism of the realifications

This module is the orientation-reversing companion of
`Submission/Work/Thom/BundleIsoGauge.lean`.  There, for two *complex* bundles `Z`, `Z'` and a
**complex** isomorphism `e : Z ≅ Z'`, one has the gauge `Work.Thom.isoGauge` comparing the chart `i`
of `realification Z` with the chart `i'` of `realification Z'` through `e`, together with the
intertwining identity `Work.Thom.isoGauge_compHom` and the positivity of its real determinant
(`Work.Thom.det_isoGauge_pos`).

Here the input is instead a **real** isomorphism `e : realification Z ≅ realification Z'` (an
arbitrary orientation of the real bundle, with no complex linearity), and the analogous objects
are built:

* `Work.Gen.realPieceMap` — the induced map of the pieces over `W ⊆ B` of the two realifications;
* `Work.Gen.realTotalMap` — the induced map of total spaces;
* `Work.Gen.realIsoGauge` — the fibrewise gauge
  `ℝ^{2m} --covE⁻¹--> ℂᵐ --Z.coordChange--> ℂᵐ --e.hom x--> ℂᵐ --Z'.coordChange--> ℂᵐ --covE--> ℝ^{2m}`,
  with defining formula `Work.Gen.realIsoGauge_apply`.

Its real determinant is that of the conjugation of `e.hom x` by the chart changes, hence has the
*sign* of `det (e.hom x)`; for an everywhere negative fibrewise determinant this is the
orientation-reversing case, which is what reverses the Euler class.
-/

namespace Work.Gen

open Work.Thom Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {m : ℕ} {ι ι' : Type}

/-! ## The piece map of a real isomorphism -/

/-- **The map of the pieces over `W ⊆ B` induced by a real isomorphism of two real bundles**:
`p ↦ (p.1.1, e.hom p.1.1 p.1.2)`.  On the realifications of complex bundles this is the map used
to compare the two chart Thom classes; it is the "total map" of `e` restricted to the piece. -/
def realPieceMap {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Z : RealBundle B F ι) (Z' : RealBundle B F ι') (e : BundleIso Z Z') (W : Set B) :
    C(↥(Z.proj ⁻¹' W), ↥(Z'.proj ⁻¹' W)) :=
  ⟨fun p => ⟨e.toTotalSpace p.1, p.2⟩,
    Continuous.subtype_mk (e.continuous_hom.comp continuous_subtype_val) (fun p => p.2)⟩

@[simp] theorem realPieceMap_apply {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Z : RealBundle B F ι) (Z' : RealBundle B F ι') (e : BundleIso Z Z') (W : Set B)
    (p : ↥(Z.proj ⁻¹' W)) :
    ((realPieceMap Z Z' e W p : ↥(Z'.proj ⁻¹' W)) : Z'.TotalSpace) = e.toTotalSpace p.1 := rfl

/-- `Work.Gen.realPieceMap` carries the complement of the zero section into the complement. -/
theorem realPieceMap_mem {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Z : RealBundle B F ι) (Z' : RealBundle B F ι') (e : BundleIso Z Z') (W : Set B) :
    ∀ p ∈ pieceZero Z W, realPieceMap Z Z' e W p ∈ pieceZero Z' W := by
  intro p hp
  show (show F from ((realPieceMap Z Z' e W p : ↥(Z'.proj ⁻¹' W)) : Z'.TotalSpace).2) ≠ 0
  have h1 : (show F from ((realPieceMap Z Z' e W p : ↥(Z'.proj ⁻¹' W)) : Z'.TotalSpace).2)
      = e.hom p.1.1 p.1.2 := rfl
  rw [h1]
  exact e.hom_ne_zero hp

/-- The piece map commutes with the inclusions of the pieces (naturality in `W`). -/
theorem pieceIncl_comp_realPieceMap {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Z : RealBundle B F ι) (Z' : RealBundle B F ι')
    (e : BundleIso Z Z') {V U : Set B} (hVU : V ⊆ U) :
    (pieceIncl Z' V U hVU).comp (realPieceMap Z Z' e V)
      = (realPieceMap Z Z' e U).comp (pieceIncl Z V U hVU) := by
  apply ContinuousMap.ext
  intro q
  apply Subtype.ext
  simp only [ContinuousMap.comp_apply, pieceIncl_apply, realPieceMap_apply]

/-! ## The total-space map of a real isomorphism -/

/-- **The map of total spaces induced by a real bundle isomorphism**, as a `ContinuousMap`. -/
def realTotalMap {F F' : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (Z : RealBundle B F ι) (Z' : RealBundle B F' ι') (e : BundleIso Z Z') :
    C(Z.TotalSpace, Z'.TotalSpace) :=
  ⟨e.toTotalSpace, e.continuous_hom⟩

@[simp] theorem realTotalMap_apply {F F' : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (Z : RealBundle B F ι) (Z' : RealBundle B F' ι') (e : BundleIso Z Z')
    (p : Z.TotalSpace) : realTotalMap Z Z' e p = e.toTotalSpace p := rfl

/-- The total-space map restricts to the piece map over `Set.univ`. -/
theorem realTotalMap_comp_subtype {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Z : RealBundle B F ι) (Z' : RealBundle B F ι') (e : BundleIso Z Z') :
    (realTotalMap Z Z' e).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(Z.proj ⁻¹' (Set.univ : Set B)), Z.TotalSpace))
      = (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(Z'.proj ⁻¹' (Set.univ : Set B)), Z'.TotalSpace)).comp
          (realPieceMap Z Z' e Set.univ) := by
  apply ContinuousMap.ext
  intro q
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, realPieceMap_apply,
    realTotalMap_apply]

/-! ## The chart gauge of a real isomorphism -/

/-- **The fibrewise linear gauge comparing the chart `i` of `realification Z` with the chart `i'`
of `realification Z'` through a real isomorphism `e` of the realifications.**  It is the composite

`ℝ^{2m} --covE⁻¹--> ℂᵐ --(Z_R).coordChange--> ℂᵐ --e.hom x--> ℂᵐ --(Z'_R).coordChange--> ℂᵐ --covE--> ℝ^{2m}`,

the real-analogue of `Work.Thom.isoGauge` with the complex-linear middle factor replaced by the
arbitrary real-linear one `e.hom x`. -/
def realIsoGauge (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : BundleIso (realification Z) (realification Z')) (i : ι) (i' : ι')
    {W : Set B} (_hWi : W ⊆ (realification Z).baseSet i)
    (_hWi' : W ⊆ (realification Z').baseSet i') : ↥W → Gauge (2 * m) :=
  fun x =>
    (covE (m := m) : EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (2 * m))).comp
      (((realification Z').coordChange ((realification Z').indexAt (x : B)) i' (x : B)).comp
        ((LinearMap.toContinuousLinearMap (𝕜 := ℝ)
            (show EuclideanSpace ℂ (Fin m) →ₗ[ℝ] EuclideanSpace ℂ (Fin m) from
              e.hom (x : B))).comp
          (((realification Z).coordChange i ((realification Z).indexAt (x : B)) (x : B)).comp
            ((covE (m := m)).symm :
              EuclideanSpace ℝ (Fin (2 * m)) →L[ℝ] EuclideanSpace ℂ (Fin m)))))

/-- The defining formula of `Work.Gen.realIsoGauge`. -/
theorem realIsoGauge_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : BundleIso (realification Z) (realification Z')) (i : ι) (i' : ι')
    {W : Set B} (hWi : W ⊆ (realification Z).baseSet i)
    (hWi' : W ⊆ (realification Z').baseSet i') (x : ↥W)
    (v : EuclideanSpace ℝ (Fin (2 * m))) :
    realIsoGauge Z Z' e i i' hWi hWi' x v =
      (covE (m := m) : EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (2 * m)))
        ((realification Z').coordChange ((realification Z').indexAt (x : B)) i' (x : B)
          (e.hom (x : B)
            ((realification Z).coordChange i ((realification Z).indexAt (x : B)) (x : B)
              ((covE (m := m)).symm v)))) := by
  rw [realIsoGauge]
  rfl

end

end Work.Gen
