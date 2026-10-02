import Mathlib
import Submission.Work.Thom.isOrientedOver_of_det_pos
import Submission.Work.Thom.Orientation.Reflection
import Submission.Work.Thom.Orientation.step_fibRefl
import Submission.Work.Thom.Orientation.pairDelta_flip_one

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The orientation character of the punctured model class: the reflection acts by `-1`

`Work.Thom.Mpun n Y` is the model Thom class of the punctured trivial bundle of rank `n` over `Y`.
Its *orientation character* — the action of a fibre automorphism — is computed here for the
reflection `Work.Thom.Orientation.fibRefl n Y`, `(y, v) ↦ (y, flipFst n v)`, which negates the first
coordinate of the fibre:

* `Work.Thom.Orientation.Mn_fibRefl` — the reflection acts by `-1` on the sphere-bundle model class
  `Work.Thom.Mn n Y`, by induction on `n`: the rank-one case `Mn_one_fibRefl` is the computation of
  the connecting homomorphism of `(Y × ℝ¹, Y × S⁰)` (`pairDelta_flip_one`), and the inductive step
  is the naturality `step_fibRefl` of `Work.Thom.step` under the reflection together with the
  linearity `step_neg` of the step;
* `Work.Thom.Orientation.Mpun_fibRefl` — the same for the punctured model class `Mpun n Y`, obtained
  from the sphere-bundle statement through the isomorphism `Work.Thom.bijective_jMap`;
* `Work.Thom.Orientation.Mpun_gaugeEnd_neg` — **the orientation character**: a gauge `D` with
  `det (D y) < 0` everywhere acts by `-1` on `Mpun n Y`.

The reduction of the last statement to the fixed reflection uses that a determinant-positive gauge
fixes `Mpun` (`Work.Thom.Mpun_gaugeEnd_invariant`) and that `det (flipFst n) = -1`
(`Work.Thom.Orientation.flipFst_det`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace Work.Thom.Orientation

open Work.Thom

noncomputable section

/-! ## Linearity of the model induction -/

/-- Linearity of `stepSph`: it is the unique preimage under the cap map of a linear map. -/
theorem stepSph_neg (n : ℕ) {Y : Type} [TopologicalSpace Y]
    (τ : RelCoh ℤ n (Y × EuclideanSpace ℝ (Fin n)) (Sph Y n)) :
    stepSph Y n (-τ) = - stepSph Y n τ := by
  apply (CleanA.capRelCohIso Y n n).1
  rw [map_neg, stepSph_spec Y n (-τ), stepSph_spec Y n τ, stepDisc, stepDisc, map_neg]

/-- Linearity of the inductive step `step`. -/
theorem step_neg (n : ℕ) {Y : Type} [TopologicalSpace Y]
    (τ : RelCoh ℤ n (Y × EuclideanSpace ℝ (Fin n)) (Sph Y n)) :
    step Y n (-τ) = - step Y n τ := by
  rw [step, step, stepSph_neg]
  simp only [map_neg]

/-! ## The rank-one base case -/

/-- **The rank-one base case of the orientation character**: the reflection acts by `-1` on the
sphere-bundle model class `Mn 1 Y`.  Immediate from `pairDelta_flip_one`. -/
theorem Mn_one_fibRefl {Y : Type} [TopologicalSpace Y] :
    (relCohMap (fibRefl 1 Y) (Sph Y 1) (Sph Y 1) (fibRefl_mem_sph 1 Y) ℤ 1).hom (Mn 1 Y)
      = - Mn 1 Y := by
  show (relCohMap (fibRefl 1 Y) (Sph Y 1) (Sph Y 1) (fibRefl_mem_sph 1 Y) ℤ 1).hom
      (step Y 0 (Mn 0 Y)) = - step Y 0 (Mn 0 Y)
  rw [step]
  rw [pairDeltaNatural_restrict (fibRefl 1 Y) (Sph Y 1) (Sph Y 1) (fibRefl_mem_sph 1 Y) 0
      ((CohMap ((prodSubsetHomeoA Y (EuclideanSpace ℝ (Fin (0+1))) (mSph (0+1))).symm :
          C(↥(Sph Y 1), Y × MSph (0+1))) ℤ 0).hom
        ((relToAbs ℤ (SphB Y 0) 0).hom (stepSph Y 0 (Mn 0 Y))))]
  have h := pairDelta_flip_one
    ((CohMap ((prodSubsetHomeoA Y (EuclideanSpace ℝ (Fin (0+1))) (mSph (0+1))).symm :
        C(↥(Sph Y 1), Y × MSph (0+1))) ℤ 0).hom
      ((relToAbs ℤ (SphB Y 0) 0).hom (stepSph Y 0 (Mn 0 Y))))
  rw [map_add] at h
  exact eq_neg_of_add_eq_zero_left h

/-! ## The induction -/

/-- **The orientation character of the sphere-bundle model class**: the reflection acts by `-1` on
`Mn n Y`.  Induction on `n`, with the rank-one case `Mn_one_fibRefl` and the naturality
`step_fibRefl` of `Work.Thom.step`. -/
theorem Mn_fibRefl (n : ℕ) (hn : 1 ≤ n) {Y : Type} [TopologicalSpace Y] :
    (relCohMap (fibRefl n Y) (Sph Y n) (Sph Y n) (fibRefl_mem_sph n Y) ℤ n).hom (Mn n Y)
      = - Mn n Y := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      exact Mn_one_fibRefl
    · have hk1 : 1 ≤ k := hkpos
      show (relCohMap (fibRefl (k+1) Y) (Sph Y (k+1)) (Sph Y (k+1))
          (fibRefl_mem_sph (k+1) Y) ℤ (k+1)).hom (step Y k (Mn k Y)) = - step Y k (Mn k Y)
      rw [step_fibRefl k hk1 (Mn k Y), ih hk1, step_neg]

/-- **The orientation character of the punctured model class**: the reflection acts by `-1` on
`Mpun n Y`.  Transfer of `Mn_fibRefl` along the pair isomorphism `Work.Thom.bijective_jMap`. -/
theorem Mpun_fibRefl (n : ℕ) (hn : 1 ≤ n) {Y : Type} [TopologicalSpace Y] :
    (relCohMap (fibRefl n Y) (Punct Y n) (Punct Y n) (fibRefl_mem_punct n Y) ℤ n).hom (Mpun n Y)
      = - Mpun n Y := by
  have hj : Function.Injective ((relCohMap (ContinuousMap.id (Y × EuclideanSpace ℝ (Fin n)))
      (Sph Y n) (Punct Y n) (mem_Sph_punct Y n) ℤ n).hom) := (bijective_jMap Y n n).1
  have hsq : CategoryTheory.CategoryStruct.comp
        (relCohMap (fibRefl n Y) (Punct Y n) (Punct Y n) (fibRefl_mem_punct n Y) ℤ n)
        (relCohMap (ContinuousMap.id (Y × EuclideanSpace ℝ (Fin n))) (Sph Y n) (Punct Y n)
          (mem_Sph_punct Y n) ℤ n)
      = CategoryTheory.CategoryStruct.comp
        (relCohMap (ContinuousMap.id (Y × EuclideanSpace ℝ (Fin n))) (Sph Y n) (Punct Y n)
          (mem_Sph_punct Y n) ℤ n)
        (relCohMap (fibRefl n Y) (Sph Y n) (Sph Y n) (fibRefl_mem_sph n Y) ℤ n) := by
    rw [relCohMap_compA (Sph Y n) (Punct Y n) (Punct Y n)
        (ContinuousMap.id (Y × EuclideanSpace ℝ (Fin n))) (fibRefl n Y)
        (fun x hx => mem_Sph_punct Y n x hx) (fibRefl_mem_punct n Y)
        (fun x hx => fibRefl_mem_punct n Y x (mem_Sph_punct Y n x hx)) ℤ n]
    rw [relCohMap_compA (Sph Y n) (Sph Y n) (Punct Y n)
        (fibRefl n Y) (ContinuousMap.id (Y × EuclideanSpace ℝ (Fin n)))
        (fibRefl_mem_sph n Y) (fun x hx => mem_Sph_punct Y n x hx)
        (fun x hx => mem_Sph_punct Y n (fibRefl n Y x) (fibRefl_mem_sph n Y x hx)) ℤ n]
    exact relCohMap_congrA (Sph Y n) (Punct Y n)
      (by rw [ContinuousMap.comp_id, ContinuousMap.id_comp]) _ _ ℤ n
  have hsq_apply : (relCohMap (ContinuousMap.id (Y × EuclideanSpace ℝ (Fin n)))
        (Sph Y n) (Punct Y n) (mem_Sph_punct Y n) ℤ n).hom
        ((relCohMap (fibRefl n Y) (Punct Y n) (Punct Y n) (fibRefl_mem_punct n Y) ℤ n).hom
          (Mpun n Y))
      = (relCohMap (fibRefl n Y) (Sph Y n) (Sph Y n) (fibRefl_mem_sph n Y) ℤ n).hom
          ((relCohMap (ContinuousMap.id (Y × EuclideanSpace ℝ (Fin n)))
            (Sph Y n) (Punct Y n) (mem_Sph_punct Y n) ℤ n).hom (Mpun n Y)) := by
    have := congrArg (fun φ => φ.hom (Mpun n Y)) hsq
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this
  apply hj
  rw [map_neg, Mpun_spec n Y, hsq_apply, Mpun_spec n Y, Mn_fibRefl n hn]

/-- The fixed reflection is the gauge `gaugeEnd (fun _ => flipFst n)`. -/
theorem fibRefl_eq_gaugeEnd (n : ℕ) (Y : Type) [TopologicalSpace Y] :
    fibRefl n Y = gaugeEnd (fun _ : Y => flipFst n) continuous_const := by
  apply ContinuousMap.ext
  intro p
  rfl

/-! ## The orientation character of a general gauge -/

/-- **The orientation character of the punctured model class**: a gauge whose determinant is
negative everywhere acts on `Mpun n Y` by `-1`.

Write `D = (D ∘ flipFst n) ∘ flipFst n`; the first factor has positive determinant everywhere, so it
fixes `Mpun` by `Work.Thom.Mpun_gaugeEnd_invariant`, and the second is the reflection, whose action
is `-1` by `Mpun_fibRefl`. -/
theorem Mpun_gaugeEnd_neg (n : ℕ) (hn : 1 ≤ n) {Y : Type} [TopologicalSpace Y]
    (D : Y → Gauge n) (hD : Continuous D)
    (hdet : ∀ y, LinearMap.det (D y).toLinearMap < 0) :
    (relCohMap (gaugeEnd D hD) (Punct Y n) (Punct Y n)
      (gaugeEnd_mem D hD (fun y => gaugeEnd_bijective_of_det_ne_zero (D y) (ne_of_lt (hdet y))))
      ℤ n).hom (Mpun n Y) = - (Mpun n Y) := by
  let D' : Y → Gauge n := fun y => (D y).comp (flipFst n)
  have hD' : Continuous D' := hD.clm_comp continuous_const
  have hdet' : ∀ y, 0 < LinearMap.det (D' y).toLinearMap := by
    intro y
    have h1 : (D' y).toLinearMap = (D y).toLinearMap.comp (flipFst n).toLinearMap := rfl
    rw [h1, LinearMap.det_comp]
    have h2 : LinearMap.det (flipFst n).toLinearMap < 0 := flipFst_det n (by omega)
    nlinarith [hdet y, h2]
  have hgauge : gaugeEnd D hD
      = (gaugeEnd D' hD').comp (gaugeEnd (fun _ : Y => flipFst n) continuous_const) := by
    apply ContinuousMap.ext
    intro p
    apply Prod.ext
    · rfl
    · show D p.1 p.2 = D' p.1 (flipFst n p.2)
      show D p.1 p.2 = (D p.1).comp (flipFst n) (flipFst n p.2)
      rw [ContinuousLinearMap.comp_apply, flipFst_involutive]
  have hA : ∀ p ∈ Punct Y n, gaugeEnd (fun _ : Y => flipFst n) continuous_const p ∈ Punct Y n :=
    gaugeEnd_mem (fun _ : Y => flipFst n) continuous_const
      (fun y => gaugeEnd_bijective_of_det_ne_zero (flipFst n) (ne_of_lt (flipFst_det n (by omega))))
  have hB : ∀ p ∈ Punct Y n, gaugeEnd D' hD' p ∈ Punct Y n :=
    gaugeEnd_mem D' hD' (fun y => gaugeEnd_bijective_of_det_ne_zero (D' y) (ne_of_gt (hdet' y)))
  have hDmem : ∀ p ∈ Punct Y n, gaugeEnd D hD p ∈ Punct Y n :=
    gaugeEnd_mem D hD (fun y => gaugeEnd_bijective_of_det_ne_zero (D y) (ne_of_lt (hdet y)))
  have hgf : ∀ p ∈ Punct Y n,
      gaugeEnd D' hD' (gaugeEnd (fun _ : Y => flipFst n) continuous_const p) ∈ Punct Y n := by
    intro p hp
    have h1 : gaugeEnd D' hD' (gaugeEnd (fun _ : Y => flipFst n) continuous_const p)
        = gaugeEnd D hD p := by
      rw [hgauge]; rfl
    rw [h1]; exact hDmem p hp
  have hconst : (relCohMap (gaugeEnd (fun _ : Y => flipFst n) continuous_const)
      (Punct Y n) (Punct Y n) hA ℤ n).hom (Mpun n Y) = - Mpun n Y := by
    have heq : gaugeEnd (fun _ : Y => flipFst n) continuous_const = fibRefl n Y :=
      (fibRefl_eq_gaugeEnd n Y).symm
    rw [relCohMap_congrA (Punct Y n) (Punct Y n) heq hA (fibRefl_mem_punct n Y) ℤ n]
    exact Mpun_fibRefl n hn
  have hgoal : (relCohMap (gaugeEnd D hD) (Punct Y n) (Punct Y n) hDmem ℤ n).hom (Mpun n Y)
      = -Mpun n Y := by
    calc (relCohMap (gaugeEnd D hD) (Punct Y n) (Punct Y n) hDmem ℤ n).hom (Mpun n Y)
        = (relCohMap ((gaugeEnd D' hD').comp (gaugeEnd (fun _ : Y => flipFst n) continuous_const))
            (Punct Y n) (Punct Y n) hgf ℤ n).hom (Mpun n Y) :=
          congrArg (fun φ => φ.hom (Mpun n Y))
            (relCohMap_congrA (Punct Y n) (Punct Y n) hgauge hDmem hgf ℤ n)
      _ = (relCohMap (gaugeEnd (fun _ : Y => flipFst n) continuous_const) (Punct Y n) (Punct Y n)
            hA ℤ n).hom ((relCohMap (gaugeEnd D' hD') (Punct Y n) (Punct Y n) hB ℤ n).hom
              (Mpun n Y)) :=
          (relCohMap_compA_apply (Punct Y n) (Punct Y n) (Punct Y n)
            (gaugeEnd (fun _ : Y => flipFst n) continuous_const) (gaugeEnd D' hD') hA hB hgf ℤ n
            (Mpun n Y)).symm
      _ = (relCohMap (gaugeEnd (fun _ : Y => flipFst n) continuous_const) (Punct Y n) (Punct Y n)
            hA ℤ n).hom (Mpun n Y) :=
          congrArg (fun z => (relCohMap (gaugeEnd (fun _ : Y => flipFst n) continuous_const)
            (Punct Y n) (Punct Y n) hA ℤ n).hom z)
            (Mpun_gaugeEnd_invariant n hn D' hD' hdet')
      _ = -Mpun n Y := hconst
  exact hgoal

end

end Work.Thom.Orientation
