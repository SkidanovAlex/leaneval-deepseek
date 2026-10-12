import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.setIntegral_insertCoord_slice
import Submission.Work.BoseBoxFock.sliceDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.kinFormB_slot_fsT`

The **slot-`i` peel of the box kinetic word** at the centred box: for a `C^∞` state
`Φ : X n → ℝ` the slot-`i` fibre word `fsT ℓ d s εT b 0 (fibre n i Φ x)` (the integrand of
`Work.BoseKinLoc.slotForm`) does not depend on the `i`-th coordinate `x i` of the configuration.
Consequently

    ℓ⁻³ ∫_{abox n ℓ} 1_{Λ(0)}(xᵢ) · fsT (fibreᵢ Φ x) = ∫_{x' ∈ Λ(ℓ)^{{k // k ≠ i}}} fsT (Φ ∘ insertᵢ x'),

i.e. the slot integral over the product box is the integral of the *inserted* fibre word over the
box over the complementary coordinates; and that inserted fibre word is integrable on the
complementary box.

The measure-theoretic content is isolated in `insertCoord_boxPiSet_peel` below: `volume` on a
finite product of Euclidean spaces is `Measure.pi` of the restricted cube measures
(`Work.BoseBoxFock.restrict_abox_eq`, `restrict_boxPiSet_eq`), the coordinate insertion
`insertCoord i : E3 × (ι → E3) → X n` is measure preserving
(`Work.BoseBoxFock.measurePreserving_insertSliceEquiv`), Fubini (`integral_prod_symm`) turns the
box integral into the iterated integral, the window `1_{Λ(0)} = indU ℓ 0` integrates to `ℓ³`
against the cube measure (`Work.BoseBoxFock.boxMeas`,
`Work.Sector.integral_indU_zero_restrict_acube`), and `integral_mul_const`/`Integrable.const_mul`
peel off the constant.
-/

namespace Work.BoseBoxFock

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The peel of the product box along one coordinate.**  If the function
`x ↦ indU ℓ 0 (x i) * G (x ↾ {k // k ≠ i})` is integrable on the product box `abox n ℓ`, then `G`
is integrable on the complementary box `boxPiSet {k // k ≠ i} ℓ` and the box integral of that
function is `ℓ³` times the integral of `G` over the complementary box.  This is the abstract
measure-theoretic core of `kinFormB_slot_fsT`. -/
theorem insertCoord_boxPiSet_peel {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {G : ({k : Fin n // k ≠ i} → E3) → ℝ}
    (hF : Integrable (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.indU ℓ 0 (x i) * G (fun k => x k.1))
      (volume.restrict (Submission.BoseGases.abox n ℓ))) :
    IntegrableOn G (boxPiSet ({k : Fin n // k ≠ i}) ℓ) volume ∧
    (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i) * G (fun k => x k.1))
      = ℓ ^ 3 * ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ, G x' := by
  -- the window `1_{Λ(0)}` integrates to the box volume against the cube measure
  have hmu_indU : (∫ w : E3, Work.BoseKinLoc.indU ℓ 0 w ∂(boxMeas ℓ)) = ℓ ^ 3 := by
    rw [boxMeas, corpusBox_boxL_eq_acube hℓ]
    exact Work.Sector.integral_indU_zero_restrict_acube hℓ
  -- the coordinate insertion is measure preserving
  have hmp := measurePreserving_insertSliceEquiv (n := n) i ℓ
  have hF' : Integrable (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.indU ℓ 0 (x i) * G (fun k => x k.1))
      (Measure.pi (fun _ : Fin n => boxMeas ℓ)) := by
    rw [← restrict_abox_eq hℓ]; exact hF
  -- the pull-back along `insertCoord i`
  have hpt : ∀ z : E3 × ({k : Fin n // k ≠ i} → E3),
      (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.indU ℓ 0 (x i) * G (fun k => x k.1)) (insertSliceEquiv i z)
        = Work.BoseKinLoc.indU ℓ 0 z.1 * G z.2 := by
    intro z
    rw [insertSliceEquiv_apply]
    have h1 : (insertCoord i z.1 z.2) i = z.1 := by simp [Work.BoseBoxFock.insertCoord]
    have h2 : (fun k : {k : Fin n // k ≠ i} => insertCoord i z.1 z.2 k.1) = z.2 := by
      funext k; simp [Work.BoseBoxFock.insertCoord, k.2]
    show Work.BoseKinLoc.indU ℓ 0 ((insertCoord i z.1 z.2) i) *
        G (fun k => insertCoord i z.1 z.2 k.1) = Work.BoseKinLoc.indU ℓ 0 z.1 * G z.2
    rw [h1, h2]
  have hInt : Integrable (fun z : E3 × ({k : Fin n // k ≠ i} → E3) =>
        Work.BoseKinLoc.indU ℓ 0 z.1 * G z.2)
      ((boxMeas ℓ).prod (Measure.pi (fun _ : {k : Fin n // k ≠ i} => boxMeas ℓ))) := by
    have h := (hmp.integrable_comp (g := fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.indU ℓ 0 (x i) * G (fun k => x k.1)) hF'.aestronglyMeasurable).mpr hF'
    exact h.congr (Filter.Eventually.of_forall hpt)
  -- `G` is integrable on the complementary box
  have hIntG : IntegrableOn G (boxPiSet ({k : Fin n // k ≠ i}) ℓ) volume := by
    have h3 : Integrable (fun x' : {k : Fin n // k ≠ i} → E3 => ℓ ^ 3 * G x')
        (Measure.pi (fun _ : {k : Fin n // k ≠ i} => boxMeas ℓ)) :=
      hInt.integral_prod_right.congr (Filter.Eventually.of_forall fun x' => by
        dsimp only
        rw [MeasureTheory.integral_mul_const, hmu_indU])
    have h4 : Integrable (fun x' : {k : Fin n // k ≠ i} → E3 => (ℓ ^ 3)⁻¹ * (ℓ ^ 3 * G x'))
        (Measure.pi (fun _ : {k : Fin n // k ≠ i} => boxMeas ℓ)) := h3.const_mul _
    have h5 : Integrable G (Measure.pi (fun _ : {k : Fin n // k ≠ i} => boxMeas ℓ)) :=
      h4.congr (Filter.Eventually.of_forall fun x' => by
        dsimp only
        rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ)), one_mul])
    show Integrable G (volume.restrict (boxPiSet ({k : Fin n // k ≠ i}) ℓ))
    rw [restrict_boxPiSet_eq]
    exact h5
  refine ⟨hIntG, ?_⟩
  calc (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i) * G (fun k => x k.1))
      = ∫ z : E3 × ({k : Fin n // k ≠ i} → E3),
          Work.BoseKinLoc.indU ℓ 0 z.1 * G z.2
          ∂((boxMeas ℓ).prod (Measure.pi (fun _ : {k : Fin n // k ≠ i} => boxMeas ℓ))) := by
        rw [restrict_abox_eq hℓ]
        rw [← hmp.integral_comp' (fun x : Submission.BoseGases.X n =>
            Work.BoseKinLoc.indU ℓ 0 (x i) * G (fun k => x k.1))]
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∫ x' : {k : Fin n // k ≠ i} → E3,
          ∫ w : E3, Work.BoseKinLoc.indU ℓ 0 w * G x' ∂(boxMeas ℓ)
          ∂(Measure.pi (fun _ : {k : Fin n // k ≠ i} => boxMeas ℓ)) :=
        MeasureTheory.integral_prod_symm _ hInt
    _ = ∫ x' : {k : Fin n // k ≠ i} → E3, ℓ ^ 3 * G x'
          ∂(Measure.pi (fun _ : {k : Fin n // k ≠ i} => boxMeas ℓ)) := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
        dsimp only
        rw [MeasureTheory.integral_mul_const, hmu_indU]
    _ = ℓ ^ 3 * ∫ x' : {k : Fin n // k ≠ i} → E3, G x'
          ∂(Measure.pi (fun _ : {k : Fin n // k ≠ i} => boxMeas ℓ)) :=
        MeasureTheory.integral_const_mul _ _
    _ = ℓ ^ 3 * ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ, G x' := by
        rw [restrict_boxPiSet_eq]

/-- The slot-`i` fibre of `Φ` is the insertion of the `i`-th coordinate: for every configuration
`x`, `fibre n i Φ x = fun w ↦ Φ (insertCoord i w (x ↾ {k // k ≠ i}))`. -/
theorem fibre_eq_insertCoord {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (i : Fin n)
    (x : Submission.BoseGases.X n) :
    Work.BoseKinLoc.fibre n i Φ x
      = fun w : E3 => Φ (insertCoord i w (fun k => x k.1)) := by
  funext w
  show Φ (Function.update x i w) = Φ (insertCoord i w (fun k => x k.1))
  congr 1
  funext k
  by_cases hk : k = i
  · subst hk; simp [Function.update_self, Work.BoseBoxFock.insertCoord]
  · simp [Work.BoseBoxFock.insertCoord, hk]

theorem kinFormB_slot_fsT {n : ℕ} {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin n) :
    MeasureTheory.IntegrableOn
      (fun x' : ({k : Fin n // k ≠ i} → EuclideanSpace ℝ (Fin 3)) =>
        Work.BoseKinLoc.fsT ℓ d s εT b 0
          (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Work.BoseBoxFock.insertCoord i z x')))
      (Work.BoseBoxFock.boxPiSet ({k : Fin n // k ≠ i}) ℓ)
    ∧ ℓ ^ (-3 : ℤ) * (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i) *
          Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n i Φ x))
      = ∫ x' in Work.BoseBoxFock.boxPiSet ({k : Fin n // k ≠ i}) ℓ,
          Work.BoseKinLoc.fsT ℓ d s εT b 0
            (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Work.BoseBoxFock.insertCoord i z x')) := by
  classical
  -- the word `fsT` is blind to the coordinate `i`, so the slot integrand is the pull-back of the
  -- inserted fibre word
  have hfun : (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.indU ℓ 0 (x i) *
          Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n i Φ x))
      = (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x i) *
          Work.BoseKinLoc.fsT ℓ d s εT b 0
            (fun z : E3 => Φ (insertCoord i z (fun k => x k.1)))) := by
    funext x
    rw [fibre_eq_insertCoord i x]
  -- integrability of the slot integrand (a smooth, hence box-local, state)
  have hF : Integrable (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.indU ℓ 0 (x i) *
          Work.BoseKinLoc.fsT ℓ d s εT b 0
            (fun z : E3 => Φ (insertCoord i z (fun k => x k.1))))
      (volume.restrict (Submission.BoseGases.abox n ℓ)) := by
    rw [← hfun]
    exact Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (ℓ := ℓ) (d := d) (s := s)
      (εT := εT) (b := b) hℓ i hΦ
  obtain ⟨hInt, hid⟩ := insertCoord_boxPiSet_peel (ℓ := ℓ) hℓ i
    (G := fun x' => Work.BoseKinLoc.fsT ℓ d s εT b 0
      (fun z : E3 => Φ (insertCoord i z x'))) hF
  refine ⟨hInt, ?_⟩
  have hL : (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i) *
          Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n i Φ x))
      = (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i) *
          Work.BoseKinLoc.fsT ℓ d s εT b 0
            (fun z : E3 => Φ (insertCoord i z (fun k => x k.1)))) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => congrFun hfun x)
  rw [hL, hid, ← mul_assoc]
  rw [show ℓ ^ (-3 : ℤ) * ℓ ^ 3 = 1 by
    rw [show (-3 : ℤ) = -(3 : ℤ) by norm_num, zpow_neg, zpow_ofNat]
    exact inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ)), one_mul]

end Work.BoseBoxFock
