import Mathlib
import Submission.Work.Modular.Poisson.Periodize
import Submission.Work.Poisson.covolume_intLatticeE
import Submission.Work.Poisson.mFourier_eq_charFun_adjoint
import Submission.Work.Poisson.setIntegral_preimage_linearEquiv

set_option linter.unusedVariables false

namespace Work.Poisson

open scoped FourierTransform SchwartzMap
open MeasureTheory

noncomputable section

/-- Multiplication by `r⁻¹ • -` undoes multiplication by `(r : ℂ)`. -/
lemma ofReal_mul_real_smul {r : ℝ} (hr : r ≠ 0) (z : ℂ) : (r : ℂ) * (r⁻¹ • z) = z := by
  rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hr,
    Complex.ofReal_one, one_mul]

theorem integral_mFourier_periodize {n : ℕ}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (hspan : Submodule.span ℝ (L : Set (EuclideanSpace ℝ (Fin n))) = ⊤)
    (d : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hd : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ L ↔ d x ∈ Work.Modular.intLatticeE (Fin n))
    (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)
    (k : Fin n → ℤ) :
    ∫ y in Work.Modular.unitCube (ι := Fin n),
        UnitAddTorus.mFourier (-k) (Work.Modular.projTorus y) •
          Work.Modular.periodize L f ((Work.Modular.coordMap d).symm y)
      = ((|LinearMap.det d.toLinearMap| : ℝ) : ℂ) *
        ∫ z in (d ⁻¹' Work.Modular.cubeE (Fin n)),
          Work.Modular.charFun (LinearMap.adjoint d.toLinearMap (Work.Modular.intVecE k)) z *
            Work.Modular.periodize L f z := by
  classical
  -- the unit cube in coordinates is the preimage of the cube under the coordinate isometry
  have hcube : MeasurableSet (Work.Modular.cubeE (Fin n)) :=
    (Work.Modular.measurableSet_unitCube (ι := Fin n)).preimage
      (EuclideanSpace.equiv (Fin n) ℝ).continuous.measurable
  have hdet : LinearMap.det d.toLinearMap ≠ 0 := by
    rw [← LinearEquiv.coe_det]
    exact Units.ne_zero _
  -- Step 1: transport the integral from the coordinate cube to the Euclidean unit cube
  have hstep1 :
      (∫ y in Work.Modular.unitCube (ι := Fin n),
          UnitAddTorus.mFourier (-k) (Work.Modular.projTorus y) •
            Work.Modular.periodize L f ((Work.Modular.coordMap d).symm y))
        = ∫ x in Work.Modular.cubeE (Fin n),
            UnitAddTorus.mFourier (-k)
                (Work.Modular.projTorus ((EuclideanSpace.equiv (Fin n) ℝ) x)) •
              Work.Modular.periodize L f
                ((Work.Modular.coordMap d).symm ((EuclideanSpace.equiv (Fin n) ℝ) x)) := by
    have h := MeasureTheory.MeasurePreserving.setIntegral_preimage_emb
      (Work.Poisson.measurePreserving_euclideanSpaceEquiv (Fin n))
      ((EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.measurableEmbedding)
      (fun y => UnitAddTorus.mFourier (-k) (Work.Modular.projTorus y) •
        Work.Modular.periodize L f ((Work.Modular.coordMap d).symm y))
      (Work.Modular.unitCube (ι := Fin n))
    rw [show Work.Modular.cubeE (Fin n)
        = (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' Work.Modular.unitCube (ι := Fin n) from rfl]
    exact h.symm
  -- Step 2: the torus character equals `charFun` of the adjoint
  have hpoint : Set.EqOn
      (fun x : EuclideanSpace ℝ (Fin n) =>
        UnitAddTorus.mFourier (-k)
            (Work.Modular.projTorus ((EuclideanSpace.equiv (Fin n) ℝ) x)) •
          Work.Modular.periodize L f
            ((Work.Modular.coordMap d).symm ((EuclideanSpace.equiv (Fin n) ℝ) x)))
      (fun x : EuclideanSpace ℝ (Fin n) =>
        Work.Modular.charFun
            (LinearMap.adjoint d.toLinearMap (Work.Modular.intVecE k)) (d.symm x) *
          Work.Modular.periodize L f (d.symm x))
      (Work.Modular.cubeE (Fin n)) := by
    intro x _
    dsimp only
    rw [Work.Modular.coordMap_symm_apply, ContinuousLinearEquiv.symm_apply_apply,
      mFourier_eq_charFun_adjoint d k x, smul_eq_mul]
  -- Step 3: change variables `z = d.symm w`
  rw [hstep1, MeasureTheory.setIntegral_congr_fun hcube hpoint]
  rw [setIntegral_preimage_linearEquiv d (Work.Modular.cubeE (Fin n))
    (fun z => Work.Modular.charFun
      (LinearMap.adjoint d.toLinearMap (Work.Modular.intVecE k)) z *
        Work.Modular.periodize L f z)]
  exact (ofReal_mul_real_smul (abs_ne_zero.mpr hdet) _).symm

end

end Work.Poisson
