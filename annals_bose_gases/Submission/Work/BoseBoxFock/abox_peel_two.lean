import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.pairGc23Aux
import Submission.Work.BoseBoxFock.setIntegral_insertCoord2_slice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.abox_peel_two`

The two-coordinate peel of the centred box `abox n ℓ`: for real `F` whose pull-back along the
coordinate insertion `Φ (u,v,x') = insertCoord2 p u v x'` is **integrable** against the product
of the box measures,

    ∫ x in abox n ℓ, F x
      = ∫ u in boxL ℓ, ∫ v in boxL ℓ, ∫ x' in boxPiSet ι ℓ, F (insertCoord2 p u v x'),

with `ι = pairFib23 n p = {k : Fin n // k ≠ p.1 ∧ k ≠ p.2}` and `p.1 ≠ p.2`.

This is the *integrable* (rather than continuous) companion of
`setIntegral_insertCoord2_slice`; the two proofs are the same argument:

* `restrict_abox_eq` writes the box measure as `Measure.pi (boxMeas ℓ)` over all coordinates;
* the measure-preserving coordinate insertion `sliceIns p hp` (`sliceIns_measurePreserving`)
  transports it to the product `((boxMeas ℓ).prod (boxMeas ℓ)).prod (pi (boxMeas ℓ))`;
* two applications of Fubini (`MeasureTheory.integral_integral`, `MeasureTheory.integral_prod`)
  peel the iterated integral off the product measure.

No continuity of `F` is needed: integrability of the pulled-back function is exactly the
hypothesis Fubini needs, and `MeasurePreserving.integral_comp'` for a *measurable equivalence*
carries no integrability side condition.

`sorry`-free.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Peeling the iterated box integral** (integrable form).  Two applications of Fubini turn the
triple set integral into a single integral against the product measure
`((boxMeas ℓ).prod (boxMeas ℓ)).prod P`, where `P` is the product of the box measures over the
remaining coordinates. -/
lemma sliceIterated_eq_prodIntegral_of_integrable {n : ℕ} {ℓ : ℝ} (_hℓ : 0 < ℓ)
    (p : Fin n × Fin n) (_hp : p.1 ≠ p.2) {f : Submission.BoseGases.X n → ℝ}
    (hf : MeasureTheory.Integrable
      (fun w : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
        f (insertCoord2 p w.1.1 w.1.2 w.2))
      (((boxMeas ℓ).prod (boxMeas ℓ)).prod
        (Measure.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} => boxMeas ℓ)))) :
    (∫ y in Work.BoseK15.corpusBox.boxL ℓ, ∫ u in Work.BoseK15.corpusBox.boxL ℓ,
        ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          f (insertCoord2 p y u x''))
      = ∫ w : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3),
          f (insertCoord2 p w.1.1 w.1.2 w.2)
            ∂(((boxMeas ℓ).prod (boxMeas ℓ)).prod
              (Measure.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} => boxMeas ℓ))) := by
  have hIntZ : Integrable
      (fun z : E3 × E3 => ∫ y : ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3),
          f (insertCoord2 p z.1 z.2 y)
          ∂(Measure.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} => boxMeas ℓ)))
      ((boxMeas ℓ).prod (boxMeas ℓ)) := hf.integral_prod_left
  calc (∫ y in Work.BoseK15.corpusBox.boxL ℓ, ∫ u in Work.BoseK15.corpusBox.boxL ℓ,
        ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          f (insertCoord2 p y u x''))
      = ∫ y, ∫ u, (∫ y' : ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3),
            f (insertCoord2 p y u y')
            ∂(Measure.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} => boxMeas ℓ)))
          ∂(boxMeas ℓ) ∂(boxMeas ℓ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        exact setIntegral_boxPiSet_eq (fun y' => f (insertCoord2 p y u y'))
    _ = ∫ z : E3 × E3, (∫ y' : ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3),
            f (insertCoord2 p z.1 z.2 y')
            ∂(Measure.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} => boxMeas ℓ)))
          ∂((boxMeas ℓ).prod (boxMeas ℓ)) :=
        MeasureTheory.integral_integral hIntZ
    _ = ∫ w : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3),
          f (insertCoord2 p w.1.1 w.1.2 w.2)
            ∂(((boxMeas ℓ).prod (boxMeas ℓ)).prod
              (Measure.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} => boxMeas ℓ))) :=
        (MeasureTheory.integral_prod
          (fun w : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
            f (insertCoord2 p w.1.1 w.1.2 w.2)) hf).symm

/-- **The iterated integral is a `Measure`-integral.**  Rewrites the triple set integral of the
statement into the iterated integral against `boxMeas ℓ` and `Measure.pi (boxMeas ℓ)`. -/
lemma sliceIterated_setIntegral_eq {n : ℕ} {ℓ : ℝ} (p : Fin n × Fin n)
    {f : Submission.BoseGases.X n → ℝ} :
    (∫ u in Work.BoseK15.corpusBox.boxL ℓ, ∫ v in Work.BoseK15.corpusBox.boxL ℓ,
        ∫ x' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          f (insertCoord2 p u v x'))
      = ∫ u : E3, ∫ v : E3, ∫ x' : ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3),
          f (insertCoord2 p u v x')
            ∂(Measure.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} => boxMeas ℓ))
            ∂(boxMeas ℓ) ∂(boxMeas ℓ) := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  exact setIntegral_boxPiSet_eq (fun x' => f (insertCoord2 p u v x'))

theorem abox_peel_two {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {F : Submission.BoseGases.X n → ℝ}
    (hF : MeasureTheory.Integrable
      (fun w : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) ×
          (Work.BoseBoxFock.pairFib23 n p → EuclideanSpace ℝ (Fin 3)) =>
        F (Work.BoseBoxFock.insertCoord2 p w.1.1 w.1.2 w.2))
      (((Work.BoseBoxFock.boxMeas ℓ).prod (Work.BoseBoxFock.boxMeas ℓ)).prod
        (MeasureTheory.Measure.pi (fun _ : Work.BoseBoxFock.pairFib23 n p =>
          Work.BoseBoxFock.boxMeas ℓ)))) :
    (∫ x in Submission.BoseGases.abox n ℓ, F x)
      = ∫ u in Work.BoseK15.corpusBox.boxL ℓ, ∫ v in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ x' in Work.BoseBoxFock.boxPiSet (Work.BoseBoxFock.pairFib23 n p) ℓ,
            F (Work.BoseBoxFock.insertCoord2 p u v x') := by
  have hZ : Integrable
      (fun z : E3 × E3 => ∫ x' : ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3),
          F (insertCoord2 p z.1 z.2 x')
          ∂(Measure.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} => boxMeas ℓ)))
      ((boxMeas ℓ).prod (boxMeas ℓ)) := hF.integral_prod_left
  calc (∫ x in Submission.BoseGases.abox n ℓ, F x)
      = ∫ x : Fin n → E3, F x ∂(Measure.pi (fun _ : Fin n => boxMeas ℓ)) :=
        setIntegral_abox_eq hℓ F
    _ = ∫ w : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3),
          F (sliceIns p hp w)
            ∂(((boxMeas ℓ).prod (boxMeas ℓ)).prod
              (Measure.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} => boxMeas ℓ))) :=
        ((sliceIns_measurePreserving (ℓ := ℓ) p hp).integral_comp' F).symm
    _ = ∫ w : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3),
          F (insertCoord2 p w.1.1 w.1.2 w.2)
            ∂(((boxMeas ℓ).prod (boxMeas ℓ)).prod
              (Measure.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} => boxMeas ℓ))) := by
        simp only [sliceIns_apply]
    _ = ∫ z : E3 × E3, (∫ x' : ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3),
            F (insertCoord2 p z.1 z.2 x')
            ∂(Measure.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} => boxMeas ℓ)))
          ∂((boxMeas ℓ).prod (boxMeas ℓ)) :=
        MeasureTheory.integral_prod
          (fun w : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
            F (insertCoord2 p w.1.1 w.1.2 w.2)) hF
    _ = ∫ u : E3, ∫ v : E3, ∫ x' : ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3),
          F (insertCoord2 p u v x')
            ∂(Measure.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} => boxMeas ℓ))
            ∂(boxMeas ℓ) ∂(boxMeas ℓ) :=
        (MeasureTheory.integral_integral (μ := boxMeas ℓ) (ν := boxMeas ℓ)
          (f := fun u v : E3 => ∫ x' : ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3),
            F (insertCoord2 p u v x')
            ∂(Measure.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} => boxMeas ℓ))) hZ).symm
    _ = ∫ u in Work.BoseK15.corpusBox.boxL ℓ, ∫ v in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ x' in Work.BoseBoxFock.boxPiSet (Work.BoseBoxFock.pairFib23 n p) ℓ,
            F (Work.BoseBoxFock.insertCoord2 p u v x') :=
        (sliceIterated_setIntegral_eq (ℓ := ℓ) p (f := F)).symm

end Work.BoseBoxFock
