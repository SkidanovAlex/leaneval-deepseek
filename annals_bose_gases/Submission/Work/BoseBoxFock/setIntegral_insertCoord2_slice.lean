import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.sliceIns_integrable
import Submission.Work.BoseBoxFock.sliceIns_measurePreserving
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.setIntegral_insertCoord2_slice`

The slice identity for the coordinate insertion: for a continuous `f : Xn n → ℝ` and two distinct
slots `p.1 ≠ p.2`,

    ∫ y in boxL ℓ, ∫ u in boxL ℓ, ∫ x'' in boxPiSet ι ℓ, f (insertCoord2 p y u x'')
      = ∫ x in abox n ℓ, f x,      ι = {k : Fin n // k ≠ p.1 ∧ k ≠ p.2}.

The right-hand side is the integral against the product of the box measures `Measure.pi (boxMeas ℓ)`
over `Fin n` (`restrict_abox_eq`), while the left-hand side is, by two applications of Fubini
(`MeasureTheory.integral_integral`, `MeasureTheory.integral_prod`), the integral of the same
function against the product measure on `(E3 × E3) × (ι → E3)`.  The two are identified by the
measure-preserving coordinate insertion `sliceIns` (`sliceIns_measurePreserving`), whose
integrability hypothesis is `sliceIns_integrable`.

All the analytic content (the measure-preserving equivalence and the integrability) is in the
imported modules; this file assembles it.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-! ## 1. The set integrals as integrals against the box measures -/

/-- The set integral over the product box is the integral against the product of the box
measures. -/
lemma setIntegral_boxPiSet_eq {ι : Type*} [Fintype ι] {ℓ : ℝ} (G : (ι → E3) → ℝ) :
    (∫ x'' in boxPiSet ι ℓ, G x'')
      = ∫ x'', G x'' ∂(Measure.pi (fun _ : ι => boxMeas ℓ)) := by
  rw [show (∫ x'' in boxPiSet ι ℓ, G x'')
      = ∫ x'', G x'' ∂((volume : Measure (ι → E3)).restrict (boxPiSet ι ℓ)) from rfl]
  rw [restrict_boxPiSet_eq]

/-- The set integral over `abox n ℓ` is the integral against the product of the box measures. -/
lemma setIntegral_abox_eq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (f : Xn n → ℝ) :
    (∫ x in Submission.BoseGases.abox n ℓ, f x)
      = ∫ x, f x ∂(Measure.pi (fun _ : Fin n => boxMeas ℓ)) := by
  rw [show (∫ x in Submission.BoseGases.abox n ℓ, f x)
      = ∫ x, f x ∂((volume : Measure (Fin n → E3)).restrict (Submission.BoseGases.abox n ℓ))
      from rfl]
  rw [restrict_abox_eq hℓ]

/-! ## 2. The iterated integral is an integral against the product measure -/

/-- **Peeling the iterated integral.**  Two applications of Fubini turn the triple set integral
into a single integral against the product measure `((boxMeas ℓ).prod (boxMeas ℓ)).prod P`, where
`P` is the product of the box measures over `ι`. -/
lemma sliceIterated_eq_prodIntegral {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    (hp : p.1 ≠ p.2) {f : Xn n → ℝ} (hf : Continuous f) :
    (∫ y in Work.BoseK15.corpusBox.boxL ℓ, ∫ u in Work.BoseK15.corpusBox.boxL ℓ,
        ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          f (insertCoord2 p y u x''))
      = ∫ w : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3),
          f (insertCoord2 p w.1.1 w.1.2 w.2)
            ∂(((boxMeas ℓ).prod (boxMeas ℓ)).prod
              (Measure.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} => boxMeas ℓ))) := by
  have hIntJoint := sliceIns_integrable hℓ p hp hf
  have hIntZ : Integrable
      (fun z : E3 × E3 => ∫ y : ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3),
          f (insertCoord2 p z.1 z.2 y)
          ∂(Measure.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} => boxMeas ℓ)))
      ((boxMeas ℓ).prod (boxMeas ℓ)) := hIntJoint.integral_prod_left
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
            f (insertCoord2 p w.1.1 w.1.2 w.2)) hIntJoint).symm

/-! ## 3. The slice identity -/

theorem setIntegral_insertCoord2_slice {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {f : Work.BoseDict.Xn n → ℝ} (hf : Continuous f) :
    (∫ y in Work.BoseK15.corpusBox.boxL ℓ, ∫ u in Work.BoseK15.corpusBox.boxL ℓ,
        ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          f (insertCoord2 p y u x''))
      = ∫ x in Submission.BoseGases.abox n ℓ, f x := by
  calc (∫ y in Work.BoseK15.corpusBox.boxL ℓ, ∫ u in Work.BoseK15.corpusBox.boxL ℓ,
        ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          f (insertCoord2 p y u x''))
      = ∫ w : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3),
          f (insertCoord2 p w.1.1 w.1.2 w.2)
            ∂(((boxMeas ℓ).prod (boxMeas ℓ)).prod
              (Measure.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} => boxMeas ℓ))) :=
        sliceIterated_eq_prodIntegral hℓ p hp hf
    _ = ∫ w : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3),
          f (sliceIns p hp w)
            ∂(((boxMeas ℓ).prod (boxMeas ℓ)).prod
              (Measure.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} => boxMeas ℓ))) := by
        simp only [sliceIns_apply]
    _ = ∫ x : Fin n → E3, f x ∂(Measure.pi (fun _ : Fin n => boxMeas ℓ)) :=
        (sliceIns_measurePreserving p hp).integral_comp' f
    _ = ∫ x in Submission.BoseGases.abox n ℓ, f x := (setIntegral_abox_eq hℓ f).symm

end Work.BoseBoxFock
