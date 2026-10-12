import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.BoxD1Pair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.measurable_boxPairFibreFun_uncurry`

Joint measurability of the box peeled pair fibre
`Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ i j` (`Submission/Work/BoseFixB1/BoxD1Pair.lean`),
as a function of the two free relative slots `(y, z)`, for a merely *measurable* state `Φ` and a
measurable box `A`.  (`Work.SmallBoxPairMomentum.stronglyMeasurable_pairFibreFun` is the
corresponding statement for the un-localised earlier chain, under a *continuity* hypothesis on
`Φ`; the box chain only ever has measurability available.)

The proof splits on `i = j` (the definition is then the zero function) and otherwise writes the
fibre as the `(y, z)`-indexed family of integrals over the remaining configuration `r2 ∈ abox N ℓ`
of a jointly measurable integrand — the two box projections evaluated at the double insertion
`ins2 i (sucAboveInv i j h) y z r2`.  Measurability of the box projections is the delivered
`Work.BoseFixB1S.measurable_boxPInd` / `Work.SlotWord.measurable_boxQInd`, measurability of the
double insertion is `Work.BoseFixB1S.Q0C.eIns2` (a measurable equivalence), and the integral over
the remaining coordinates is `StronglyMeasurable.integral_prod_right`.
-/

namespace Work.BoseFixB1

open MeasureTheory

set_option maxHeartbeats 1000000

theorem measurable_boxPairFibreFun_uncurry {N : ℕ} {ℓ volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦ : Measurable Φ) (i j : Fin (N + 2)) :
    Measurable (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ i j q.1 q.2) := by
  by_cases hij : i = j
  · subst hij
    simp [Work.BoseFixB1.boxPairFibreFun]
  · set j' := Submission.BoseGases.sucAboveInv i j hij with hj'def
    have hPm : Measurable (Work.UBBInputs8.boxPInd volA A i
        (Work.UBBInputs8.boxPInd volA A j Φ)) :=
      Work.BoseFixB1S.measurable_boxPInd volA A hA i
        (Work.BoseFixB1S.measurable_boxPInd volA A hA j hΦ)
    have hQm : Measurable (Work.UBBInputs8.boxQInd volA A j
        (Work.UBBInputs8.boxQInd volA A i Φ)) :=
      Work.SlotWord.measurable_boxQInd volA A hA j
        (Work.SlotWord.measurable_boxQInd volA A hA i hΦ)
    have hmap : Measurable (fun z : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) ×
        Submission.BoseGases.X N =>
        Submission.BoseGases.ins2 i j' z.1.1 z.1.2 z.2) := by
      have h2 : Measurable (fun z : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) ×
          Submission.BoseGases.X N =>
          Work.BoseFixB1S.Q0C.eIns2 i j' ((z.1.1, z.1.2), z.2)) :=
        (Work.BoseFixB1S.Q0C.eIns2 i j').measurable.comp (by fun_prop)
      simpa only [Work.BoseFixB1S.Q0C.eIns2_apply] using h2
    have hF : StronglyMeasurable (Function.uncurry (fun (q : EuclideanSpace ℝ (Fin 3) ×
        EuclideanSpace ℝ (Fin 3)) (r2 : Submission.BoseGases.X N) =>
        Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ)
            (Submission.BoseGases.ins2 i j' q.1 q.2 r2)
          * Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ)
            (Submission.BoseGases.ins2 i j' q.1 q.2 r2))) :=
      ((hPm.comp hmap).stronglyMeasurable).mul ((hQm.comp hmap).stronglyMeasurable)
    have hmain := hF.integral_prod_right
      (ν := (volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N ℓ))
    have hfun : (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ i j q.1 q.2)
        = fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
            ∫ r2, (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ)
                (Submission.BoseGases.ins2 i j' q.1 q.2 r2)
              * Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ)
                (Submission.BoseGases.ins2 i j' q.1 q.2 r2))
              ∂((volume : Measure (Submission.BoseGases.X N)).restrict
                  (Submission.BoseGases.abox N ℓ)) := by
      funext q
      rw [Work.BoseFixB1.boxPairFibreFun, dif_pos hij, ← hj'def]
    rw [hfun]
    exact hmain.measurable

end Work.BoseFixB1
