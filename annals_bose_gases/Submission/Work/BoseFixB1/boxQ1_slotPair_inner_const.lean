import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Q1FormDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

/-- Inner slot-`s` integral against a constant: at an inserted configuration `x = kcInsN n s (y,r)`
both `P_s`-factors are the box indicator `1_A(y)` times the slot-independent one-slot means, so the
`y`-integral of the product against a constant costs the box volume `|A| = q1Vol ℓ d u`. -/
theorem boxQ1_slotPair_inner_const {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : Work.BoseFixB1.E3)
    {n : ℕ} (s : Fin (n + 1)) (t' : Fin n)
    (Ψ₁ Ψ₂ : Submission.BoseGases.X (n + 1) → ℝ) (r : Submission.BoseGases.X n) (c : ℝ) :
    (∫ y in Submission.BoseGases.acube ℓ,
        (Work.BoseFixB1.q1P ℓ d u s Ψ₁ (Submission.BoseGases.kcInsN n s (y, r)))
          * (Work.BoseFixB1.q1P ℓ d u s Ψ₂ (Submission.BoseGases.kcInsN n s (y, r)))
          * c)
      = (Work.BoseFixB1S.Q0C.oneRest (Work.BoseFixB1.q1Vol ℓ d u) (Work.BoseFixB1.q1Box ℓ d u) s Ψ₁ r
          * Work.BoseFixB1S.Q0C.oneRest (Work.BoseFixB1.q1Vol ℓ d u) (Work.BoseFixB1.q1Box ℓ d u) s Ψ₂ r
          * c) * (Work.BoseFixB1.q1Vol ℓ d u) := by
  -- Both `P_s`-factors, read at the inserted configuration, are the box indicator in the
  -- inserted slot times the slot-independent one-slot mean (`Q0C.boxPInd_kcInsN`).
  simp only [q1P, Work.BoseFixB1S.Q0C.boxPInd_kcInsN, Work.BoseFixB1S.Q0C.oneRest_def]
  -- The indicator is `0/1`-valued, so the square of it in the product collapses.
  rw [show (∫ y in Submission.BoseGases.acube ℓ,
        (q1Box ℓ d u).indicator (fun x => 1) y *
              (1 / q1Vol ℓ d u *
                ∫ (z : Submission.BoseGases.kcE3) in q1Box ℓ d u,
                  Ψ₁ ((Submission.BoseGases.kcInsN n s) (z, r))) *
            ((q1Box ℓ d u).indicator (fun x => 1) y *
              (1 / q1Vol ℓ d u *
                ∫ (z : Submission.BoseGases.kcE3) in q1Box ℓ d u,
                  Ψ₂ ((Submission.BoseGases.kcInsN n s) (z, r)))) *
          c)
      = ∫ y in Submission.BoseGases.acube ℓ,
        (q1Box ℓ d u).indicator (fun _ => (1 : ℝ)) y *
          ((1 / q1Vol ℓ d u *
              ∫ (z : Submission.BoseGases.kcE3) in q1Box ℓ d u,
                Ψ₁ ((Submission.BoseGases.kcInsN n s) (z, r)))
            * (1 / q1Vol ℓ d u *
              ∫ (z : Submission.BoseGases.kcE3) in q1Box ℓ d u,
                Ψ₂ ((Submission.BoseGases.kcInsN n s) (z, r)))
            * c) from by
      apply integral_congr_ae
      refine ae_of_all _ (fun y => ?_)
      by_cases hy : y ∈ q1Box ℓ d u <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]]
  -- The indicator is independent of `y`, so the integral against a constant is the constant
  -- times the box volume `∫_{acube ℓ} 1_A = q1Vol ℓ d u`.
  rw [MeasureTheory.integral_mul_const, q1_indicator_acube hℓ u]
  ring

end Work.BoseFixB1
