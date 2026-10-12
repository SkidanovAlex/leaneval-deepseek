import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.amgmSlotSum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

open MeasureTheory

/-- Pointwise Cauchy–Schwarz / power-mean for a finite family of real functions:
`(Σ_k g_k x)² ≤ N · Σ_k (g_k x)²`. -/
private lemma sq_sum_le_card_mul_sum_sq_fin {N : ℕ} {g : Fin N → Submission.BoseGases.X N → ℝ}
    (x : Submission.BoseGases.X N) :
    (∑ k : Fin N, g k x) ^ 2 ≤ (N : ℝ) * ∑ k : Fin N, (g k x) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin N)))
    (f := fun k => g k x)
  simpa using h

theorem sqSumInt_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : Fin N → Submission.BoseGases.X N → ℝ} (hgc : ∀ k, Continuous (g k)) :
    (∫ x in Submission.BoseGases.abox N ℓ, (∑ k : Fin N, g k x) ^ 2)
      ≤ (N : ℝ) * (∑ k : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (g k x) ^ 2) := by
  -- the two integrands are continuous, hence integrable on the compact box
  have hLc : Continuous (fun x : Submission.BoseGases.X N => (∑ k : Fin N, g k x) ^ 2) :=
    (continuous_finsetSum (Finset.univ : Finset (Fin N)) (fun k _ => hgc k)).pow 2
  have hRc : Continuous (fun x : Submission.BoseGases.X N =>
      (N : ℝ) * ∑ k : Fin N, (g k x) ^ 2) :=
    continuous_const.mul
      (continuous_finsetSum (Finset.univ : Finset (Fin N)) (fun k _ => (hgc k).pow 2))
  have hLint : IntegrableOn (fun x : Submission.BoseGases.X N => (∑ k : Fin N, g k x) ^ 2)
      (Submission.BoseGases.abox N ℓ) volume :=
    Submission.BoseGases.integrableOn_abox_of_continuous hℓ hLc
  have hRint : IntegrableOn (fun x : Submission.BoseGases.X N =>
      (N : ℝ) * ∑ k : Fin N, (g k x) ^ 2) (Submission.BoseGases.abox N ℓ) volume :=
    Submission.BoseGases.integrableOn_abox_of_continuous hℓ hRc
  calc
    (∫ x in Submission.BoseGases.abox N ℓ, (∑ k : Fin N, g k x) ^ 2)
        ≤ ∫ x in Submission.BoseGases.abox N ℓ, (N : ℝ) * ∑ k : Fin N, (g k x) ^ 2 :=
          integral_mono hLint hRint (fun x => sq_sum_le_card_mul_sum_sq_fin x)
    _ = (N : ℝ) * ∑ k : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (g k x) ^ 2 := by
          rw [MeasureTheory.integral_const_mul]
          congr 1
          exact MeasureTheory.integral_finsetSum (Finset.univ)
            (fun k _ => Submission.BoseGases.integrableOn_abox_of_continuous hℓ ((hgc k).pow 2))

end Work.BoseFixB1
