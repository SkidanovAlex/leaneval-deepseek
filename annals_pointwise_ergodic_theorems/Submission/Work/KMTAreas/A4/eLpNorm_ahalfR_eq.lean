import Mathlib
import Submission.Work.KMTContract.Areas

/-!
# `AhalfR TZ` and `AhalfZ` agree in `ℓᵖ`

`Submission.PointwiseErgodicTheorems.AhalfR TZ` is the paper's halved average in the *reflected*
convention, `Ã_N(f,g)(x) = N⁻¹ ∑_{N/2<n≤N} f(x-n) g(x-P(n))`, whereas the inverse-theory chapter's
`Work.Analysis.InverseTheory.AhalfZ` uses the paper's convention
`Ã_N(f,g)(x) = N⁻¹ ∑_{N/2<n≤N} f(x+n) g(x+P(n))`.

The two differ only by the reflection `x ↦ -x` of the ambient group `ℤ` (which is a
measure-preserving bijection for `Measure.count`) together with the reflection of *both* input
functions.  Consequently their `ℓᵖ` seminorms agree; this file records that identity.
-/

namespace Work.KMTAreas.A4

open scoped ENNReal NNReal BigOperators

/-- Negation on `ℤ` preserves counting measure. -/
private lemma measurePreserving_neg_count :
    MeasureTheory.MeasurePreserving (fun x : ℤ => -x) MeasureTheory.Measure.count
      MeasureTheory.Measure.count := by
  refine MeasureTheory.MeasurePreserving.mk measurable_neg ?_
  ext s hs
  rw [MeasureTheory.Measure.map_apply measurable_neg hs]
  have hpre : (fun x : ℤ => -x) ⁻¹' s = Neg.neg '' s := by
    ext y; simp
  rw [hpre]
  exact MeasureTheory.Measure.count_injective_image neg_injective s

/-- The pointwise identity: the halved average `AhalfZ` with both inputs reflected is the reflected
halved average `AhalfR TZ`. -/
private lemma AhalfZ_neg_eq_AhalfR (N : ℕ) (P : Polynomial ℤ) (f g : ℤ → ℂ) (x : ℤ) :
    Work.Analysis.InverseTheory.AhalfZ N P (fun t : ℤ => f (-t)) (fun t : ℤ => g (-t)) x
      = Submission.PointwiseErgodicTheorems.AhalfR Submission.PointwiseErgodicTheorems.TZ
          (N : ℝ≥0) Polynomial.X P f g (-x) := by
  rw [Work.Analysis.InverseTheory.AhalfZ, Submission.PointwiseErgodicTheorems.AhalfR,
    Submission.PointwiseErgodicTheorems.Ahalf, Submission.PointwiseErgodicTheorems.Ablock]
  simp only [Nat.floor_natCast]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Polynomial.eval_X, Submission.PointwiseErgodicTheorems.TZ_zpow,
    Submission.PointwiseErgodicTheorems.TZ_zpow]
  congr 2 <;> ring

theorem eLpNorm_ahalfR_eq (P : Polynomial ℤ) (N : ℕ) (f g : ℤ → ℂ) (p : ENNReal) : MeasureTheory.eLpNorm (fun x : ℤ => Submission.PointwiseErgodicTheorems.AhalfR Submission.PointwiseErgodicTheorems.TZ (N : NNReal) Polynomial.X P f g x) p MeasureTheory.Measure.count = MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.InverseTheory.AhalfZ N P (fun t : ℤ => f (-t)) (fun t : ℤ => g (-t)) x) p MeasureTheory.Measure.count := by
  have hfun : (fun x : ℤ =>
        Work.Analysis.InverseTheory.AhalfZ N P (fun t : ℤ => f (-t)) (fun t : ℤ => g (-t)) x)
      = (fun x : ℤ => Submission.PointwiseErgodicTheorems.AhalfR
          Submission.PointwiseErgodicTheorems.TZ (N : ℝ≥0) Polynomial.X P f g (-x)) :=
    funext fun x => AhalfZ_neg_eq_AhalfR N P f g x
  rw [hfun]
  rw [show (fun x : ℤ => Submission.PointwiseErgodicTheorems.AhalfR
        Submission.PointwiseErgodicTheorems.TZ (N : ℝ≥0) Polynomial.X P f g (-x))
      = (fun x : ℤ => Submission.PointwiseErgodicTheorems.AhalfR
          Submission.PointwiseErgodicTheorems.TZ (N : ℝ≥0) Polynomial.X P f g x) ∘
            (fun x : ℤ => -x) from rfl]
  rw [MeasureTheory.eLpNorm_comp_measurePreserving _ measurePreserving_neg_count]
  exact (measurable_of_countable _).aestronglyMeasurable

end Work.KMTAreas.A4
