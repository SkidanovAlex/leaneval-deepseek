import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Hcond_cofinality
import Submission.Work.EKLC6Core.HcondSig_ne_top_of_measure_decay
import Submission.Work.EKLC6Core.CountablePartTrunc

/-!
# `Work.EKLC6Core.C6_tsum_entropy` — finite static entropy from a summable-entropy partition

**Pisa 7.50**, in the form consumed by the countable-generator route of component C6
(`Work.EKLC6Core.Ch_ent_le_HcondSig_gen`): if a countable measurable partition `P` of `X₃` has
`∑' n, negMulLog (μ (P n)) < ∞`, then the static conditional entropy of its σ-algebra is finite,

    HcondSig μ (σ (range P)) ⊥ ≠ ⊤.

This is the quantitative version of `Work.EKLC6Core.HcondSig_ne_top_of_measure_decay` (which only
assumes the *geometric* decay `μ (P n) ≤ 1/(n+2)²`): the tail term
`negMulLog (μ ((⋃_{k<l} P k)ᶜ))` is bounded by `1` (via `Real.negMulLog ≤ 1 - id`), and the
remaining finite sum by the `∑'`-bound, all inside `ℝ≥0∞` so that no summability side condition is
needed.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **The truncation bound**: the Shannon entropy of the `l`-th truncation of `P` is at most
`(∑' n, ofReal (negMulLog (μ (P n)))) + 1`, uniformly in `l`. -/
theorem ofReal_Hfam_truncPart_le_tsum {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (P : ℕ → Set X3)
    (hPmeas : ∀ n : ℕ, MeasurableSet (P n))
    (hPdisj : ∀ m n : ℕ, m ≠ n → Disjoint (P m) (P n)) (l : ℕ) :
    ENNReal.ofReal (@Hfam X3 instMeasurableSpaceX3 (Fin (truncPart P hPmeas hPdisj l).n) _
        μ (truncPart P hPmeas hPdisj l).parts)
      ≤ (∑' n : ℕ, ENNReal.ofReal (Real.negMulLog ((μ (P n)).toReal))) + 1 := by
  rw [Hfam_truncPart_eq μ P hPmeas hPdisj l]
  refine le_trans (ENNReal.ofReal_add_le) ?_
  refine add_le_add ?_ ?_
  · -- the finite sum of `ofReal (negMulLog (μ (P k)))`
    have hsum : ENNReal.ofReal (∑ k : Fin l, Real.negMulLog ((μ (P k)).toReal))
        = ∑ k : Fin l, ENNReal.ofReal (Real.negMulLog ((μ (P k)).toReal)) :=
      ENNReal.ofReal_sum_of_nonneg (fun k _ =>
        Real.negMulLog_nonneg ENNReal.toReal_nonneg (by
          rw [← ENNReal.toReal_one]
          refine ENNReal.toReal_mono ENNReal.one_ne_top ?_
          rw [← MeasureTheory.measure_univ (μ := μ)]
          exact MeasureTheory.measure_mono (Set.subset_univ _)))
    rw [hsum]
    rw [Fin.sum_univ_eq_sum_range (fun n => ENNReal.ofReal (Real.negMulLog ((μ (P n)).toReal))) l]
    simpa using ENNReal.sum_le_tsum (Finset.range l)
      (f := fun n => ENNReal.ofReal (Real.negMulLog ((μ (P n)).toReal)))
  · -- the tail term is at most `1`
    have hx : (0:ℝ) ≤ (μ ((⋃ j : Fin l, P (j:ℕ))ᶜ)).toReal := ENNReal.toReal_nonneg
    have h1 : Real.negMulLog ((μ ((⋃ j : Fin l, P (j:ℕ))ᶜ)).toReal) ≤ 1 :=
      le_trans (Real.negMulLog_le_one_sub_self hx) (by linarith)
    calc ENNReal.ofReal (Real.negMulLog ((μ ((⋃ j : Fin l, P (j:ℕ))ᶜ)).toReal))
        ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal h1
      _ = 1 := ENNReal.ofReal_one

/-- **Pisa 7.50, `∑'`-form.**  A countable measurable partition with summable Shannon entropy
generates a σ-algebra of finite static conditional entropy. -/
theorem HcondSig_ne_top_of_tsum {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (P : ℕ → Set X3)
    (hPmeas : ∀ n : ℕ, MeasurableSet (P n))
    (hPdisj : ∀ m n : ℕ, m ≠ n → Disjoint (P m) (P n))
    (htsum : (∑' n : ℕ, ENNReal.ofReal (Real.negMulLog ((μ (P n)).toReal))) ≠ ⊤) :
    @HcondSig X3 instMeasurableSpaceX3 μ
      (MeasurableSpace.generateFrom (Set.range P))
      (⊥ : MeasurableSpace X3) ≠ ⊤ := by
  classical
  set B : ℝ≥0∞ := (∑' n : ℕ, ENNReal.ofReal (Real.negMulLog ((μ (P n)).toReal))) + 1 with hB
  have hBtop : B ≠ ⊤ := by
    rw [hB]
    exact ENNReal.add_ne_top.mpr ⟨htsum, ENNReal.one_ne_top⟩
  have hmono : Monotone fun l =>
      @partSigma X3 instMeasurableSpaceX3 (truncPart P hPmeas hPdisj l) :=
    monotone_nat_of_le_succ (fun l => partSigma_truncPart_mono l)
  have hSm : ∀ l : ℕ, @partSigma X3 instMeasurableSpaceX3 (truncPart P hPmeas hPdisj l)
      ≤ instMeasurableSpaceX3 := by
    intro l
    rw [partSigma]
    exact MeasurableSpace.generateFrom_le (by
      rintro s ⟨i, rfl⟩
      exact (@FinPart.measurable X3 instMeasurableSpaceX3
        (truncPart P hPmeas hPdisj l)) i)
  have hbound : ∀ R : {R : @FinPart X3 instMeasurableSpaceX3 //
      @partSigma X3 instMeasurableSpaceX3 R ≤ MeasurableSpace.generateFrom (Set.range P)},
      ENNReal.ofReal (@Hcond X3 instMeasurableSpaceX3 μ R.1 (⊥ : MeasurableSpace X3)) ≤ B := by
    intro R
    have hR : @partSigma X3 instMeasurableSpaceX3 R.1
        ≤ ⨆ l, @partSigma X3 instMeasurableSpaceX3 (truncPart P hPmeas hPdisj l) := by
      rw [iSup_partSigma_truncPart]; exact R.2
    have h1 := ofReal_Hcond_le_iSup_of_partSigma_iSup (mX := instMeasurableSpaceX3) μ R.1
      (fun l => truncPart P hPmeas hPdisj l) hmono bot_le hSm hR
    refine le_trans h1 (iSup_le (fun l => ?_))
    have h2 : ENNReal.ofReal (@Hcond X3 instMeasurableSpaceX3 μ
        (truncPart P hPmeas hPdisj l) (⊥ : MeasurableSpace X3)) ≤ B := by
      rw [Hcond_bot_eq_Hfam (mX := instMeasurableSpaceX3)]
      rw [hB]
      exact ofReal_Hfam_truncPart_le_tsum (μ := μ) P hPmeas hPdisj l
    exact h2
  have hle : @HcondSig X3 instMeasurableSpaceX3 μ
      (MeasurableSpace.generateFrom (Set.range P)) (⊥ : MeasurableSpace X3) ≤ B := by
    rw [HcondSig]
    exact iSup_le hbound
  exact ne_top_of_lt (lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hBtop))

end Work.EKLC6Core

end
