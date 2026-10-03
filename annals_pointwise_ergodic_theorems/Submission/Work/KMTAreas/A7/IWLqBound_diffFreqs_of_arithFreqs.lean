import Mathlib
import Submission.Work.KMTAreas.A7.FpieceEqTm
import Submission.Work.KMTAreas.integrable_iwSymbolSet_periodize

namespace Work.KMTAreas.A7

open MeasureTheory

open scoped ENNReal NNReal BigOperators

/-- For a finitely supported sequence `f`, the IW convolution with the symbol over a difference
`A \ B` (`B ⊆ A`) of frequency sets is the difference of the IW convolutions over `A` and `B`.
The finite-support hypothesis is essential: for arbitrary `f` the unconditional `tsum`s are not
additive, and this is exactly why the paper's functional calculus is used only on `ℓ^p`, `p < ∞`
(see the header of `FpieceEqTm.lean`). -/
theorem iwConv_sdiff_of_finsupp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {A B : Finset Work.Analysis.IonescuWainger.Circle}
    (hBA : B ⊆ A) {Φ : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hA : Integrable (Work.Analysis.IonescuWainger.iwSymbolSet A Φ)
      Work.Analysis.IonescuWainger.circleMeasure)
    (hB : Integrable (Work.Analysis.IonescuWainger.iwSymbolSet B Φ)
      Work.Analysis.IonescuWainger.circleMeasure)
    (f : ℤ → H) (hf : (Function.support f).Finite) :
    Work.Analysis.IWMultiplier.iwConv (A \ B) Φ f
      = fun n => Work.Analysis.IWMultiplier.iwConv A Φ f n
          - Work.Analysis.IWMultiplier.iwConv B Φ f n := by
  funext n
  have hs : ∀ m : ℤ, m ∉ hf.toFinset → f m = 0 := fun m hm => by
    by_contra hne
    exact hm (hf.mem_toFinset.mpr hne)
  rw [Work.Analysis.IWMultiplier.iwConv_apply_eq_sum (A \ B) Φ f hf.toFinset hs n,
    Work.Analysis.IWMultiplier.iwConv_apply_eq_sum A Φ f hf.toFinset hs n,
    Work.Analysis.IWMultiplier.iwConv_apply_eq_sum B Φ f hf.toFinset hs n,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun m _ => by
    rw [iwKernel_iwSymbolSet_sdiff hBA hA hB (n - m), sub_smul]

theorem IWLqBound_diffFreqs_of_arithFreqs (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ)
    (Φ : SchwartzMap ℝ ℂ) {q : ENNReal} (hq : 1 < q) {CA CB : NNReal}
    (hA : Work.Analysis.IWMultiplier.IWLqBound (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
      (Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ)) q CA)
    (hB : Work.Analysis.IWMultiplier.IWLqBound (Work.Analysis.IonescuWainger.iwArithFreqs ρ (l - 1))
      (Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ)) q CB) :
    Work.Analysis.IWMultiplier.IWLqBound (Work.KMTAreas.A7.diffFreqs ρ l)
      (Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ)) q (CA + CB) := by
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    rw [diffFreqs, if_pos rfl]
    exact Work.Analysis.IWMultiplier.IWLqBound.mono hA
      (le_add_of_nonneg_right (by positivity : (0 : NNReal) ≤ CB))
  · have hne : l ≠ 0 := Nat.pos_iff_ne_zero.mp hl
    have hsub : Work.Analysis.IonescuWainger.iwArithFreqs ρ (l - 1)
        ⊆ Work.Analysis.IonescuWainger.iwArithFreqs ρ l :=
      Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ1 (Nat.pred_le l)
    have hIntA : Integrable (Work.Analysis.IonescuWainger.iwSymbolSet
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ)))
        Work.Analysis.IonescuWainger.circleMeasure :=
      Work.KMTAreas.integrable_iwSymbolSet_periodize _ Φ
    have hIntB : Integrable (Work.Analysis.IonescuWainger.iwSymbolSet
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ (l - 1))
        (Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ)))
        Work.Analysis.IonescuWainger.circleMeasure :=
      Work.KMTAreas.integrable_iwSymbolSet_periodize _ Φ
    have hset : diffFreqs ρ l
        = Work.Analysis.IonescuWainger.iwArithFreqs ρ l
          \ Work.Analysis.IonescuWainger.iwArithFreqs ρ (l - 1) := by
      rw [diffFreqs, if_neg hne]
    intro H _ _ _ f hf
    have hpt : Work.Analysis.IWMultiplier.iwConv (diffFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ)) f
        = fun n => Work.Analysis.IWMultiplier.iwConv
              (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
              (Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ)) f n
            - Work.Analysis.IWMultiplier.iwConv
              (Work.Analysis.IonescuWainger.iwArithFreqs ρ (l - 1))
              (Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ)) f n := by
      rw [hset]
      exact iwConv_sdiff_of_finsupp hsub hIntA hIntB f hf
    rw [hpt]
    calc eLpNorm (fun n => Work.Analysis.IWMultiplier.iwConv
              (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
              (Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ)) f n
            - Work.Analysis.IWMultiplier.iwConv
              (Work.Analysis.IonescuWainger.iwArithFreqs ρ (l - 1))
              (Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ)) f n) q Measure.count
        ≤ eLpNorm (Work.Analysis.IWMultiplier.iwConv
              (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
              (Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ)) f) q Measure.count
          + eLpNorm (Work.Analysis.IWMultiplier.iwConv
              (Work.Analysis.IonescuWainger.iwArithFreqs ρ (l - 1))
              (Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ)) f) q Measure.count :=
          eLpNorm_sub_le
            (le_of_lt hq)
      _ ≤ ENNReal.ofReal (CA : ℝ) * eLpNorm f q Measure.count
          + ENNReal.ofReal (CB : ℝ) * eLpNorm f q Measure.count :=
          add_le_add (hA H f hf) (hB H f hf)
      _ = ENNReal.ofReal ((CA + CB : NNReal) : ℝ) * eLpNorm f q Measure.count := by
          rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
            NNReal.coe_add]

end Work.KMTAreas.A7
