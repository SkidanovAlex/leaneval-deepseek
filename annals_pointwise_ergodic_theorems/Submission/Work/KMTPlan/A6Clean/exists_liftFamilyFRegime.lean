import Mathlib
import Submission.Work.KMTPlan.A6Clean.MdlLiftRegimeDefs

namespace Work.KMTPlan.A6Clean

open MeasureTheory
open scoped BigOperators ENNReal NNReal

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- **The `f`-side window-piece lift family, in the regime.**  The pointwise lifts
`Work.KMTPlan.A6Clean.mdlWindowLiftF` are assembled into a single family `W : ℕ → Circ → ℝ → ℂ`
over all scales `n` on which the model core `mdlCore` holds (with the regime conditions supplied by
`hreg`), and `W n = 0` off the core. -/
theorem exists_liftFamilyFRegime (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (C₀ : ℕ) (a : ℕ → NNReal) (f : ℤ → ℂ)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (l₁ l₂ k₁ k₂ : ℕ) (j₁ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ))
    (hk₁ : k₁ = 0 → j₁ ≠ -1) (t : ℝ) (hl₁ : l₁ ≠ 0)
    (hreg : ∀ n, Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n →
        Work.KMTPlan.A6Clean.MdlLiftRegimeF ρ a l₁ l₂ k₁ k₂ j₁ t n) :
    ∃ W : ℕ → Work.Analysis.IonescuWainger.Circle → ℝ → ℂ,
      (∀ (n : ℕ) (α : Work.Analysis.IonescuWainger.Circle), Measurable (W n α)) ∧
      (∀ (n : ℕ) (α : Work.Analysis.IonescuWainger.Circle),
        Work.KMTAreas.A7Rep.HasRealFreqSupport (W n α)
        (Set.Icc (-((2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))))
          ((2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))))) ∧
      (∀ (n : ℕ) (α : Work.Analysis.IonescuWainger.Circle),
        α ∉ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁ → W n α = 0) ∧
      (∀ (n : ℕ) (α : Work.Analysis.IonescuWainger.Circle),
        α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁ → ∀ x : ℤ,
        W n α (x : ℝ) = Work.KMTAreas.A7.winConvR (Work.KMTAreas.A7.mStarF
            (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
          (Work.KMTAreas.A7.winModR (-α) (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n)) x) ∧
      (∀ (n : ℕ) (z : ℤ), Summable (fun j : ℤ =>
        Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF
            (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))) j *
          Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n (z - j))) ∧
      (∀ n, ¬ Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → W n = fun _ _ => (0 : ℂ)) := by
  classical
  have hex : ∀ n : ℕ, ∃ W : Circ → ℝ → ℂ,
      (∀ α : Circ, Measurable (W α)) ∧
      (∀ α : Circ, Work.KMTAreas.A7Rep.HasRealFreqSupport (W α)
        (Set.Icc (-((2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))))
          ((2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))))) ∧
      (∀ α : Circ, α ∉ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁ → W α = 0) ∧
      (∀ α : Circ, α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁ → ∀ x : ℤ,
        W α (x : ℝ) = Work.KMTAreas.A7.winConvR (Work.KMTAreas.A7.mStarF
            (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
          (Work.KMTAreas.A7.winModR (-α) (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n)) x) ∧
      (∀ z : ℤ, Summable (fun j : ℤ =>
        Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF
            (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))) j *
          Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n (z - j))) ∧
      (¬ Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → W = fun _ _ => (0 : ℂ)) := by
    intro n
    by_cases hc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
    · obtain ⟨hN, hrad, hnA, hΦ, hsepU⟩ := hreg n hc
      obtain ⟨W, h1, h2, h3, h4, h5⟩ :=
        Work.KMTPlan.A6Clean.mdlWindowLiftF ρ hρ hρ1 P hd C₀ a f hf l₁ l₂ k₁ k₂ j₁ hj₁ hk₁ t n
          hN hl₁ hrad hnA hΦ hsepU
      exact ⟨W, h1, h2, h3, h4, h5, fun hnc => absurd hc hnc⟩
    · have hzero : Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n = 0 := by
        rw [Work.KMTPlan.A6.mdlSliceF, if_neg hc]
      refine ⟨fun _ _ => 0, fun α => measurable_const, fun α => hasRealFreqSupport_zero _,
        fun α _ => rfl, ?_, ?_, fun _ => rfl⟩
      · intro α hα x
        rw [hzero]
        simp [Work.KMTAreas.A7.winModR, Work.KMTAreas.A7.winConvR]
      · intro z
        simp [hzero]
  choose W hW using hex
  exact ⟨W, fun n α => (hW n).1 α, fun n α => (hW n).2.1 α, fun n α => (hW n).2.2.1 α,
    fun n α hα x => (hW n).2.2.2.1 α hα x, fun n z => (hW n).2.2.2.2.1 z,
    fun n hnc => (hW n).2.2.2.2.2 hnc⟩

end Work.KMTPlan.A6Clean
