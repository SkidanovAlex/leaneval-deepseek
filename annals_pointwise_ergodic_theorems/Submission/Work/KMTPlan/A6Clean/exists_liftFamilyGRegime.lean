import Mathlib
import Submission.Work.KMTPlan.A6Clean.MdlLiftRegimeDefs

namespace Work.KMTPlan.A6Clean

open MeasureTheory
open scoped BigOperators ENNReal NNReal

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- **The `g`-side window-piece lift family, in the regime.**  The pointwise lifts
`Work.KMTPlan.A6Clean.mdlWindowLiftG` are assembled into a single family `W : ℕ → Circ → ℝ → ℂ`
over all scales `n` on which the model core `mdlCore` holds (with the regime conditions supplied by
`hreg`), and `W n = 0` off the core. -/
theorem exists_liftFamilyGRegime (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (C₀ : ℕ) (a : ℕ → NNReal) (g : ℤ → ℂ)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
    (l₁ l₂ k₁ k₂ : ℕ) (j₂ : ℤ) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
    (hk₂ : k₂ = 0 → j₂ ≠ -1) (t : ℝ) (hl₂ : l₂ ≠ 0)
    (hreg : ∀ n, Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n →
        Work.KMTPlan.A6Clean.MdlLiftRegimeG ρ P a l₁ l₂ k₁ k₂ j₂ t n) :
    ∃ W : ℕ → Work.Analysis.IonescuWainger.Circle → ℝ → ℂ,
      (∀ (n : ℕ) (β : Work.Analysis.IonescuWainger.Circle), Measurable (W n β)) ∧
      (∀ (n : ℕ) (β : Work.Analysis.IonescuWainger.Circle),
        Work.KMTAreas.A7Rep.HasRealFreqSupport (W n β)
        (Set.Icc (-((2 : ℝ) ^ ((P.natDegree : ℝ) *
              ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)))))
          ((2 : ℝ) ^ ((P.natDegree : ℝ) *
              ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)))))) ∧
      (∀ (n : ℕ) (β : Work.Analysis.IonescuWainger.Circle),
        β ∉ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂ → W n β = 0) ∧
      (∀ (n : ℕ) (β : Work.Analysis.IonescuWainger.Circle),
        β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂ → ∀ x : ℤ,
        W n β (x : ℝ) = Work.KMTAreas.A7.winConvR (Work.KMTAreas.A7.mStargF P.natDegree
            (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
          (Work.KMTAreas.A7.winModR (-β) (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n)) x) ∧
      (∀ (n : ℕ) (z : ℤ), Summable (fun j : ℤ =>
        Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree
            (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))) j *
          Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n (z - j))) ∧
      (∀ n, ¬ Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → W n = fun _ _ => (0 : ℂ)) := by
  classical
  have hex : ∀ n : ℕ, ∃ W : Circ → ℝ → ℂ,
      (∀ β : Circ, Measurable (W β)) ∧
      (∀ β : Circ, Work.KMTAreas.A7Rep.HasRealFreqSupport (W β)
        (Set.Icc (-((2 : ℝ) ^ ((P.natDegree : ℝ) *
              ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)))))
          ((2 : ℝ) ^ ((P.natDegree : ℝ) *
              ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)))))) ∧
      (∀ β : Circ, β ∉ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂ → W β = 0) ∧
      (∀ β : Circ, β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂ → ∀ x : ℤ,
        W β (x : ℝ) = Work.KMTAreas.A7.winConvR (Work.KMTAreas.A7.mStargF P.natDegree
            (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
          (Work.KMTAreas.A7.winModR (-β)
            (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n)) x) ∧
      (∀ z : ℤ, Summable (fun j : ℤ =>
        Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree
            (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))) j *
          Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n (z - j))) ∧
      (¬ Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → W = fun _ _ => (0 : ℂ)) := by
    intro n
    by_cases hc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
    · obtain ⟨hN, hrad, hnA, hΦ, hsepU⟩ := hreg n hc
      obtain ⟨W, h1, h2, h3, h4, h5⟩ :=
        Work.KMTPlan.A6Clean.mdlWindowLiftG ρ hρ hρ1 P hd C₀ a g hg l₁ l₂ k₁ k₂ j₂ hj₂ hk₂ t n
          hN hl₂ hrad hnA hΦ hsepU
      exact ⟨W, h1, h2, h3, h4, h5, fun hnc => absurd hc hnc⟩
    · have hzero : Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n = 0 := by
        rw [Work.KMTPlan.A6.mdlSliceG, if_neg hc]
      refine ⟨fun _ _ => 0, fun β => measurable_const, fun β => hasRealFreqSupport_zero _,
        fun β _ => rfl, ?_, ?_, fun _ => rfl⟩
      · intro β hβ x
        rw [hzero]
        simp [Work.KMTAreas.A7.winModR, Work.KMTAreas.A7.winConvR]
      · intro z
        simp [hzero]
  choose W hW using hex
  exact ⟨W, fun n β => (hW n).1 β, fun n β => (hW n).2.1 β, fun n β => (hW n).2.2.1 β,
    fun n β hβ x => (hW n).2.2.2.1 β hβ x, fun n z => (hW n).2.2.2.2.1 z,
    fun n hnc => (hW n).2.2.2.2.2 hnc⟩

end Work.KMTPlan.A6Clean
