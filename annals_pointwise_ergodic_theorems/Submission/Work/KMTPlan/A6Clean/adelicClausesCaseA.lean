import Mathlib
import Submission.Work.KMTPlan.A6Clean.MdlLiftRegimeDefs
import Submission.Work.KMTPlan.A6Clean.AdelicClausesAt
import Submission.Work.KMTPlan.A6Clean.packetFamG_minorArc
import Submission.Work.KMTPlan.A6Clean.pfFUniformAlt
import Submission.Work.KMTPlan.A6Clean.pfGUniformAlt

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.KMTPlan.A6Clean

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7
open Work.KMTAreas.A7Rep
open Work.KMTPlan.A6

local notation "Circ" => Work.Analysis.IonescuWainger.Circle
local notation "logN" => Work.Analysis.EndVar.logN

noncomputable section

/-! ## The two lift families -/

/-- The window convolution of the zero sequence vanishes. -/
private lemma winConvR_winModR_zero (m : ℝ → ℂ) (α : Circ) :
    winConvR m (winModR (-α) (fun _ : ℤ => (0 : ℂ))) = 0 := by
  funext x
  simp [winConvR, winModR]

/-- **The `f`-side lift family of the `f`-side window pieces**, at every scale (the lift at the
core scales, `0` off the core). -/
private lemma exists_liftFamilyF (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (C₀ : ℕ) (a : ℕ → NNReal) (f : ℤ → ℂ)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (l₁ l₂ k₁ k₂ : ℕ) (j₁ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ))
    (hk₁ : k₁ = 0 → j₁ ≠ -1) (t : ℝ) (hl₁ : l₁ ≠ 0)
    (hreg : ∀ n, mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → MdlLiftRegimeF ρ a l₁ l₂ k₁ k₂ j₁ t n) :
    ∃ W : ℕ → Circ → ℝ → ℂ,
      (∀ (n : ℕ) (α : Circ), Measurable (W n α)) ∧
      (∀ (n : ℕ) (α : Circ), HasRealFreqSupport (W n α)
        (Set.Icc (-((2 : ℝ) ^ ((k₁ : ℝ) - ((logN (Nat.floor (a n)) : ℤ) : ℝ))))
          ((2 : ℝ) ^ ((k₁ : ℝ) - ((logN (Nat.floor (a n)) : ℤ) : ℝ))))) ∧
      (∀ (n : ℕ) (α : Circ), α ∉ iwArithFreqsNew ρ l₁ → W n α = 0) ∧
      (∀ (n : ℕ) (α : Circ), α ∈ iwArithFreqs ρ l₁ → ∀ x : ℤ,
        W n α (x : ℝ) = winConvR (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂)))
          (winModR (-α) (mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n)) x) ∧
      (∀ (n : ℕ) (z : ℤ), Summable (fun j : ℤ =>
        cw (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂))) j *
          mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n (z - j))) ∧
      (∀ n, ¬ mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → W n = fun _ _ => (0 : ℂ)) := by
  classical
  have key : ∀ n, mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → ∃ W₀ : Circ → ℝ → ℂ,
      (∀ α, Measurable (W₀ α)) ∧
      (∀ α, HasRealFreqSupport (W₀ α)
        (Set.Icc (-((2 : ℝ) ^ ((k₁ : ℝ) - ((logN (Nat.floor (a n)) : ℤ) : ℝ))))
          ((2 : ℝ) ^ ((k₁ : ℝ) - ((logN (Nat.floor (a n)) : ℤ) : ℝ))))) ∧
      (∀ α, α ∉ iwArithFreqsNew ρ l₁ → W₀ α = 0) ∧
      (∀ α, α ∈ iwArithFreqs ρ l₁ → ∀ x : ℤ,
        W₀ α (x : ℝ) = winConvR (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂)))
          (winModR (-α) (mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n)) x) ∧
      (∀ z : ℤ, Summable (fun j : ℤ =>
        cw (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂))) j *
          mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n (z - j))) := by
    intro n h
    exact mdlWindowLiftF ρ hρ hρ1 P hd C₀ a f hf l₁ l₂ k₁ k₂ j₁ hj₁ hk₁ t n
      (hreg n h).1 hl₁ (hreg n h).2.1 (hreg n h).2.2.1 (hreg n h).2.2.2.1 (hreg n h).2.2.2.2
  refine ⟨fun n => if h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then Classical.choose (key n h)
      else fun _ _ => 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n α
    by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
    · simp only [dif_pos h]
      exact (Classical.choose_spec (key n h)).1 α
    · simp only [dif_neg h]
      exact measurable_const
  · intro n α
    by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
    · simp only [dif_pos h]
      exact (Classical.choose_spec (key n h)).2.1 α
    · simp only [dif_neg h]
      exact hasRealFreqSupport_zero _
  · intro n α hα
    by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
    · simp only [dif_pos h]
      exact (Classical.choose_spec (key n h)).2.2.1 α hα
    · simp only [dif_neg h]
      rfl
  · intro n α hα x
    by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
    · simp only [dif_pos h]
      exact (Classical.choose_spec (key n h)).2.2.2.1 α hα x
    · simp only [dif_neg h]
      have hz : mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n = fun _ : ℤ => (0 : ℂ) := by
        simp only [mdlSliceF, h, if_false]
        rfl
      rw [hz, winConvR_winModR_zero]
      rfl
  · intro n z
    by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
    · exact (Classical.choose_spec (key n h)).2.2.2.2 z
    · have hz : mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n = fun _ : ℤ => (0 : ℂ) := by
        simp only [mdlSliceF, h, if_false]
        rfl
      rw [hz]
      simp [mul_zero]
  · intro n h
    simp only [dif_neg h]

/-- **The `g`-side lift family of the `g`-side window pieces.** -/
private lemma exists_liftFamilyG (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (C₀ : ℕ) (a : ℕ → NNReal) (g : ℤ → ℂ)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
    (l₁ l₂ k₁ k₂ : ℕ) (j₂ : ℤ) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
    (hk₂ : k₂ = 0 → j₂ ≠ -1) (t : ℝ) (hl₂ : l₂ ≠ 0)
    (hreg : ∀ n, mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → MdlLiftRegimeG ρ P a l₁ l₂ k₁ k₂ j₂ t n) :
    ∃ W : ℕ → Circ → ℝ → ℂ,
      (∀ (n : ℕ) (β : Circ), Measurable (W n β)) ∧
      (∀ (n : ℕ) (β : Circ), HasRealFreqSupport (W n β)
        (Set.Icc (-((2 : ℝ) ^ ((P.natDegree : ℝ) *
              ((k₂ : ℝ) - ((logN (Nat.floor (a n)) : ℤ) : ℝ)))))
          ((2 : ℝ) ^ ((P.natDegree : ℝ) *
              ((k₂ : ℝ) - ((logN (Nat.floor (a n)) : ℤ) : ℝ)))))) ∧
      (∀ (n : ℕ) (β : Circ), β ∉ iwArithFreqsNew ρ l₂ → W n β = 0) ∧
      (∀ (n : ℕ) (β : Circ), β ∈ iwArithFreqs ρ l₂ → ∀ x : ℤ,
        W n β (x : ℝ) = winConvR (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂)))
          (winModR (-β) (mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n)) x) ∧
      (∀ (n : ℕ) (z : ℤ), Summable (fun j : ℤ =>
        cw (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂))) j *
          mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n (z - j))) ∧
      (∀ n, ¬ mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → W n = fun _ _ => (0 : ℂ)) := by
  classical
  have key : ∀ n, mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → ∃ W₀ : Circ → ℝ → ℂ,
      (∀ β, Measurable (W₀ β)) ∧
      (∀ β, HasRealFreqSupport (W₀ β)
        (Set.Icc (-((2 : ℝ) ^ ((P.natDegree : ℝ) *
              ((k₂ : ℝ) - ((logN (Nat.floor (a n)) : ℤ) : ℝ)))))
          ((2 : ℝ) ^ ((P.natDegree : ℝ) *
              ((k₂ : ℝ) - ((logN (Nat.floor (a n)) : ℤ) : ℝ)))))) ∧
      (∀ β, β ∉ iwArithFreqsNew ρ l₂ → W₀ β = 0) ∧
      (∀ β, β ∈ iwArithFreqs ρ l₂ → ∀ x : ℤ,
        W₀ β (x : ℝ) = winConvR (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂)))
          (winModR (-β) (mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n)) x) ∧
      (∀ z : ℤ, Summable (fun j : ℤ =>
        cw (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂))) j *
          mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n (z - j))) := by
    intro n h
    exact mdlWindowLiftG ρ hρ hρ1 P hd C₀ a g hg l₁ l₂ k₁ k₂ j₂ hj₂ hk₂ t n
      (hreg n h).1 hl₂ (hreg n h).2.1 (hreg n h).2.2.1 (hreg n h).2.2.2.1 (hreg n h).2.2.2.2
  refine ⟨fun n => if h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then Classical.choose (key n h)
      else fun _ _ => 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n β
    by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
    · simp only [dif_pos h]
      exact (Classical.choose_spec (key n h)).1 β
    · simp only [dif_neg h]
      exact measurable_const
  · intro n β
    by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
    · simp only [dif_pos h]
      exact (Classical.choose_spec (key n h)).2.1 β
    · simp only [dif_neg h]
      exact hasRealFreqSupport_zero _
  · intro n β hβ
    by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
    · simp only [dif_pos h]
      exact (Classical.choose_spec (key n h)).2.2.1 β hβ
    · simp only [dif_neg h]
      rfl
  · intro n β hβ x
    by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
    · simp only [dif_pos h]
      exact (Classical.choose_spec (key n h)).2.2.2.1 β hβ x
    · simp only [dif_neg h]
      have hz : mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n = fun _ : ℤ => (0 : ℂ) := by
        simp only [mdlSliceG, h, if_false]
        rfl
      rw [hz, winConvR_winModR_zero]
      rfl
  · intro n z
    by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
    · exact (Classical.choose_spec (key n h)).2.2.2.2 z
    · have hz : mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n = fun _ : ℤ => (0 : ℂ) := by
        simp only [mdlSliceG, h, if_false]
        rfl
      rw [hz]
      simp [mul_zero]
  · intro n h
    simp only [dif_neg h]

/-- **The structural clauses** (band, diagonal identity, `zmodAvg`-presentation, measurability) of
the §8 adelic form, for the explicit packet families `packetFamF ⋯ W₁` and `packetFamG ⋯ W₂`. -/
private lemma structuralClauses_explicit
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (t : ℝ)
    (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
    (hk₁ : k₁ = 0 → j₁ ≠ -1) (hk₂ : k₂ = 0 → j₂ ≠ -1)
    (W₁ W₂ : ℕ → Circ → ℝ → ℂ) (δ₁ δ₂ : ℕ → ℝ) (β : ℝ)
    (hβ : ∀ n, goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) →
      δ₁ n + δ₂ n ≤ β)
    (hW₁b : ∀ (n : ℕ) (α : Circ), HasRealFreqSupport (W₁ n α)
      (Set.Icc (-(δ₁ n)) (δ₁ n)))
    (hW₂b : ∀ (n : ℕ) (α : Circ), HasRealFreqSupport (W₂ n α)
      (Set.Icc (-(δ₂ n)) (δ₂ n)))
    (hW₁c : ∀ (n : ℕ) (α : Circ), Measurable (W₁ n α))
    (hW₂c : ∀ (n : ℕ) (α : Circ), Measurable (W₂ n α))
    (hW₁s : ∀ (n : ℕ) (α : Circ), α ∈ iwArithFreqs ρ l₁ → ∀ x : ℤ,
      W₁ n α (x : ℝ) = winConvR (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂)))
        (winModR (-α) (mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n)) x)
    (hW₂s : ∀ (n : ℕ) (α : Circ), α ∈ iwArithFreqs ρ l₂ → ∀ x : ℤ,
      W₂ n α (x : ℝ) = winConvR (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂)))
        (winModR (-α) (mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n)) x)
    (hW₁sum : ∀ (n : ℕ) (z : ℤ), Summable (fun j : ℤ =>
      cw (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂))) j *
        mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n (z - j)))
    (hW₂sum : ∀ (n : ℕ) (z : ℤ), Summable (fun j : ℤ =>
      cw (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂))) j *
        mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n (z - j))) :
    (∀ (n : ℕ) (ρ' : ℤ), HasRealFreqSupport (fun X : ℝ =>
        zmodAvg (negReflect P) (arithQ ρ (max l₁ l₂))
          (packetFamF ρ a l₁ l₂ k₁ k₂ W₁ n X) (packetFamG ρ a l₁ l₂ k₁ k₂ W₂ n X)
          (((ρ' : ℤ)) : ZMod (arithQ ρ (max l₁ l₂)))) (Set.Icc (-β) β)) ∧
    (∀ (n : ℕ) (x : ℤ), zmodAvg (negReflect P) (arithQ ρ (max l₁ l₂))
        (packetFamF ρ a l₁ l₂ k₁ k₂ W₁ n (x : ℝ))
        (packetFamG ρ a l₁ l₂ k₁ k₂ W₂ n (x : ℝ))
        (((x % ((arithQ ρ (max l₁ l₂) : ℕ) : ℤ) : ℤ)) : ZMod (arithQ ρ (max l₁ l₂)))
      = (if goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) then
          mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x else 0)) ∧
    (∀ (n : ℕ) (θ : ZMod (arithQ ρ (max l₁ l₂))),
        AEMeasurable (fun X : ℝ => packetFamF ρ a l₁ l₂ k₁ k₂ W₁ n X θ)) ∧
    (∀ (n : ℕ) (θ : ZMod (arithQ ρ (max l₁ l₂))),
        AEMeasurable (fun X : ℝ => packetFamG ρ a l₁ l₂ k₁ k₂ W₂ n X θ)) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n ρ'
    by_cases hg : goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n))
    · have hb₁ : ∀ θ : ZMod (arithQ ρ (max l₁ l₂)),
          HasRealFreqSupport (fun X : ℝ => packetFamF ρ a l₁ l₂ k₁ k₂ W₁ n X θ)
            (Set.Icc (-(δ₁ n)) (δ₁ n)) := by
        intro θ
        simpa only [packetFamF_apply] using
          hasRealFreqSupport_gatedProfile_nd ρ C₀ a l₁ l₂ k₁ k₂ l₁ W₁ hW₁b n θ
      have hb₂ : ∀ θ : ZMod (arithQ ρ (max l₁ l₂)),
          HasRealFreqSupport (fun X : ℝ => packetFamG ρ a l₁ l₂ k₁ k₂ W₂ n X θ)
            (Set.Icc (-(δ₂ n)) (δ₂ n)) := by
        intro θ
        simpa only [packetFamG_apply] using
          hasRealFreqSupport_gatedProfile_nd ρ C₀ a l₁ l₂ k₁ k₂ l₂ W₂ hW₂b n θ
      exact hasRealFreqSupport_zmodAvg_packets P (arithQ ρ (max l₁ l₂))
        (fun θ X => packetFamF ρ a l₁ l₂ k₁ k₂ W₁ n X θ)
        (fun θ X => packetFamG ρ a l₁ l₂ k₁ k₂ W₂ n X θ)
        hb₁ hb₂ (hβ n hg) (((ρ' : ℤ)) : ZMod (arithQ ρ (max l₁ l₂)))
    · have hz : (fun X : ℝ => zmodAvg (negReflect P) (arithQ ρ (max l₁ l₂))
            (packetFamF ρ a l₁ l₂ k₁ k₂ W₁ n X) (packetFamG ρ a l₁ l₂ k₁ k₂ W₂ n X)
            (((ρ' : ℤ)) : ZMod (arithQ ρ (max l₁ l₂)))) = fun _ : ℝ => 0 := by
        funext X
        have hF0 : packetFamF ρ a l₁ l₂ k₁ k₂ W₁ n X = fun _ : ZMod (arithQ ρ (max l₁ l₂)) =>
            (0 : ℂ) := by
          funext θ
          rw [packetFamF_apply, if_neg hg]
        have hG0 : packetFamG ρ a l₁ l₂ k₁ k₂ W₂ n X = fun _ : ZMod (arithQ ρ (max l₁ l₂)) =>
            (0 : ℂ) := by
          funext θ
          rw [packetFamG_apply, if_neg hg]
        rw [hF0, hG0]
        simp [zmodAvg]
      rw [hz]
      exact hasRealFreqSupport_zero _
  · intro n x
    rw [intCast_emod_eq (arithQ ρ (max l₁ l₂)) x]
    have h₁ : packetFamF ρ a l₁ l₂ k₁ k₂ W₁ n (x : ℝ) =
        fun θ : ZMod (arithQ ρ (max l₁ l₂)) =>
          if goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) then
            ∑ α ∈ iwArithFreqs ρ l₁, fourier (T := 1) (-(θ.val : ℤ)) α * W₁ n α (x : ℝ)
          else 0 := by
      funext θ
      rw [packetFamF_apply]
    have h₂ : packetFamG ρ a l₁ l₂ k₁ k₂ W₂ n (x : ℝ) =
        fun θ : ZMod (arithQ ρ (max l₁ l₂)) =>
          if goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) then
            ∑ β ∈ iwArithFreqs ρ l₂, fourier (T := 1) (-(θ.val : ℤ)) β * W₂ n β (x : ℝ)
          else 0 := by
      funext θ
      rw [packetFamG_apply]
    rw [h₁, h₂]
    exact zmodAvg_gated_packets_eq_slice ρ hρ hρ1 P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x
      hj₁ hj₂ hk₁ hk₂ (W₁ n) (W₂ n)
      (fun α hα => hW₁s n α hα x) (fun β hβ' => hW₂s n β hβ' x) (hW₁sum n) (hW₂sum n)
  · intro n θ
    simpa only [packetFamF_apply] using
      aemeasurable_packetProfile_nd ρ C₀ a l₁ l₂ k₁ k₂ l₁ W₁ hW₁c n θ
  · intro n θ
    simpa only [packetFamG_apply] using
      aemeasurable_packetProfile_nd ρ C₀ a l₁ l₂ k₁ k₂ l₂ W₂ hW₂c n θ

theorem adelicClausesCaseA (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hI : Work.KMTContract.ImprovKMT P) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (R : NNReal) (hR : 2 < R) (r : NNReal) (hr : 2 < r) (hrT : (r : ℝ) < Work.KMTPlan.A6.adelicRTop P) (j₁ j₂ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) : ∃ c : ℝ, 0 < c ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ Cin : NNReal → NNReal, ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f g : ℤ → ℂ), 1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → t ∈ Set.Icc (1 / 2 : ℝ) 1 → (k₁ = 0 → j₁ ≠ -1) → (k₂ = 0 → j₂ ≠ -1) → MeasureTheory.MemLp f 2 MeasureTheory.Measure.count → MeasureTheory.MemLp g 2 MeasureTheory.Measure.count → l₁ ≠ 0 → l₂ ≠ 0 → (∀ n, Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → Work.KMTPlan.A6Clean.MdlLiftRegimeF ρ a l₁ l₂ k₁ k₂ j₁ t n) → (∀ n, Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → Work.KMTPlan.A6Clean.MdlLiftRegimeG ρ P a l₁ l₂ k₁ k₂ j₂ t n) → Work.KMTPlan.A6Clean.AdelicClausesAt P ρ R r a Λ l₁ l₂ k₁ k₂ t j₁ j₂ f g C₀ c A Cin := by
  classical
  -- ### the three constant families
  obtain ⟨cb, hcb, hbile⟩ := MdlAdelicBileClausesOr P hd hI r hr hrT
  obtain ⟨AF, hAF, ρF, hρF, hKF⟩ := Work.A6Clean.PacketFamFUniformAlt C₀ hC₀ R hR j₁ hj₁
  obtain ⟨AG, hAG, ρG, hρG, hKG⟩ := Work.A6Clean.PacketFamGUniformAlt P hd C₀ hC₀ R hR j₂ hj₂
  refine ⟨cb, hcb, max AF AG, le_max_of_le_left hAF, min 1 (min ρF ρG),
    lt_min one_pos (lt_min hρF hρG), ?_⟩
  intro ρ hρ hρle
  have hρ1 : ρ ≤ 1 := le_trans hρle (min_le_left _ _)
  have hρF' : ρ ≤ ρF := le_trans hρle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρG' : ρ ≤ ρG := le_trans hρle (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨Cb, hCbpos, hbileC⟩ := hbile ρ hρ hρ1
  obtain ⟨KF, hKF'⟩ := hKF ρ hρ hρF'
  obtain ⟨KG, hKG'⟩ := hKG ρ hρ hρG'
  let Cin : NNReal → NNReal := fun Λ => ⟨max (max (max ((KF Λ : NNReal) : ℝ) ((KG Λ : NNReal) : ℝ))
      (Cb * (2 : ℝ) ^ cb)) 1, le_trans zero_le_one (le_max_right _ _)⟩
  refine ⟨Cin, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ t f g hΛ ha ha1 ht hk₁ hk₂ hf hg hl₁ hl₂ hregF hregG
  -- the loss-weight comparisons at the common exponent `max AF AG`
  have hKFi : ENNReal.ofReal (lossWeight AF ρ l₁ l₂ k₁ k₂)
      ≤ ENNReal.ofReal (lossWeight (max AF AG) ρ l₁ l₂ k₁ k₂) :=
    ENNReal.ofReal_le_ofReal (Work.KMTAreas.A7Hi.lossWeight_mono (le_max_left _ _) hAF hρ.le l₁ l₂ k₁ k₂)
  have hKGi : ENNReal.ofReal (lossWeight AG ρ l₁ l₂ k₁ k₂)
      ≤ ENNReal.ofReal (lossWeight (max AF AG) ρ l₁ l₂ k₁ k₂) :=
    ENNReal.ofReal_le_ofReal (Work.KMTAreas.A7Hi.lossWeight_mono (le_max_right _ _) hAG hρ.le l₁ l₂ k₁ k₂)
  have hpowF : (ENNReal.ofReal (lossWeight AF ρ l₁ l₂ k₁ k₂)) ^ (2 : ℕ)
      ≤ (ENNReal.ofReal (lossWeight (max AF AG) ρ l₁ l₂ k₁ k₂)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ zero_le hKFi 2
  have hpowG : (ENNReal.ofReal (lossWeight AG ρ l₁ l₂ k₁ k₂)) ^ (2 : ℕ)
      ≤ (ENNReal.ofReal (lossWeight (max AF AG) ρ l₁ l₂ k₁ k₂)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ zero_le hKGi 2
  have hlwA : (0 : ℝ) ≤ lossWeight (max AF AG) ρ l₁ l₂ k₁ k₂ :=
    le_trans zero_le_one
      (Work.KMTAreas.A7Hi.one_le_lossWeight_of_nonneg (max AF AG) ρ
        (le_trans hAF (le_max_left _ _)) hρ.le l₁ l₂ k₁ k₂)
  -- ### the two lift families and their bands
  obtain ⟨W₁, hW₁meas, hW₁band, hW₁zero, hW₁samp, hW₁sum, hW₁zeroCore⟩ :=
    exists_liftFamilyF ρ hρ hρ1 P hd C₀ a f hf l₁ l₂ k₁ k₂ j₁ hj₁ hk₁ t hl₁ hregF
  obtain ⟨W₂, hW₂meas, hW₂band, hW₂zero, hW₂samp, hW₂sum, hW₂zeroCore⟩ :=
    exists_liftFamilyG ρ hρ hρ1 P hd C₀ a g hg l₁ l₂ k₁ k₂ j₂ hj₂ hk₂ t hl₂ hregG
  let δ₁ : ℕ → ℝ := fun n => (2 : ℝ) ^ ((k₁ : ℝ) - ((logN (Nat.floor (a n)) : ℤ) : ℝ))
  let δ₂ : ℕ → ℝ :=
    fun n => (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - ((logN (Nat.floor (a n)) : ℤ) : ℝ)))
  let β : ℝ := 1 / (8 * (arithQ ρ (max l₁ l₂) : ℝ))
  have hβ : ∀ n, goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) →
      δ₁ n + δ₂ n ≤ β := by
    intro n hn
    simp only [δ₁, δ₂, β]
    exact goodScale_two_pow_bands_le (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂)
      (Nat.floor (a n)) k₁ k₂ P.natDegree hd (one_le_arithQ ρ (max l₁ l₂)) hn
      (le_trans (le_max_left k₁ k₂) (le_max_right _ _))
      (le_trans (le_max_right k₁ k₂) (le_max_right _ _))
  -- ### the structural clauses
  obtain ⟨hband, hdiag, humeas, hvmeas⟩ :=
    structuralClauses_explicit ρ hρ hρ1 P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t hj₁ hj₂ hk₁ hk₂
      W₁ W₂ δ₁ δ₂ β hβ hW₁band hW₂band hW₁meas hW₂meas hW₁samp hW₂samp hW₁sum hW₂sum
  haveI : NeZero (arithQ ρ (max l₁ l₂)) :=
    ⟨Nat.pos_iff_ne_zero.mp (arithQ_pos ρ (max l₁ l₂))⟩
  -- ### the arithmetic clauses
  have hminor : (∀ (n : ℕ) (X : ℝ), MdlIwMinorArc ρ (max l₁ l₂ - 1) (arithQ ρ (max l₁ l₂))
        (packetFamF ρ a l₁ l₂ k₁ k₂ W₁ n X)) ∨
      (∀ (n : ℕ) (X : ℝ), MdlIwMinorArc ρ (max l₁ l₂ - 1) (arithQ ρ (max l₁ l₂))
        (packetFamG ρ a l₁ l₂ k₁ k₂ W₂ n X)) := by
    rcases le_total l₂ l₁ with h21 | h12
    · left
      intro n X
      have hmax : max l₁ l₂ - 1 = l₁ - 1 := by rw [Nat.max_eq_left h21]
      rw [hmax]
      exact packetFamF_minorArc ρ hρ hρ1 a l₁ l₂ k₁ k₂ (W₁ n)
        (fun α hα => hW₁zero n α hα) n X
    · right
      intro n X
      have hmax : max l₁ l₂ - 1 = l₂ - 1 := by rw [Nat.max_eq_right h12]
      rw [hmax]
      exact packetFamG_minorArc ρ hρ hρ1 a l₁ l₂ k₁ k₂ (W₂ n)
        (fun β hβ' => hW₂zero n β hβ') n X
  have hb3 := hbileC (arithQ ρ (max l₁ l₂)) (max l₁ l₂ - 1)
    (packetFamF ρ a l₁ l₂ k₁ k₂ W₁) (packetFamG ρ a l₁ l₂ k₁ k₂ W₂) hminor
  obtain ⟨hbase, hB1, hB2⟩ := hb3
  let M : ℝ := Cb * (2 : ℝ) ^ (-(cb * (((max l₁ l₂ - 1 : ℕ)) : ℝ)))
  have hMnn : 0 ≤ M := by
    simp only [M]
    exact mul_nonneg hCbpos.le (Real.rpow_pos_of_pos (by norm_num) _).le
  have hMbound : ENNReal.ofReal M ≤ (Cin Λ : ENNReal)
      * ENNReal.ofReal ((2 : ℝ) ^ (-(cb * max (l₁ : ℝ) (l₂ : ℝ)))) := by
    have hmax1 : 1 ≤ max l₁ l₂ := le_trans (Nat.one_le_iff_ne_zero.mpr hl₁) (le_max_left _ _)
    have h2 : (2 : ℝ) ^ (-(cb * (((max l₁ l₂ - 1 : ℕ)) : ℝ)))
        = (2 : ℝ) ^ cb * (2 : ℝ) ^ (-(cb * ((max l₁ l₂ : ℕ) : ℝ))) := by
      rw [Nat.cast_sub hmax1, Nat.cast_one,
        show -(cb * (((max l₁ l₂ : ℕ) : ℝ) - 1))
            = -(cb * ((max l₁ l₂ : ℕ) : ℝ)) + cb by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      ring
    have hfac : M = (Cb * (2 : ℝ) ^ cb) * (2 : ℝ) ^ (-(cb * ((max l₁ l₂ : ℕ) : ℝ))) := by
      simp only [M]
      rw [h2]
      ring
    rw [hfac, ENNReal.ofReal_mul (by positivity), Nat.cast_max]
    refine mul_le_mul' ?_ le_rfl
    rw [← ENNReal.ofReal_coe_nnreal (p := Cin Λ)]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [Cin]
    exact le_trans (le_max_right (max ((KF Λ : NNReal) : ℝ) ((KG Λ : NNReal) : ℝ)) _)
      (le_max_left _ _)
  -- ### the `f`-side `(lin-1)` data bound
  have hband₁4 : ∀ (n : ℕ) (α : Circ),
      HasRealFreqSupport (W₁ n α) (Set.Icc (-(1 / 4 : ℝ)) (1 / 4)) := by
    intro n α
    by_cases hc : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
    · have hrad := (hregF n hc).2.1
      have hquarter : δ₁ n ≤ 1 / 4 := by
        have hU1 : (1 : ℤ) ≤ (uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ) := by
          exact_mod_cast one_le_uScale ρ hρ.le (lcL l₁ l₂ k₁ k₂)
        have h3 : (-(2 * (uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ)) - 1 : ℤ) ≤ -3 := by omega
        have h4 := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h3
        have h5 : (2 : ℝ) ^ ((-3 : ℤ)) = 1 / 8 := by norm_num
        rw [h5] at h4
        have h6 := hrad
        simp only [δ₁] at h6 ⊢
        linarith
      refine hasRealFreqSupport_mono (fun x hx => ?_) (hW₁band n α)
      simp only [Set.mem_Icc] at hx ⊢
      exact ⟨by linarith [hx.1, hquarter], by linarith [hx.2, hquarter]⟩
    · rw [hW₁zeroCore n hc]
      exact hasRealFreqSupport_zero _
  have hFint : ∫⁻ X : ℝ, (VrLiftDataP (R : ℝ) (arithQ ρ (max l₁ l₂))
        (fun n : ℕ => packetFamF ρ a l₁ l₂ k₁ k₂ W₁ n X)) ^ (2 : ℕ)
      ≤ (KF Λ : ENNReal) ^ (2 : ℕ)
        * (ENNReal.ofReal (lossWeight (max AF AG) ρ l₁ l₂ k₁ k₂)) ^ (2 : ℕ)
        * (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
    refine le_trans (hKF' a Λ l₁ l₂ k₁ k₂ t f W₁ hΛ ha ha1 hf ht hk₁ hband₁4
      (fun n α hα x => hW₁samp n α (mem_iwArithFreqsNew_le hα) x)
      (fun n α hα => hW₁zero n α hα)) ?_
    exact mul_le_mul' (mul_le_mul_right hpowF ((KF Λ : ENNReal) ^ (2 : ℕ))) le_rfl
  let F₂ : ℝ := (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count).toReal
  have hF₂ : ENNReal.ofReal F₂ = MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    simp only [F₂, ENNReal.ofReal_toReal (MeasureTheory.MemLp.eLpNorm_lt_top hf).ne]
  let Ku : ℝ := ((KF Λ : NNReal) : ℝ) * lossWeight (max AF AG) ρ l₁ l₂ k₁ k₂ * F₂
  have hKu_nn : 0 ≤ Ku := by
    simp only [Ku]
    exact mul_nonneg (mul_nonneg (NNReal.coe_nonneg _) hlwA) (ENNReal.toReal_nonneg)
  have hKu_eq : ENNReal.ofReal Ku = (KF Λ : ENNReal)
      * ENNReal.ofReal (lossWeight (max AF AG) ρ l₁ l₂ k₁ k₂)
      * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    rw [show Ku = ((KF Λ : NNReal) : ℝ) * lossWeight (max AF AG) ρ l₁ l₂ k₁ k₂ * F₂ from rfl,
      ENNReal.ofReal_mul (mul_nonneg (NNReal.coe_nonneg _) hlwA),
      ENNReal.ofReal_mul (NNReal.coe_nonneg _), hF₂, ENNReal.ofReal_coe_nnreal]
  have hKu_bound : ENNReal.ofReal Ku ≤ (Cin Λ : ENNReal)
      * ENNReal.ofReal (lossWeight (max AF AG) ρ l₁ l₂ k₁ k₂)
      * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    have hstep : (KF Λ : ENNReal) ≤ (Cin Λ : ENNReal) := by
      have h1 : ((KF Λ : NNReal) : ℝ) ≤ ((Cin Λ : NNReal) : ℝ) := by
        dsimp only [Cin]
        exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
      calc (KF Λ : ENNReal) = ENNReal.ofReal ((KF Λ : NNReal) : ℝ) :=
            (ENNReal.ofReal_coe_nnreal (p := KF Λ)).symm
        _ ≤ ENNReal.ofReal ((Cin Λ : NNReal) : ℝ) := ENNReal.ofReal_le_ofReal h1
        _ = (Cin Λ : ENNReal) := ENNReal.ofReal_coe_nnreal
    rw [hKu_eq]
    exact mul_le_mul'
      (mul_le_mul_left hstep (ENNReal.ofReal (lossWeight (max AF AG) ρ l₁ l₂ k₁ k₂))) le_rfl
  have hKu_int : ∫⁻ X : ℝ, (VrLiftDataP (R : ℝ) (arithQ ρ (max l₁ l₂))
        (fun n : ℕ => packetFamF ρ a l₁ l₂ k₁ k₂ W₁ n X)) ^ (2 : ℕ)
      ≤ ENNReal.ofReal (Ku ^ 2) := by
    rw [ENNReal.ofReal_pow hKu_nn, hKu_eq, mul_pow, mul_pow]
    exact hFint
  -- ### the `g`-side `(lin-2)` data bound
  have hband₂4 : ∀ (n : ℕ) (α : Circ),
      HasRealFreqSupport (W₂ n α) (Set.Icc (-(1 / 4 : ℝ)) (1 / 4)) := by
    intro n α
    by_cases hc : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
    · have hrad := (hregG n hc).2.1
      have hquarter : δ₂ n ≤ 1 / 4 := by
        have hU1 : (1 : ℤ) ≤ (uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ) := by
          exact_mod_cast one_le_uScale ρ hρ.le (lcL l₁ l₂ k₁ k₂)
        have h3 : (-((P.natDegree : ℤ) * 2 * (uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ)) - 1 : ℤ)
            ≤ -3 := by
          have hd2 : (2 : ℤ) ≤ (P.natDegree : ℤ) := by exact_mod_cast hd
          have hU1z : (1 : ℤ) ≤ (uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ) := by
            exact_mod_cast hU1
          nlinarith
        have h4 := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h3
        have h5 : (2 : ℝ) ^ ((-3 : ℤ)) = 1 / 8 := by norm_num
        rw [h5] at h4
        have h6 := hrad
        simp only [δ₂] at h6 ⊢
        linarith
      refine hasRealFreqSupport_mono (fun x hx => ?_) (hW₂band n α)
      simp only [Set.mem_Icc] at hx ⊢
      exact ⟨by linarith [hx.1, hquarter], by linarith [hx.2, hquarter]⟩
    · rw [hW₂zeroCore n hc]
      exact hasRealFreqSupport_zero _
  have hGint : ∫⁻ X : ℝ, (VrLiftDataP (R : ℝ) (arithQ ρ (max l₁ l₂))
        (fun n : ℕ => packetFamG ρ a l₁ l₂ k₁ k₂ W₂ n X)) ^ (2 : ℕ)
      ≤ (KG Λ : ENNReal) ^ (2 : ℕ)
        * (ENNReal.ofReal (lossWeight (max AF AG) ρ l₁ l₂ k₁ k₂)) ^ (2 : ℕ)
        * (MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
    refine le_trans (hKG' a Λ l₁ l₂ k₁ k₂ t g W₂ hΛ ha ha1 hg ht hk₂ hband₂4
      (fun n α hα x => hW₂samp n α (mem_iwArithFreqsNew_le hα) x)
      (fun n α hα => hW₂zero n α hα)) ?_
    exact mul_le_mul' (mul_le_mul_right hpowG ((KG Λ : ENNReal) ^ (2 : ℕ))) le_rfl
  let G₂ : ℝ := (MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count).toReal
  have hG₂ : ENNReal.ofReal G₂ = MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    simp only [G₂, ENNReal.ofReal_toReal (MeasureTheory.MemLp.eLpNorm_lt_top hg).ne]
  let Kv : ℝ := ((KG Λ : NNReal) : ℝ) * lossWeight (max AF AG) ρ l₁ l₂ k₁ k₂ * G₂
  have hKv_nn : 0 ≤ Kv := by
    simp only [Kv]
    exact mul_nonneg (mul_nonneg (NNReal.coe_nonneg _) hlwA) (ENNReal.toReal_nonneg)
  have hKv_eq : ENNReal.ofReal Kv = (KG Λ : ENNReal)
      * ENNReal.ofReal (lossWeight (max AF AG) ρ l₁ l₂ k₁ k₂)
      * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    rw [show Kv = ((KG Λ : NNReal) : ℝ) * lossWeight (max AF AG) ρ l₁ l₂ k₁ k₂ * G₂ from rfl,
      ENNReal.ofReal_mul (mul_nonneg (NNReal.coe_nonneg _) hlwA),
      ENNReal.ofReal_mul (NNReal.coe_nonneg _), hG₂, ENNReal.ofReal_coe_nnreal]
  have hKv_bound : ENNReal.ofReal Kv ≤ (Cin Λ : ENNReal)
      * ENNReal.ofReal (lossWeight (max AF AG) ρ l₁ l₂ k₁ k₂)
      * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    have hstep : (KG Λ : ENNReal) ≤ (Cin Λ : ENNReal) := by
      have h1 : ((KG Λ : NNReal) : ℝ) ≤ ((Cin Λ : NNReal) : ℝ) := by
        dsimp only [Cin]
        exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
      calc (KG Λ : ENNReal) = ENNReal.ofReal ((KG Λ : NNReal) : ℝ) :=
            (ENNReal.ofReal_coe_nnreal (p := KG Λ)).symm
        _ ≤ ENNReal.ofReal ((Cin Λ : NNReal) : ℝ) := ENNReal.ofReal_le_ofReal h1
        _ = (Cin Λ : ENNReal) := ENNReal.ofReal_coe_nnreal
    rw [hKv_eq]
    exact mul_le_mul'
      (mul_le_mul_left hstep (ENNReal.ofReal (lossWeight (max AF AG) ρ l₁ l₂ k₁ k₂))) le_rfl
  have hKv_int : ∫⁻ X : ℝ, (VrLiftDataP (R : ℝ) (arithQ ρ (max l₁ l₂))
        (fun n : ℕ => packetFamG ρ a l₁ l₂ k₁ k₂ W₂ n X)) ^ (2 : ℕ)
      ≤ ENNReal.ofReal (Kv ^ 2) := by
    rw [ENNReal.ofReal_pow hKv_nn, hKv_eq, mul_pow, mul_pow]
    exact hGint
  -- ### the assembly
  refine ⟨fun n X ρ' => zmodAvg (negReflect P) (arithQ ρ (max l₁ l₂))
      (packetFamF ρ a l₁ l₂ k₁ k₂ W₁ n X) (packetFamG ρ a l₁ l₂ k₁ k₂ W₂ n X)
      (((ρ' : ℤ)) : ZMod (arithQ ρ (max l₁ l₂))),
    packetFamF ρ a l₁ l₂ k₁ k₂ W₁, packetFamG ρ a l₁ l₂ k₁ k₂ W₂, M, Ku, Kv,
    hband, hdiag, ?_, ⟨hMnn, hMbound⟩, ⟨hKu_nn, hKu_bound⟩, ⟨hKv_nn, hKv_bound⟩,
    hKu_int, hKv_int, humeas, hvmeas, hbase, hB1, hB2⟩
  intro n X ρ'
  rfl

end

end Work.KMTPlan.A6Clean
