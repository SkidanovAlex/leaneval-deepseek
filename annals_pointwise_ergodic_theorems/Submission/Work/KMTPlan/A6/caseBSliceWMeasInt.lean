import Mathlib
import Submission.Work.KMTPlan.A6.LowModelVarCaseBDefs
import Submission.Work.KMTPlan.A6.btwistExNtjSliceBound

namespace Work.KMTPlan.A6

open MeasureTheory

/-- Measurability in `t` and interval integrability on `[1/2, 1]` of the slices of the weighted
family `t ↦ w n t * caseBMasked … t n x`.

The measurability of every slice is that of `BtwistEx` applied to the two modified bumps
(`btwistExNtjSliceBound`), multiplied by the weight `w n`.  The uniform bound in `t ∈ [1/2,1]` of
the same slice (`btwistExNtjSliceBound`, second component), valid on `lowSmallSet`, together with
the bound `hwbd` on the weight on the same set, gives a uniform bound of the product on the compact
interval `[1/2,1]`; a measurable function bounded on `[1/2,1]` is interval integrable there. -/
theorem caseBSliceWMeasInt
    (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (u : ℕ) (w : ℕ → ℝ → ℂ)
    (hwm : ∀ n : ℕ, Measurable (w n))
    (hwbd : ∀ n : ℕ, Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n →
      ∃ C : ℝ, ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ‖w n t‖ ≤ C)
    (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
    (hk₁ : k₁ ≠ 0 ∨ 0 ≤ j₁) (hk₂ : k₂ ≠ 0 ∨ 0 ≤ j₂)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count) :
    (∀ (n : ℕ) (x : ℤ), Measurable (fun t : ℝ =>
        w n t * Work.KMTPlan.A6.caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)) ∧
      (∀ (n : ℕ) (x : ℤ), IntervalIntegrable (fun t : ℝ =>
        w n t * Work.KMTPlan.A6.caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)
        MeasureTheory.volume (1 / 2) 1) := by
  classical
  -- Every slice of the clamped single-scale family is measurable in `t` and bounded on `[1/2,1]`.
  have key : ∀ (n : ℕ) (x : ℤ),
      Measurable (fun t : ℝ =>
        w n t * Work.KMTPlan.A6.caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x) ∧
      (∃ C : ℝ, ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1,
        ‖w n t * Work.KMTPlan.A6.caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x‖ ≤ C) := by
    intro n x
    by_cases hsl : Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
    · -- On `lowSmallSet` the mask is the identity and both factors are controlled.
      obtain ⟨hm, hb⟩ := Work.KMTPlan.A6.btwistExNtjSliceBound ρ P l₁ l₂
        (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))
        (Nat.floor (a n)) k₁ k₂ j₁ j₂ hj₁ hj₂ hk₁ hk₂ f g hf hg x
      obtain ⟨Cw, hCw⟩ := hwbd n hsl
      obtain ⟨Cb, hCb⟩ := hb
      have hEq : (fun t : ℝ =>
            w n t * Work.KMTPlan.A6.caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)
          = fun t : ℝ => w n t * Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂
              (Work.KMTAreas.A7.mStarF
                (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
              (Work.KMTAreas.A7.mStargF P.natDegree
                (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
              (Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) k₁ j₁ t) f)
              (Work.KMTAreas.A7.Tm ρ l₂
                (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t) g) x := by
        funext t
        simp only [Work.KMTPlan.A6.caseBMasked]
        rw [if_pos hsl]
      refine ⟨hEq ▸ (hwm n).mul hm, ⟨max Cw 0 * max Cb 0, fun t ht => ?_⟩⟩
      rw [congrFun hEq t, norm_mul]
      exact mul_le_mul (le_trans (hCw t ht) (le_max_left _ _))
        (le_trans (hCb t ht) (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
    · -- Off `lowSmallSet` the slice vanishes.
      have hEq : (fun t : ℝ =>
            w n t * Work.KMTPlan.A6.caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)
          = fun _ : ℝ => (0 : ℂ) := by
        funext t
        simp only [Work.KMTPlan.A6.caseBMasked]
        rw [if_neg hsl, mul_zero]
      refine ⟨hEq ▸ measurable_const, ⟨0, fun t _ => ?_⟩⟩
      rw [congrFun hEq t]
      simp
  refine ⟨fun n x => (key n x).1, fun n x => ?_⟩
  obtain ⟨hm, C, hC⟩ := key n x
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  refine MeasureTheory.IntegrableOn.of_bound measure_Icc_lt_top
    hm.aestronglyMeasurable.restrict C ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  exact Filter.Eventually.of_forall (fun t ht => hC t ht)

end Work.KMTPlan.A6
