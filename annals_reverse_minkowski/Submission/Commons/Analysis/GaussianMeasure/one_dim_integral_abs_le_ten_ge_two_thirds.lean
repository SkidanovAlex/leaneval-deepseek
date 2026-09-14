import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.GaussianMeasure.one_dim_tail_ten_le_sixth

noncomputable section

open Real MeasureTheory Set
open scoped Real

namespace Commons.Analysis.GaussianMeasure

/-- The Gaussian density `exp (-π x²)` is even. -/
private lemma gaussian_even (x : ℝ) :
    Real.exp (-Real.pi * (-x) ^ 2) = Real.exp (-Real.pi * x ^ 2) := by
  congr 1
  ring

theorem one_dim_integral_abs_le_ten_ge_two_thirds :
    (2 : ℝ) / 3 ≤ ∫ x in {x : ℝ | |x| ≤ 10}, Real.exp (-Real.pi * x ^ 2) := by
  let f : ℝ → ℝ := fun x => Real.exp (-Real.pi * x ^ 2)
  let s : Set ℝ := {x : ℝ | |x| ≤ 10}
  change (2 : ℝ) / 3 ≤ ∫ x in s, f x
  -- Basic analytic facts
  have hf_int : Integrable f := by
    dsimp [f]
    exact integrable_exp_neg_mul_sq (b := Real.pi) Real.pi_pos
  have hmeas_s : MeasurableSet s := by
    dsimp [s]
    rw [show {x : ℝ | |x| ≤ 10} = Set.Icc (-10) 10 by ext x; simp [abs_le]]
    exact measurableSet_Icc
  have htot : (∫ x : ℝ, f x) = 1 := by
    dsimp [f]
    rw [integral_gaussian]
    have hsq : Real.sqrt (Real.pi / Real.pi) = 1 := by
      rw [div_self (ne_of_gt Real.pi_pos)]
      simp
    exact hsq
  -- Complement of the interval
  have hS_eq : s = Set.Icc (-10) (10 : ℝ) := by
    dsimp [s]
    ext x
    simp [abs_le]
  have hScc_eq : sᶜ = Set.Iio (-10) ∪ Set.Ioi (10 : ℝ) := by
    rw [hS_eq]
    ext x
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
    constructor
    · intro hx
      by_cases h1 : x < -10
      · exact Or.inl h1
      · right
        by_contra h2
        exact hx ⟨le_of_not_gt h1, le_of_not_gt h2⟩
    · rintro (h1 | h2) hcc
      · linarith [hcc.1]
      · linarith [hcc.2]
  -- Tail bound from the shared library
  have htail : (∫ x in Set.Ioi (10 : ℝ), f x) ≤ 1 / 6 := by
    dsimp [f]
    exact one_dim_tail_ten_le_sixth
  -- The negative tail equals the positive tail (reflection, evenness)
  have hneg_eq : (∫ x in Set.Iio (-10), f x) = ∫ x in Set.Ioi (10 : ℝ), f x := by
    calc
      (∫ x in Set.Iio (-10), f x) = ∫ x in Set.Iic (-10), f x := by
        exact (MeasureTheory.integral_Iic_eq_integral_Iio (μ := (volume : Measure ℝ))
          (x := (-10 : ℝ)) (f := f)).symm
      _ = ∫ x in Set.Ioi (10 : ℝ), f (-x) := by
        rw [integral_comp_neg_Ioi]
      _ = ∫ x in Set.Ioi (10 : ℝ), f x := by
        refine setIntegral_congr_fun measurableSet_Ioi ?_
        intro x hx
        dsimp [f]
        exact gaussian_even x
  have hneg_le : (∫ x in Set.Iio (-10), f x) ≤ 1 / 6 := by
    rw [hneg_eq]
    exact htail
  -- Integral over the complement is at most one third
  have hcompl_le : (∫ x in sᶜ, f x) ≤ 1 / 3 := by
    rw [hScc_eq]
    have hdisc : Disjoint (Set.Iio (-10 : ℝ)) (Set.Ioi (10 : ℝ)) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      change x < -10 at hx1
      change 10 < x at hx2
      linarith
    have hunion : (∫ x in Set.Iio (-10) ∪ Set.Ioi (10 : ℝ), f x)
        = (∫ x in Set.Iio (-10), f x) + ∫ x in Set.Ioi (10 : ℝ), f x := by
      exact setIntegral_union hdisc measurableSet_Ioi hf_int.integrableOn hf_int.integrableOn
    rw [hunion]
    linarith
  -- Conclusion: `∫_s f = 1 - ∫_{sᶜ} f ≥ 2/3`
  have hmain : (2 : ℝ) / 3 ≤ ∫ x in s, f x := by
    have hval : (∫ x in s, f x) = 1 - ∫ x in sᶜ, f x := by
      have h := MeasureTheory.setIntegral_compl (μ := (volume : Measure ℝ)) hmeas_s hf_int
      rw [htot] at h
      linarith
    rw [hval]
    linarith
  exact hmain

end Commons.Analysis.GaussianMeasure