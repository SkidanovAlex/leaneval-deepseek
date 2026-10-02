import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Submission.Commons.Probability.Chernoff.prod_mgf_finite
import Submission.Commons.Analysis.Real.exp_neg_sub_one_add_le
import Submission.Commons.Analysis.Real.exp_sub_one_sub_le

namespace Commons.Probability.Chernoff

open Finset


/-- Chord bound for the exponential: for `x ∈ [0,1]` and any real `t`,
`exp (t * x) ≤ 1 + x * (exp t - 1)`. -/
theorem exp_mul_le_one_add (t x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (t * x) ≤ 1 + x * (Real.exp t - 1) := by
  have hmem0 : (0 : ℝ) ∈ Set.univ := Set.mem_univ _
  have hmemt : t ∈ Set.univ := Set.mem_univ _
  have h : Real.exp ((1 - x) • (0 : ℝ) + x • t)
      ≤ (1 - x) • Real.exp (0 : ℝ) + x • Real.exp t :=
    convexOn_exp.right hmem0 hmemt (by linarith) hx0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  calc Real.exp (t * x) = Real.exp (x * t) := by rw [mul_comm]
    _ ≤ 1 - x + x * Real.exp t := h
    _ = 1 + x * (Real.exp t - 1) := by ring

/-- The weighted moment generating identity over all `ι → Bool` configurations. -/
theorem sum_weight_exp_eq_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p X : ι → ℝ) (T : ℝ) :
    (∑ s : ι → Bool, (∏ i, (if s i then p i else 1 - p i)) *
        Real.exp (T * ∑ i, (if s i then X i else 0)))
      = ∏ i, ((1 - p i) + p i * Real.exp (T * X i)) := by
  classical
  let g : ι → Bool → ℝ := fun i b =>
    (if b then p i else 1 - p i) * Real.exp (T * (if b then X i else 0))
  have step1 : (∑ s : ι → Bool, (∏ i, (if s i then p i else 1 - p i)) *
        Real.exp (T * ∑ i, (if s i then X i else 0)))
      = ∑ s : ι → Bool, ∏ i, g i (s i) := by
    apply Finset.sum_congr rfl
    intro s _
    have hexp : Real.exp (T * ∑ i, (if s i then X i else 0))
        = ∏ i, Real.exp (T * (if s i then X i else 0)) := by
      rw [Finset.mul_sum, Real.exp_sum]
    rw [hexp, ← Finset.prod_mul_distrib]
  have step2 : (∑ s : ι → Bool, ∏ i, g i (s i))
      = ∏ i, ∑ b : Bool, g i b := by
    have h := Finset.sum_prod_piFinset (s := (Finset.univ : Finset Bool)) (g := g)
    rw [Fintype.piFinset_univ] at h
    simpa using h
  have step3 : ∀ i : ι, (∑ b : Bool, g i b)
      = (1 - p i) + p i * Real.exp (T * X i) := by
    intro i
    have htrue : g i true = p i * Real.exp (T * X i) := by simp [g]
    have hfalse : g i false = 1 - p i := by simp [g]
    rw [Fintype.sum_bool, htrue, hfalse]
    ring
  rw [step1, step2]
  exact Finset.prod_congr rfl (fun i _ => step3 i)

/-- The total weight is one. -/
theorem sum_weight_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) :
    (∑ s : ι → Bool, ∏ i, (if s i then p i else 1 - p i)) = 1 := by
  have h := sum_weight_exp_eq_prod p (fun _ => 0) 0
  simpa using h

/-- Per-coordinate exponential factor bound. -/
theorem per_coord_exp_le (p x T : ℝ) :
    (1 - p) + p * Real.exp (T * x) ≤ Real.exp (p * (Real.exp (T * x) - 1)) := by
  have h : (1 - p) + p * Real.exp (T * x) = 1 + p * (Real.exp (T * x) - 1) := by ring
  rw [h]
  have := Real.add_one_le_exp (p * (Real.exp (T * x) - 1))
  linarith

/-- Scaled chord bound: for `0 ≤ x ≤ C` and `C > 0`, `exp (T * x) - 1 ≤ (x/C)*(exp (T*C) - 1)`. -/
theorem chord_scaled {x C T : ℝ} (hC : 0 < C) (hx0 : 0 ≤ x) (hxC : x ≤ C) :
    Real.exp (T * x) - 1 ≤ (x / C) * (Real.exp (T * C) - 1) := by
  have hxc0 : 0 ≤ x / C := div_nonneg hx0 (le_of_lt hC)
  have hxc1 : x / C ≤ 1 := (div_le_one hC).mpr hxC
  have h := exp_mul_le_one_add (T * C) (x / C) hxc0 hxc1
  have harg : T * C * (x / C) = T * x := by field_simp
  rw [harg] at h
  linarith

/-- Moment-generating bound for the weighted Bernoulli sum. -/
theorem mgf_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {p X : ι → ℝ} {C : ℝ}
    (hC : 0 < C) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hX0 : ∀ i, 0 ≤ X i) (hXC : ∀ i, X i ≤ C) (T : ℝ) :
    (∑ s : ι → Bool, (∏ i, (if s i then p i else 1 - p i)) *
        Real.exp (T * ((∑ i, (if s i then X i else 0)) - ∑ i, p i * X i)))
      ≤ Real.exp (-(T * ∑ i, p i * X i) +
          ((∑ i, p i * X i) / C) * (Real.exp (T * C) - 1)) := by
  classical
  have hchord : ∀ i, Real.exp (T * X i) - 1 ≤ (X i / C) * (Real.exp (T * C) - 1) :=
    fun i => chord_scaled hC (hX0 i) (hXC i)
  have hsplit : ∀ s : ι → Bool,
      Real.exp (T * ((∑ i, (if s i then X i else 0)) - ∑ i, p i * X i))
      = Real.exp (T * ∑ i, (if s i then X i else 0)) * Real.exp (-(T * ∑ i, p i * X i)) := by
    intro s
    rw [← Real.exp_add]; congr 1; ring
  have hnonneg : ∀ i, 0 ≤ (1 - p i) + p i * Real.exp (T * X i) := by
    intro i
    have h1 : 0 ≤ 1 - p i := by linarith [hp1 i]
    have h2 : 0 ≤ p i * Real.exp (T * X i) := mul_nonneg (hp0 i) (Real.exp_nonneg _)
    linarith
  have hS : (∑ i, p i * (Real.exp (T * X i) - 1))
      ≤ ((∑ i, p i * X i) / C) * (Real.exp (T * C) - 1) := by
    have h1 : (∑ i, p i * (Real.exp (T * X i) - 1))
        ≤ ∑ i, p i * ((X i / C) * (Real.exp (T * C) - 1)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hchord i) (hp0 i)
    have h2 : (∑ i, p i * ((X i / C) * (Real.exp (T * C) - 1)))
        = (∑ i, p i * X i / C) * (Real.exp (T * C) - 1) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _; ring
    have h3 : (∑ i, p i * X i / C) = (∑ i, p i * X i) / C := by rw [Finset.sum_div]
    rw [h2, h3] at h1
    exact h1
  calc (∑ s : ι → Bool, (∏ i, (if s i then p i else 1 - p i)) *
        Real.exp (T * ((∑ i, (if s i then X i else 0)) - ∑ i, p i * X i)))
      = (∑ s : ι → Bool, (∏ i, (if s i then p i else 1 - p i)) *
          Real.exp (T * ∑ i, (if s i then X i else 0)))
          * Real.exp (-(T * ∑ i, p i * X i)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro s _
        rw [hsplit s]; ring
    _ = (∏ i, ((1 - p i) + p i * Real.exp (T * X i)))
          * Real.exp (-(T * ∑ i, p i * X i)) := by
        rw [sum_weight_exp_eq_prod]
    _ ≤ (∏ i, Real.exp (p i * (Real.exp (T * X i) - 1)))
          * Real.exp (-(T * ∑ i, p i * X i)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact Finset.prod_le_prod₀ (fun i _ => hnonneg i) (fun i _ => per_coord_exp_le (p i) (X i) T)
    _ = Real.exp (∑ i, p i * (Real.exp (T * X i) - 1))
          * Real.exp (-(T * ∑ i, p i * X i)) := by rw [Real.exp_sum]
    _ = Real.exp ((∑ i, p i * (Real.exp (T * X i) - 1)) + -(T * ∑ i, p i * X i)) := by
        rw [← Real.exp_add]
    _ ≤ Real.exp (((∑ i, p i * X i) / C) * (Real.exp (T * C) - 1) + -(T * ∑ i, p i * X i)) := by
        apply Real.exp_le_exp.mpr
        linarith [hS]
    _ = Real.exp (-(T * ∑ i, p i * X i) + ((∑ i, p i * X i) / C) * (Real.exp (T * C) - 1)) := by
        rw [add_comm]

/-- Indicator inequality for the absolute-value deviation. -/
theorem indicator_le_abs (t z : ℝ) :
    (if t ≤ |z| then (1 : ℝ) else 0)
      ≤ (if t ≤ z then 1 else 0) + (if t ≤ -z then 1 else 0) := by
  by_cases h : t ≤ |z|
  · rw [if_pos h]
    rcases le_abs.mp h with h' | h'
    · have hz : (if t ≤ z then (1 : ℝ) else 0) = 1 := if_pos h'
      rw [hz]
      have h2 : (0 : ℝ) ≤ (if t ≤ -z then 1 else 0) := by split_ifs <;> norm_num
      linarith
    · have hz : (if t ≤ -z then (1 : ℝ) else 0) = 1 := if_pos h'
      rw [hz]
      have h2 : (0 : ℝ) ≤ (if t ≤ z then 1 else 0) := by split_ifs <;> norm_num
      linarith
  · rw [if_neg h]
    have h2 : (0 : ℝ) ≤ (if t ≤ z then 1 else 0) := by split_ifs <;> norm_num
    have h3 : (0 : ℝ) ≤ (if t ≤ -z then 1 else 0) := by split_ifs <;> norm_num
    linarith

/-- Comparison of the two exponential exponents for the lower tail. -/
theorem exponent_neg_le {lam C M : ℝ} (hlam : 0 ≤ lam) (hC : 0 < C) (hM : 0 ≤ M) :
    -(-lam * M) + (M / C) * (Real.exp ((-lam) * C) - 1)
      ≤ -(lam * M) + (M / C) * (Real.exp (lam * C) - 1) := by
  have hg := Commons.Analysis.Real.exp_neg_sub_one_add_le (show (0 : ℝ) ≤ lam * C by positivity)
  rw [← neg_mul] at hg
  have hM0 : 0 ≤ M / C := div_nonneg hM (le_of_lt hC)
  have h1 : (M / C) * (Real.exp ((-lam) * C) - 1 + lam * C)
      ≤ (M / C) * (Real.exp (lam * C) - 1 - lam * C) :=
    mul_le_mul_of_nonneg_left hg hM0
  have hrel : (M / C) * (lam * C) = lam * M := by field_simp
  have h2 : (M / C) * (Real.exp ((-lam) * C) - 1 + lam * C)
      = (M / C) * (Real.exp ((-lam) * C) - 1) + lam * M := by
    calc (M / C) * (Real.exp ((-lam) * C) - 1 + lam * C)
        = (M / C) * (Real.exp ((-lam) * C) - 1) + (M / C) * (lam * C) := by ring
      _ = (M / C) * (Real.exp ((-lam) * C) - 1) + lam * M := by rw [hrel]
  have h3 : (M / C) * (Real.exp (lam * C) - 1 - lam * C)
      = (M / C) * (Real.exp (lam * C) - 1) - lam * M := by
    calc (M / C) * (Real.exp (lam * C) - 1 - lam * C)
        = (M / C) * (Real.exp (lam * C) - 1) - (M / C) * (lam * C) := by ring
      _ = (M / C) * (Real.exp (lam * C) - 1) - lam * M := by rw [hrel]
  rw [h2, h3] at h1
  have h4 : -(-lam * M) = lam * M := by ring
  rw [h4]
  linarith

/-- Upper tail of the weighted Bernoulli sum. -/
theorem upper_tail {ι : Type*} [Fintype ι] [DecidableEq ι] {p X : ι → ℝ} {C : ℝ}
    (hC : 0 < C) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hX0 : ∀ i, 0 ≤ X i) (hXC : ∀ i, X i ≤ C) {lam T : ℝ} (hlam : 0 ≤ lam) :
    (∑ s : ι → Bool, (∏ i, (if s i then p i else 1 - p i)) *
        (if T ≤ (∑ i, (if s i then X i else 0)) - ∑ i, p i * X i then 1 else 0))
      ≤ Real.exp (-(lam * T) - lam * (∑ i, p i * X i)
          + ((∑ i, p i * X i) / C) * (Real.exp (lam * C) - 1)) := by
  classical
  have hw : ∀ s : ι → Bool, 0 ≤ ∏ i, (if s i then p i else 1 - p i) := by
    intro s
    apply Finset.prod_nonneg
    intro i _
    have h1 : 0 ≤ p i := hp0 i
    have h2 : 0 ≤ 1 - p i := by linarith [hp1 i]
    split_ifs <;> linarith
  have hterm : ∀ s : ι → Bool,
      (∏ i, (if s i then p i else 1 - p i)) *
        (if T ≤ (∑ i, (if s i then X i else 0)) - ∑ i, p i * X i then 1 else 0)
      ≤ Real.exp (-(lam * T)) * ((∏ i, (if s i then p i else 1 - p i)) *
          Real.exp (lam * ((∑ i, (if s i then X i else 0)) - ∑ i, p i * X i))) := by
    intro s
    have hind : (if T ≤ (∑ i, (if s i then X i else 0)) - ∑ i, p i * X i then (1 : ℝ) else 0)
        ≤ Real.exp (lam * (((∑ i, (if s i then X i else 0)) - ∑ i, p i * X i) - T)) := by
      by_cases h : T ≤ (∑ i, (if s i then X i else 0)) - ∑ i, p i * X i
      · rw [if_pos h]
        have hpos : 0 ≤ lam * (((∑ i, (if s i then X i else 0)) - ∑ i, p i * X i) - T) :=
          mul_nonneg hlam (by linarith)
        calc (1 : ℝ) = Real.exp 0 := by simp
          _ ≤ Real.exp (lam * (((∑ i, (if s i then X i else 0)) - ∑ i, p i * X i) - T)) :=
              Real.exp_le_exp.mpr hpos
      · rw [if_neg h]
        exact Real.exp_nonneg _
    calc (∏ i, (if s i then p i else 1 - p i)) *
          (if T ≤ (∑ i, (if s i then X i else 0)) - ∑ i, p i * X i then 1 else 0)
        ≤ (∏ i, (if s i then p i else 1 - p i)) *
            Real.exp (lam * (((∑ i, (if s i then X i else 0)) - ∑ i, p i * X i) - T)) :=
          mul_le_mul_of_nonneg_left hind (hw s)
      _ = Real.exp (-(lam * T)) * ((∏ i, (if s i then p i else 1 - p i)) *
            Real.exp (lam * ((∑ i, (if s i then X i else 0)) - ∑ i, p i * X i))) := by
          rw [show Real.exp (lam * (((∑ i, (if s i then X i else 0)) - ∑ i, p i * X i) - T))
              = Real.exp (-(lam * T)) *
                Real.exp (lam * ((∑ i, (if s i then X i else 0)) - ∑ i, p i * X i)) by
            rw [← Real.exp_add]; congr 1; ring]
          ring
  calc (∑ s : ι → Bool, (∏ i, (if s i then p i else 1 - p i)) *
        (if T ≤ (∑ i, (if s i then X i else 0)) - ∑ i, p i * X i then 1 else 0))
      ≤ ∑ s : ι → Bool, Real.exp (-(lam * T)) * ((∏ i, (if s i then p i else 1 - p i)) *
          Real.exp (lam * ((∑ i, (if s i then X i else 0)) - ∑ i, p i * X i))) :=
        Finset.sum_le_sum (fun s _ => hterm s)
    _ = Real.exp (-(lam * T)) * (∑ s : ι → Bool, (∏ i, (if s i then p i else 1 - p i)) *
          Real.exp (lam * ((∑ i, (if s i then X i else 0)) - ∑ i, p i * X i))) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (-(lam * T)) * Real.exp (-(lam * (∑ i, p i * X i))
          + ((∑ i, p i * X i) / C) * (Real.exp (lam * C) - 1)) :=
        mul_le_mul_of_nonneg_left (mgf_bound hC hp0 hp1 hX0 hXC lam) (Real.exp_nonneg _)
    _ = Real.exp (-(lam * T) - lam * (∑ i, p i * X i)
          + ((∑ i, p i * X i) / C) * (Real.exp (lam * C) - 1)) := by
        rw [← Real.exp_add]; congr 1; ring

/-- Lower tail of the weighted Bernoulli sum. -/
theorem lower_tail {ι : Type*} [Fintype ι] [DecidableEq ι] {p X : ι → ℝ} {C : ℝ}
    (hC : 0 < C) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hX0 : ∀ i, 0 ≤ X i) (hXC : ∀ i, X i ≤ C) {lam T : ℝ} (hlam : 0 ≤ lam) :
    (∑ s : ι → Bool, (∏ i, (if s i then p i else 1 - p i)) *
        (if T ≤ (∑ i, p i * X i) - (∑ i, (if s i then X i else 0)) then 1 else 0))
      ≤ Real.exp (-(lam * T) - lam * (∑ i, p i * X i)
          + ((∑ i, p i * X i) / C) * (Real.exp (lam * C) - 1)) := by
  classical
  have hw : ∀ s : ι → Bool, 0 ≤ ∏ i, (if s i then p i else 1 - p i) := by
    intro s
    apply Finset.prod_nonneg
    intro i _
    have h1 : 0 ≤ p i := hp0 i
    have h2 : 0 ≤ 1 - p i := by linarith [hp1 i]
    split_ifs <;> linarith
  have hterm : ∀ s : ι → Bool,
      (∏ i, (if s i then p i else 1 - p i)) *
        (if T ≤ (∑ i, p i * X i) - (∑ i, (if s i then X i else 0)) then 1 else 0)
      ≤ Real.exp (-(lam * T)) * ((∏ i, (if s i then p i else 1 - p i)) *
          Real.exp ((-lam) * ((∑ i, (if s i then X i else 0)) - ∑ i, p i * X i))) := by
    intro s
    have hind : (if T ≤ (∑ i, p i * X i) - (∑ i, (if s i then X i else 0)) then (1 : ℝ) else 0)
        ≤ Real.exp (lam * (((∑ i, p i * X i) - (∑ i, (if s i then X i else 0))) - T)) := by
      by_cases h : T ≤ (∑ i, p i * X i) - (∑ i, (if s i then X i else 0))
      · rw [if_pos h]
        have hpos : 0 ≤ lam * (((∑ i, p i * X i) - (∑ i, (if s i then X i else 0))) - T) :=
          mul_nonneg hlam (by linarith)
        calc (1 : ℝ) = Real.exp 0 := by simp
          _ ≤ Real.exp (lam * (((∑ i, p i * X i) - (∑ i, (if s i then X i else 0))) - T)) :=
              Real.exp_le_exp.mpr hpos
      · rw [if_neg h]
        exact Real.exp_nonneg _
    calc (∏ i, (if s i then p i else 1 - p i)) *
          (if T ≤ (∑ i, p i * X i) - (∑ i, (if s i then X i else 0)) then 1 else 0)
        ≤ (∏ i, (if s i then p i else 1 - p i)) *
            Real.exp (lam * (((∑ i, p i * X i) - (∑ i, (if s i then X i else 0))) - T)) :=
          mul_le_mul_of_nonneg_left hind (hw s)
      _ = Real.exp (-(lam * T)) * ((∏ i, (if s i then p i else 1 - p i)) *
            Real.exp ((-lam) * ((∑ i, (if s i then X i else 0)) - ∑ i, p i * X i))) := by
          rw [show Real.exp (lam * (((∑ i, p i * X i) - (∑ i, (if s i then X i else 0))) - T))
              = Real.exp (-(lam * T)) *
                Real.exp ((-lam) * ((∑ i, (if s i then X i else 0)) - ∑ i, p i * X i)) by
            rw [← Real.exp_add]; congr 1; ring]
          ring
  have hmgf := mgf_bound hC hp0 hp1 hX0 hXC (-lam)
  have hcompare : Real.exp (-(-lam * (∑ i, p i * X i))
        + ((∑ i, p i * X i) / C) * (Real.exp ((-lam) * C) - 1))
      ≤ Real.exp (-(lam * (∑ i, p i * X i))
        + ((∑ i, p i * X i) / C) * (Real.exp (lam * C) - 1)) := by
    apply Real.exp_le_exp.mpr
    exact exponent_neg_le hlam hC
      (Finset.sum_nonneg (fun i _ => mul_nonneg (hp0 i) (hX0 i)))
  calc (∑ s : ι → Bool, (∏ i, (if s i then p i else 1 - p i)) *
        (if T ≤ (∑ i, p i * X i) - (∑ i, (if s i then X i else 0)) then 1 else 0))
      ≤ ∑ s : ι → Bool, Real.exp (-(lam * T)) * ((∏ i, (if s i then p i else 1 - p i)) *
          Real.exp ((-lam) * ((∑ i, (if s i then X i else 0)) - ∑ i, p i * X i))) :=
        Finset.sum_le_sum (fun s _ => hterm s)
    _ = Real.exp (-(lam * T)) * (∑ s : ι → Bool, (∏ i, (if s i then p i else 1 - p i)) *
          Real.exp ((-lam) * ((∑ i, (if s i then X i else 0)) - ∑ i, p i * X i))) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (-(lam * T)) * Real.exp (-(-lam * (∑ i, p i * X i))
          + ((∑ i, p i * X i) / C) * (Real.exp (-lam * C) - 1)) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
    _ ≤ Real.exp (-(lam * T)) * Real.exp (-(lam * (∑ i, p i * X i))
          + ((∑ i, p i * X i) / C) * (Real.exp (lam * C) - 1)) :=
        mul_le_mul_of_nonneg_left hcompare (Real.exp_nonneg _)
    _ = Real.exp (-(lam * T) - lam * (∑ i, p i * X i)
          + ((∑ i, p i * X i) / C) * (Real.exp (lam * C) - 1)) := by
        rw [← Real.exp_add]; congr 1; ring

/-- Arithmetic identity used for the degenerate mean-zero case. -/
theorem sq_div_two_C_third (t C : ℝ) : t ^ 2 / (2 * C * (t / 3)) = 3 * t / (2 * C) := by
  by_cases hC : C = 0
  · simp [hC]
  · by_cases ht : t = 0
    · simp [ht]
    · field_simp
      try ring

/-- The split of the two-sided indicator into the two one-sided indicators. -/
theorem split_indicator_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (p X : ι → ℝ) (t : ℝ)
    (hw : ∀ s : ι → Bool, 0 ≤ ∏ i, (if s i then p i else 1 - p i)) :
    (∑ s : ι → Bool, (∏ i, (if s i then p i else 1 - p i)) *
        (if t ≤ |(∑ i, (if s i then X i else 0)) - (∑ i, p i * X i)| then (1 : ℝ) else 0))
      ≤ (∑ s : ι → Bool, (∏ i, (if s i then p i else 1 - p i)) *
            (if t ≤ (∑ i, (if s i then X i else 0)) - (∑ i, p i * X i) then 1 else 0))
          + (∑ s : ι → Bool, (∏ i, (if s i then p i else 1 - p i)) *
            (if t ≤ (∑ i, p i * X i) - (∑ i, (if s i then X i else 0)) then 1 else 0)) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  have hind := indicator_le_abs t ((∑ i, (if s i then X i else 0)) - (∑ i, p i * X i))
  have hz : (-((∑ i, (if s i then X i else 0)) - (∑ i, p i * X i)))
      = (∑ i, p i * X i) - (∑ i, (if s i then X i else 0)) := by ring
  rw [hz] at hind
  calc (∏ i, (if s i then p i else 1 - p i)) *
        (if t ≤ |(∑ i, (if s i then X i else 0)) - (∑ i, p i * X i)| then (1 : ℝ) else 0)
      ≤ (∏ i, (if s i then p i else 1 - p i)) *
        ((if t ≤ (∑ i, (if s i then X i else 0)) - (∑ i, p i * X i) then 1 else 0)
          + (if t ≤ (∑ i, p i * X i) - (∑ i, (if s i then X i else 0)) then 1 else 0)) :=
        mul_le_mul_of_nonneg_left hind (hw s)
    _ = (∏ i, (if s i then p i else 1 - p i)) *
          (if t ≤ (∑ i, (if s i then X i else 0)) - (∑ i, p i * X i) then 1 else 0)
        + (∏ i, (if s i then p i else 1 - p i)) *
          (if t ≤ (∑ i, p i * X i) - (∑ i, (if s i then X i else 0)) then 1 else 0) := by
        ring

/-- The two-sided weighted Chernoff bound. -/
theorem chernoff_two_sided_finite_weighted {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) {X : ι → ℝ} (hX0 : ∀ i, 0 ≤ X i) {C : ℝ}
    (hC0 : 0 ≤ C) (hXC : ∀ i, X i ≤ C) {t : ℝ} (ht : 0 ≤ t) :
    (Finset.univ.sum fun s : ι → Bool =>
        (Finset.univ.prod fun i => (if s i then p i else 1 - p i)) *
        (if t ≤ |(Finset.univ.sum fun i => if s i then X i else 0) -
            (Finset.univ.sum fun i => p i * X i)| then (1 : ℝ) else 0))
      ≤ 2 * Real.exp (-(t ^ 2) /
          (2 * C * ((Finset.univ.sum fun i => p i * X i) + t / 3))) := by
  classical
  have hw : ∀ s : ι → Bool, 0 ≤ ∏ i, (if s i then p i else 1 - p i) := by
    intro s
    apply Finset.prod_nonneg
    intro i _
    have h1 : 0 ≤ p i := hp0 i
    have h2 : 0 ≤ 1 - p i := by linarith [hp1 i]
    split_ifs <;> linarith
  rcases eq_or_lt_of_le hC0 with hCeq | hCpos
  · -- C = 0
    subst hCeq
    have hle : (∑ s : ι → Bool, (∏ i, (if s i then p i else 1 - p i)) *
        (if t ≤ |(∑ i, (if s i then X i else 0)) - (∑ i, p i * X i)| then (1 : ℝ) else 0))
        ≤ ∑ s : ι → Bool, ∏ i, (if s i then p i else 1 - p i) := by
      apply Finset.sum_le_sum
      intro s _
      have hind : (if t ≤ |(∑ i, (if s i then X i else 0)) - (∑ i, p i * X i)| then (1 : ℝ) else 0)
          ≤ 1 := by split_ifs <;> norm_num
      calc (∏ i, (if s i then p i else 1 - p i)) *
            (if t ≤ |(∑ i, (if s i then X i else 0)) - (∑ i, p i * X i)| then (1 : ℝ) else 0)
          ≤ (∏ i, (if s i then p i else 1 - p i)) * 1 := mul_le_mul_of_nonneg_left hind (hw s)
        _ = ∏ i, (if s i then p i else 1 - p i) := by ring
    rw [sum_weight_eq_one p] at hle
    have hR : 1 ≤ 2 * Real.exp (-(t ^ 2) /
        (2 * (0:ℝ) * ((∑ i, p i * X i) + t / 3))) := by
      have : 2 * Real.exp (-(t ^ 2) / (2 * (0:ℝ) * ((∑ i, p i * X i) + t / 3))) = 2 := by
        simp
      rw [this]; norm_num
    linarith
  · -- C > 0
    by_cases hμ0 : (∑ i, p i * X i) = 0
    · -- mean zero: use lam = 3/(2C)
      set lam : ℝ := 3 / (2 * C) with hlamdef
      have hlam0' : 0 ≤ lam := by rw [hlamdef]; positivity
      have hU := upper_tail hCpos hp0 hp1 hX0 hXC (lam := lam) (T := t) hlam0'
      have hL := lower_tail hCpos hp0 hp1 hX0 hXC (lam := lam) (T := t) hlam0'
      have hexp : -(lam * t) - lam * (∑ i, p i * X i)
            + ((∑ i, p i * X i) / C) * (Real.exp (lam * C) - 1)
          ≤ -(t ^ 2) / (2 * C * ((∑ i, p i * X i) + t / 3)) := by
        rw [hμ0, hlamdef]
        simp only [mul_zero, sub_zero, zero_div, zero_mul, add_zero]
        rw [zero_add, neg_div, sq_div_two_C_third]
        exact le_of_eq (by ring)
      have hsplit := split_indicator_sum p X t hw
      calc (∑ s : ι → Bool, (∏ i, (if s i then p i else 1 - p i)) *
            (if t ≤ |(∑ i, (if s i then X i else 0)) - (∑ i, p i * X i)| then (1 : ℝ) else 0))
          ≤ _ := hsplit
        _ ≤ Real.exp (-(t ^ 2) / (2 * C * ((∑ i, p i * X i) + t / 3)))
              + Real.exp (-(t ^ 2) / (2 * C * ((∑ i, p i * X i) + t / 3))) :=
            add_le_add (le_trans hU (Real.exp_le_exp.mpr hexp))
              (le_trans hL (Real.exp_le_exp.mpr hexp))
        _ = 2 * Real.exp (-(t ^ 2) / (2 * C * ((∑ i, p i * X i) + t / 3))) := by ring
    · -- mean positive
      have hμpos : 0 < ∑ i, p i * X i :=
        lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => mul_nonneg (hp0 i) (hX0 i)))
          (Ne.symm hμ0)
      set B : ℝ := (∑ i, p i * X i) + t / 3 with hBdef
      have hBpos : 0 < B := by rw [hBdef]; linarith
      set u : ℝ := t / B with hudef
      have hu0 : 0 ≤ u := by rw [hudef]; positivity
      have hu3 : u < 3 := by
        rw [hudef, div_lt_iff₀ hBpos, hBdef]; linarith
      have hI := Commons.Analysis.Real.exp_sub_one_sub_le hu0 hu3
      have h1u : 1 - u / 3 = (∑ i, p i * X i) / B := by
        rw [hudef, hBdef]; field_simp; try ring
      have hgoal : (∑ i, p i * X i) * (Real.exp u - 1 - u) - u * t ≤ -(t ^ 2) / (2 * B) := by
        have h1 : (∑ i, p i * X i) * (Real.exp u - 1 - u)
            ≤ (∑ i, p i * X i) * (u ^ 2 / (2 * (1 - u / 3))) :=
          mul_le_mul_of_nonneg_left hI (Finset.sum_nonneg (fun i _ => mul_nonneg (hp0 i) (hX0 i)))
        have h2 : (∑ i, p i * X i) * (u ^ 2 / (2 * (1 - u / 3))) = t ^ 2 / (2 * B) := by
          rw [h1u, hudef]; field_simp; try ring
        have h3 : u * t = 2 * (t ^ 2 / (2 * B)) := by rw [hudef]; field_simp; try ring
        rw [h2] at h1
        rw [h3]
        rw [neg_div]
        linarith
      set lam : ℝ := u / C with hlamdef
      have hlam0 : 0 ≤ lam := by rw [hlamdef]; positivity
      have hlamC : lam * C = u := by rw [hlamdef]; field_simp; try ring
      have hexp : -(lam * t) - lam * (∑ i, p i * X i)
            + ((∑ i, p i * X i) / C) * (Real.exp (lam * C) - 1)
          ≤ -(t ^ 2) / (2 * C * B) := by
        have hA : -(lam * t) - lam * (∑ i, p i * X i)
              + ((∑ i, p i * X i) / C) * (Real.exp (lam * C) - 1)
            = (1 / C) * ((∑ i, p i * X i) * (Real.exp u - 1 - u) - u * t) := by
          rw [hlamC, hlamdef]
          field_simp
          try ring
        have hC' : -(t ^ 2) / (2 * C * B) = (1 / C) * (-(t ^ 2) / (2 * B)) := by
          field_simp; try ring
        rw [hA, hC']
        exact mul_le_mul_of_nonneg_left hgoal (by positivity)
      have hU := upper_tail hCpos hp0 hp1 hX0 hXC (lam := lam) (T := t) hlam0
      have hL := lower_tail hCpos hp0 hp1 hX0 hXC (lam := lam) (T := t) hlam0
      have hsplit := split_indicator_sum p X t hw
      calc (∑ s : ι → Bool, (∏ i, (if s i then p i else 1 - p i)) *
            (if t ≤ |(∑ i, (if s i then X i else 0)) - (∑ i, p i * X i)| then (1 : ℝ) else 0))
          ≤ _ := hsplit
        _ ≤ Real.exp (-(t ^ 2) / (2 * C * B)) + Real.exp (-(t ^ 2) / (2 * C * B)) :=
            add_le_add (le_trans hU (Real.exp_le_exp.mpr hexp))
              (le_trans hL (Real.exp_le_exp.mpr hexp))
        _ = 2 * Real.exp (-(t ^ 2) / (2 * C * B)) := by ring
end Commons.Probability.Chernoff