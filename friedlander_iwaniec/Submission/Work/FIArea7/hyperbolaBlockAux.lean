import Mathlib
import Submission.Work.FIArea7.Classical172Defs
import Submission.Work.FIArea7.exists_separating_function

/-!
# `Work.FIArea7.hyperbolaBlockAux`

Auxiliary lemmas for the hyperbola form of *FI* Proposition 23.1.
-/

set_option autoImplicit false

namespace Work.FIArea7

open Finset MeasureTheory
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

lemma norm_ofReal_complex (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  have hsq : ‖(x : ℂ)‖ ^ 2 = x ^ 2 := by rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
  calc ‖(x : ℂ)‖ = Real.sqrt (‖(x : ℂ)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (x ^ 2) := by rw [hsq]
    _ = |x| := Real.sqrt_sq_eq_abs x

lemma norm_natCast_cpow_I (k : ℕ) (hk : 1 ≤ k) (t : ℝ) :
    ‖(k : ℂ) ^ (t * Complex.I)‖ = 1 := by
  have hkc : ((k : ℂ)) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  rw [Complex.norm_cpow_of_ne_zero hkc]
  have harg : ((k : ℂ)).arg = 0 := by
    rw [show (k : ℂ) = ((k : ℝ) : ℂ) by simp]
    exact Complex.arg_ofReal_of_nonneg (by positivity)
  rw [harg]; simp

lemma continuous_cpowI (k : ℕ) (hk : 1 ≤ k) :
    Continuous (fun t : ℝ => (k : ℂ) ^ (t * Complex.I)) := by
  have hk0 : (k : ℂ) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hfun : (fun t : ℝ => (k : ℂ) ^ (t * Complex.I))
      = fun t : ℝ => Complex.exp (Complex.log (k : ℂ) * ((t : ℂ) * Complex.I)) := by
    funext t; exact Complex.cpow_def_of_ne_zero hk0 _
  rw [hfun]
  exact Complex.continuous_exp.comp (Continuous.mul continuous_const
    (Continuous.mul Complex.continuous_ofReal continuous_const))

lemma integrable_h_mul_cpowI (h : ℝ → ℝ) (hInt : Integrable (fun t : ℝ => (h t : ℂ)))
    (k : ℕ) (hk : 1 ≤ k) :
    Integrable (fun t : ℝ => (h t : ℂ) * (k : ℂ) ^ (t * Complex.I)) := by
  have hAbs : Integrable (fun t : ℝ => |h t|) := by
    have := hInt.norm
    simpa only [norm_ofReal_complex] using this
  refine MeasureTheory.Integrable.mono' hAbs ?_ ?_
  · refine AEStronglyMeasurable.mul hInt.aestronglyMeasurable ?_
    exact (continuous_cpowI k hk).aestronglyMeasurable
  · filter_upwards with t
    rw [norm_mul, norm_ofReal_complex, norm_natCast_cpow_I k hk t, mul_one]

lemma natCast_mul_cpow_I (m n : ℕ) (t : ℝ) :
    ((m * n : ℕ) : ℂ) ^ (t * Complex.I)
      = ((m : ℂ)) ^ (t * Complex.I) * ((n : ℂ)) ^ (t * Complex.I) := by
  have h : ((m * n : ℕ) : ℂ) = ((m : ℝ) : ℂ) * ((n : ℝ) : ℂ) := by push_cast; ring
  rw [h]
  exact Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity) _

/-! ## The dyadic partition of `[1, M]` -/

/-- Partition of `[1, M]` into the dyadic blocks `[2^a, min (2^{a+1}-1) M]`. -/
lemma dyadic_partition (M : ℕ) (g : ℕ → ℂ) :
    (∑ m ∈ Finset.Icc 1 M, g m)
    = ∑ a ∈ Finset.range (Nat.log 2 M + 1),
        ∑ m ∈ Finset.Icc (2 ^ a) (min (2 ^ (a + 1) - 1) M), g m := by
  have hbi : (Finset.range (Nat.log 2 M + 1)).biUnion
      (fun a => Finset.Icc (2 ^ a) (min (2 ^ (a + 1) - 1) M)) = Finset.Icc 1 M := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨a, ha, hx⟩ := hx
      rw [Finset.mem_range] at ha
      rw [Finset.mem_Icc] at hx ⊢
      exact ⟨le_trans Nat.one_le_two_pow hx.1, le_trans hx.2 (min_le_right _ _)⟩
    · intro hx
      rw [Finset.mem_biUnion]
      rw [Finset.mem_Icc] at hx
      refine ⟨Nat.log 2 x, ?_, ?_⟩
      · rw [Finset.mem_range]
        have := Nat.log_mono_right (b := 2) hx.2
        omega
      · rw [Finset.mem_Icc]
        have hx0 : x ≠ 0 := by omega
        refine ⟨Nat.pow_log_le_self 2 hx0, ?_⟩
        have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) x
        omega
  have hdisj : (Finset.range (Nat.log 2 M + 1) : Set ℕ).PairwiseDisjoint
      (fun a => Finset.Icc (2 ^ a) (min (2 ^ (a + 1) - 1) M)) := by
    intro a _ha b _hb _hab
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx hxb
    simp only [Finset.mem_Icc] at hx hxb
    have h1 : 2 ^ b < 2 ^ (a + 1) := by
      calc 2 ^ b ≤ x := hxb.1
        _ ≤ min (2 ^ (a + 1) - 1) M := hx.2
        _ ≤ 2 ^ (a + 1) - 1 := min_le_left _ _
        _ < 2 ^ (a + 1) := Nat.sub_one_lt (by positivity)
    have h2 : 2 ^ a < 2 ^ (b + 1) := by
      calc 2 ^ a ≤ x := hx.1
        _ ≤ min (2 ^ (b + 1) - 1) M := hxb.2
        _ ≤ 2 ^ (b + 1) - 1 := min_le_left _ _
        _ < 2 ^ (b + 1) := Nat.sub_one_lt (by positivity)
    have hba : b ≤ a := by
      have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h1
      omega
    have hab' : a ≤ b := by
      have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2
      omega
    omega
  rw [← hbi, Finset.sum_biUnion hdisj]

/-- Truncating the range of `n` at `min N (u / 2^a)` does not change the sum, because for
`m ≥ 2^a` and `n > u / 2^a` one has `m * n > u`. -/
lemma hyperbolaCutReduce (f : ℕ → ℂ) (m N u a : ℕ) (hm : 2 ^ a ≤ m) :
    (∑ n ∈ Finset.Icc 1 N, (if m * n ≤ u then f n else 0))
      = ∑ n ∈ Finset.Icc 1 (min N (u / 2 ^ a)),
          (if m * n ≤ u then f n else 0) := by
  refine (Finset.sum_subset ?_ ?_).symm
  · intro x hx
    rw [Finset.mem_Icc] at hx ⊢
    exact ⟨hx.1, le_trans hx.2 (min_le_left N (u / 2 ^ a))⟩
  · intro x hx hxs
    rw [Finset.mem_Icc] at hx
    have hxg : u / 2 ^ a < x := by
      by_contra h
      apply hxs
      rw [Finset.mem_Icc]
      exact ⟨hx.1, le_min hx.2 (le_of_not_gt h)⟩
    have hx2 : u / 2 ^ a + 1 ≤ x := by omega
    have hmul : u < m * x := by
      have h1 : 2 ^ a * (u / 2 ^ a + 1) ≤ m * x := Nat.mul_le_mul hm hx2
      have h2 : u < 2 ^ a * (u / 2 ^ a + 1) := by
        have hmod : u % 2 ^ a < 2 ^ a := Nat.mod_lt _ (by positivity)
        have hdiv := Nat.div_add_mod u (2 ^ a)
        nlinarith [hdiv, hmod]
      omega
    rw [if_neg (by omega : ¬ m * x ≤ u)]

/-! ## The per-block estimate -/

/-- **A single dyadic block.**  Given the separating function `h` for the threshold `u`, a uniform
bound `B` on the twisted rectangular bilinear forms, the hyperbola-restricted block sum obeys
`‖Σ‖ ≤ B · ∫|h|`. -/
lemma hyperbola_block_le
    (h : ℝ → ℝ) (u : ℕ) (hu : 1 ≤ u)
    (hint : ∀ k : ℕ, 1 ≤ k →
      (∫ t : ℝ, (h t : ℂ) * (k : ℂ) ^ (t * Complex.I))
        = if (k : ℝ) ≤ (u : ℝ) then 1 else 0)
    (M_a C_a c0 : ℕ) (psi : GaussianInt → ℂ) (α β : ℕ → ℂ) (B : ℝ) (hBnn : 0 ≤ B)
    (hB : ∀ t : ℝ, ‖LBilin M_a C_a c0 psi
        (fun m => α m * (m : ℂ) ^ (t * Complex.I))
        (fun n => β n * (n : ℂ) ^ (t * Complex.I))‖ ≤ B) :
    ‖∑ m ∈ Finset.Icc 1 M_a, ∑ n ∈ Finset.Icc 1 C_a,
        (if m * n ≤ u then α m * β n * quadEigen psi (c0 * m * n) else 0)‖
      ≤ B * ∫ t : ℝ, |h t| := by
  have hInt : Integrable (fun t : ℝ => (h t : ℂ)) := by
    by_contra hc
    have h0 : (∫ t : ℝ, (h t : ℂ)) = 0 := MeasureTheory.integral_undef hc
    have h1 : (∫ t : ℝ, (h t : ℂ)) = 1 := by
      have h1' := hint 1 le_rfl
      rw [if_pos (by exact_mod_cast hu)] at h1'
      simpa using h1'
    exact one_ne_zero (h1.symm.trans h0)
  have hAbs : Integrable (fun t : ℝ => |h t|) := by
    have := hInt.norm
    simpa only [norm_ofReal_complex] using this
  set F : ℝ → ℂ := fun t => LBilin M_a C_a c0 psi
        (fun m => α m * (m : ℂ) ^ (t * Complex.I))
        (fun n => β n * (n : ℂ) ^ (t * Complex.I)) with hFdef
  have hBF : ∀ t : ℝ, ‖F t‖ ≤ B := fun t => by rw [hFdef]; exact hB t
  have key : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      Integrable (fun t : ℝ => (α m * β n * quadEigen psi (c0 * m * n))
        * ((h t : ℂ) * ((m * n : ℕ) : ℂ) ^ (t * Complex.I))) := by
    intro m n hm1 hn1
    have hk : 1 ≤ m * n := by have := Nat.mul_le_mul hm1 hn1; simpa using this
    exact (integrable_h_mul_cpowI h hInt (m * n) hk).const_mul _
  have hmain : (∑ m ∈ Finset.Icc 1 M_a, ∑ n ∈ Finset.Icc 1 C_a,
        (if m * n ≤ u then α m * β n * quadEigen psi (c0 * m * n) else 0))
      = ∫ t, (h t : ℂ) * F t := by
    have hstep1 : ∀ m ∈ Finset.Icc 1 M_a, ∀ n ∈ Finset.Icc 1 C_a,
        (if m * n ≤ u then α m * β n * quadEigen psi (c0 * m * n) else 0)
        = ∫ t, (α m * β n * quadEigen psi (c0 * m * n))
            * ((h t : ℂ) * ((m * n : ℕ) : ℂ) ^ (t * Complex.I)) := by
      intro m hm n hn
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hk : 1 ≤ m * n := by have := Nat.mul_le_mul hm1 hn1; simpa using this
      rw [MeasureTheory.integral_const_mul, hint (m * n) hk]
      by_cases hc : m * n ≤ u
      · rw [if_pos hc, if_pos (by exact_mod_cast hc), mul_one]
      · rw [if_neg hc, if_neg (by exact_mod_cast hc), mul_zero]
    rw [show (∑ m ∈ Finset.Icc 1 M_a, ∑ n ∈ Finset.Icc 1 C_a,
          (if m * n ≤ u then α m * β n * quadEigen psi (c0 * m * n) else 0))
        = (∑ m ∈ Finset.Icc 1 M_a, ∑ n ∈ Finset.Icc 1 C_a,
            ∫ t, (α m * β n * quadEigen psi (c0 * m * n))
              * ((h t : ℂ) * ((m * n : ℕ) : ℂ) ^ (t * Complex.I))) from
        Finset.sum_congr rfl (fun m hm => Finset.sum_congr rfl (fun n hn => hstep1 m hm n hn))]
    rw [Finset.sum_congr rfl (fun m hm => (MeasureTheory.integral_finset_sum _
          (fun n _hn => key m n (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp _hn).1)).symm)]
    rw [(MeasureTheory.integral_finset_sum _
          (fun m hm => MeasureTheory.integrable_finset_sum _
            (fun n hn => key m n (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hn).1))).symm]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [hFdef]
    simp only [LBilin]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro m hm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n hn
    rw [natCast_mul_cpow_I]
    ring
  rw [hmain]
  calc ‖∫ t, (h t : ℂ) * F t‖ ≤ ∫ t, ‖(h t : ℂ) * F t‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ t, |h t| * B := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun t => norm_nonneg _)
        · exact hAbs.mul_const B
        · exact Filter.Eventually.of_forall (fun t => by
            change ‖(h t : ℂ) * F t‖ ≤ |h t| * B
            rw [norm_mul, norm_ofReal_complex]
            exact mul_le_mul_of_nonneg_left (hBF t) (abs_nonneg _))
    _ = B * ∫ t, |h t| := by rw [MeasureTheory.integral_mul_const, mul_comm]

/-! ## Assembly helpers -/

lemma sum_Icc_zero_lt {M : Type*} [AddCommMonoid M] (H : ℕ → M) (a M_a : ℕ)
    (h : ∀ m, m < 2 ^ a → H m = 0) :
    ∑ m ∈ Finset.Icc 1 M_a, H m = ∑ m ∈ Finset.Icc (2 ^ a) M_a, H m := by
  refine (Finset.sum_subset ?_ ?_).symm
  · intro x hx
    rw [Finset.mem_Icc] at hx ⊢
    exact ⟨le_trans Nat.one_le_two_pow hx.1, hx.2⟩
  · intro x hx hxs
    apply h
    rw [Finset.mem_Icc] at hx
    by_contra hcon
    push Not at hcon
    exact hxs (Finset.mem_Icc.mpr ⟨hcon, hx.2⟩)

lemma hyperbola_block_rewrite (a M N u : ℕ) (A B : ℕ → ℂ) (Q : ℕ → ℕ → ℂ) :
    (∑ m ∈ Finset.Icc (2 ^ a) (min (2 ^ (a + 1) - 1) M), ∑ n ∈ Finset.Icc 1 N,
        (if m * n ≤ u then A m * B n * Q m n else 0))
      = ∑ m ∈ Finset.Icc 1 (min (2 ^ (a + 1) - 1) M),
          ∑ n ∈ Finset.Icc 1 (min N (u / 2 ^ a)),
            (if m * n ≤ u then (if 2 ^ a ≤ m then A m else 0) * B n * Q m n else 0) := by
  rw [Finset.sum_congr rfl (fun m hm =>
        hyperbolaCutReduce (fun n => A m * B n * Q m n) m N u a (Finset.mem_Icc.mp hm).1)]
  rw [sum_Icc_zero_lt (fun m => ∑ n ∈ Finset.Icc 1 (min N (u / 2 ^ a)),
        (if m * n ≤ u then (if 2 ^ a ≤ m then A m else 0) * B n * Q m n else 0))
      a (min (2 ^ (a + 1) - 1) M) (fun m hm => by
        apply Finset.sum_eq_zero; intro n hn
        rw [if_neg (by omega : ¬ 2 ^ a ≤ m), zero_mul]
        by_cases hc : m * n ≤ u <;> simp [hc])]
  apply Finset.sum_congr rfl; intro m hm
  apply Finset.sum_congr rfl; intro n hn
  rw [if_pos (Finset.mem_Icc.mp hm).1]

lemma card_dyadic_blocks (M N u : ℕ) :
    ((Finset.range (Nat.log 2 M + 1)).filter (fun a => 1 ≤ min N (u / 2 ^ a))).card
      ≤ Nat.log 2 u + 1 := by
  rw [← Finset.card_range (Nat.log 2 u + 1)]
  apply Finset.card_le_card
  intro a ha
  rw [Finset.mem_filter, Finset.mem_range] at ha
  rw [Finset.mem_range]
  have h2a : 2 ^ a ≤ u := by
    have h1 : (1:ℕ) ≤ u / 2 ^ a := le_trans ha.2 (min_le_right N (u / 2 ^ a))
    have h0 : 0 < u / 2 ^ a := by omega
    exact (Nat.div_pos_iff.mp h0).2
  have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) h2a
  omega

end

end Work.FIArea7
