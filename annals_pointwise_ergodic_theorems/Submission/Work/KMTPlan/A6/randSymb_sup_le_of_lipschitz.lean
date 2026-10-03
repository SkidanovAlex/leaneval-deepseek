import Mathlib
import Submission.Work.KMTAreas.A7.narrow_of_core
import Submission.Work.KMTPlan.A6.lowSmallSet_conv

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6
noncomputable section
open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

/-! ## The bump `φ_N` in scaled form -/

/-- `φ_N(x) = η(2^{Log N} x)` at `k = 0` and `η(2^{Log N - k}x) - η(2·2^{Log N-k}x)` otherwise. -/
theorem varphiN_apply_form (N k : ℕ) (x : ℝ) :
    Work.KMTAreas.A7.varphiN N k x =
      (if k = 0 then Work.KMTContract.kmtEta ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ)) * x)
       else Work.KMTContract.kmtEta ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * x)
        - Work.KMTContract.kmtEta (2 * ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * x))) := by
  rw [Work.KMTAreas.A7.varphiN]
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, if_false]
    have harg : (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1) * x
        = 2 * ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * x) := by
      rw [show ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)
          = ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) + 1 by ring]
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      ring
    rw [harg]

/-- `φ_N` is even in the frequency variable. -/
theorem varphiN_even (N k : ℕ) (x : ℝ) :
    Work.KMTAreas.A7.varphiN N k (-x) = Work.KMTAreas.A7.varphiN N k x := by
  rw [varphiN_apply_form N k (-x), varphiN_apply_form N k x]
  by_cases hk : k = 0
  · subst hk
    simp only [if_true, Nat.cast_zero, sub_zero]
    rw [show (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ)) * (-x)
        = -((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ)) * x) by ring,
      Work.KMTContract.kmtEta_neg]
  · simp only [hk, if_false]
    rw [show (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * (-x)
        = -((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * x) by ring]
    rw [show 2 * (-((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * x))
        = -(2 * ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * x)) by ring,
      Work.KMTContract.kmtEta_neg, Work.KMTContract.kmtEta_neg]

/-- `φ_N(x) = φ_N(|x|)`. -/
theorem varphiN_even_abs (N k : ℕ) (x : ℝ) :
    Work.KMTAreas.A7.varphiN N k x = Work.KMTAreas.A7.varphiN N k |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, varphiN_even N k x]

/-- The cutoff `η` takes values in `[0,1]` (real), so the difference of two of its values has
modulus at most one. -/
theorem kmtEta_sub_norm_le_one (u v : ℝ) :
    ‖Work.KMTContract.kmtEta u - Work.KMTContract.kmtEta v‖ ≤ 1 := by
  simp only [Work.KMTContract.kmtEta, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_le]
  constructor
  · have h1 := Work.KMTContract.kmtEta_nonneg u
    have h2 := Work.KMTContract.kmtEta_le_one v
    linarith
  · have h1 := Work.KMTContract.kmtEta_le_one u
    have h2 := Work.KMTContract.kmtEta_nonneg v
    linarith

/-- `‖φ_N(x)‖ ≤ 1`. -/
theorem varphiN_norm_le_one (N k : ℕ) (x : ℝ) :
    ‖Work.KMTAreas.A7.varphiN N k x‖ ≤ 1 := by
  rw [Work.KMTAreas.A7.varphiN]
  split
  · exact Work.KMTContract.norm_kmtEta_le _
  · exact kmtEta_sub_norm_le_one _ _

/-- `‖φ_{N,t}(x)‖ ≤ 1`. -/
theorem varphiNt_norm_le_one (N k : ℕ) (t x : ℝ) :
    ‖Work.KMTAreas.A7.varphiNt N k t x‖ ≤ 1 := by
  rw [Work.KMTAreas.A7.varphiNt, norm_mul]
  rw [norm_ee_eq_one, mul_one]
  exact varphiN_norm_le_one N k x

/-- The bump vanishes where the scaled frequency variable exceeds one in modulus. -/
theorem varphiN_eq_zero_of_one_lt (N k : ℕ) (x : ℝ)
    (h : 1 < |(2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * x|) :
    Work.KMTAreas.A7.varphiN N k x = 0 := by
  rw [varphiN_apply_form N k x]
  by_cases hk : k = 0
  · subst hk
    simp only [if_true, Nat.cast_zero, sub_zero] at h ⊢
    exact Work.KMTContract.kmtEta_zero (le_of_lt h)
  · simp only [hk, if_false]
    have h2 : 1 < |2 * ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * x)| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    rw [Work.KMTContract.kmtEta_zero (le_of_lt h), Work.KMTContract.kmtEta_zero (le_of_lt h2),
      sub_zero]

/-- The bump vanishes where the scaled frequency variable exceeds one in modulus. -/
theorem varphiN_ne_zero_le (N k : ℕ) (x : ℝ) (h : Work.KMTAreas.A7.varphiN N k x ≠ 0) :
    |(2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * x| ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  exact h (varphiN_eq_zero_of_one_lt N k x hcon)

/-- For `k ≥ 1` the bump vanishes where the scaled variable is at most `1/4`. -/
theorem varphiN_eq_zero_of_small (N k : ℕ) (hk : 1 ≤ k) (x : ℝ)
    (h : |(2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * x| ≤ 1 / 4) :
    Work.KMTAreas.A7.varphiN N k x = 0 := by
  have hk0 : k ≠ 0 := by omega
  rw [varphiN_apply_form N k x, if_neg hk0]
  have h2 : |2 * ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * x)| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  rw [Work.KMTContract.kmtEta_one (by linarith), Work.KMTContract.kmtEta_one h2, sub_self]

/-- For `k ≥ 1`, `φ_N(x) ≠ 0` forces the scaled variable to exceed `1/4`. -/
theorem one_four_lt_of_varphiN_ne_zero (N k : ℕ) (hk : 1 ≤ k) (x : ℝ)
    (h : Work.KMTAreas.A7.varphiN N k x ≠ 0) :
    1 / 4 < |(2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * x| := by
  by_contra hcon
  push_neg at hcon
  exact h (varphiN_eq_zero_of_small N k hk x hcon)

/-- The Lipschitz bound for the bump in the scaled variable `w = 2^{Log · - k}x`. -/
theorem varphiN_diff_le_main (Lη : ℝ)
    (hη : ∀ x y : ℝ, ‖Work.KMTContract.kmtEta x - Work.KMTContract.kmtEta y‖ ≤ Lη * |x - y|)
    (N M k : ℕ) (x : ℝ) :
    ‖Work.KMTAreas.A7.varphiN N k x - Work.KMTAreas.A7.varphiN M k x‖ ≤ 3 * Lη *
      |(2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * x
        - (2 : ℝ) ^ ((Work.Analysis.EndVar.logN M : ℝ) - (k : ℝ)) * x| := by
  have hLη0 : 0 ≤ Lη := by
    have h := hη 0 1
    have h0 : Work.KMTContract.kmtEta (0 : ℝ) = 1 := Work.KMTContract.kmtEta_one (by norm_num)
    have h1 : Work.KMTContract.kmtEta (1 : ℝ) = 0 := Work.KMTContract.kmtEta_zero (by norm_num)
    rw [h0, h1, sub_zero, norm_one] at h
    have h2 : |((0 : ℝ) - 1)| = 1 := by norm_num
    rw [h2, mul_one] at h
    linarith
  rw [varphiN_apply_form N k x, varphiN_apply_form M k x]
  by_cases hk : k = 0
  · subst hk
    simp only [if_true, Nat.cast_zero, sub_zero]
    calc ‖Work.KMTContract.kmtEta ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ)) * x)
          - Work.KMTContract.kmtEta ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN M : ℝ)) * x)‖
        ≤ Lη * |(2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ)) * x
            - (2 : ℝ) ^ ((Work.Analysis.EndVar.logN M : ℝ)) * x| := hη _ _
      _ ≤ 3 * Lη * |(2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ)) * x
            - (2 : ℝ) ^ ((Work.Analysis.EndVar.logN M : ℝ)) * x| := by
          nlinarith [abs_nonneg ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ)) * x
            - (2 : ℝ) ^ ((Work.Analysis.EndVar.logN M : ℝ)) * x)]
  · simp only [hk, if_false]
    set wN := (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * x with hwN
    set wM := (2 : ℝ) ^ ((Work.Analysis.EndVar.logN M : ℝ) - (k : ℝ)) * x with hwM
    have h1 := hη wN wM
    have h2 := hη (2 * wN) (2 * wM)
    have h3 : |2 * wN - 2 * wM| = 2 * |wN - wM| := by
      rw [show 2 * wN - 2 * wM = 2 * (wN - wM) by ring, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [h3] at h2
    rw [show Work.KMTContract.kmtEta ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN M : ℝ) - (k : ℝ)) * x)
        = Work.KMTContract.kmtEta wM from by rw [hwM],
      show Work.KMTContract.kmtEta ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * x)
        = Work.KMTContract.kmtEta wN from by rw [hwN]]
    rw [show 2 * ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN M : ℝ) - (k : ℝ)) * x) = 2 * wM from by rw [hwM],
      show 2 * ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * x) = 2 * wN from by rw [hwN]]
    calc ‖(Work.KMTContract.kmtEta wN - Work.KMTContract.kmtEta (2 * wN))
          - (Work.KMTContract.kmtEta wM - Work.KMTContract.kmtEta (2 * wM))‖
        = ‖(Work.KMTContract.kmtEta wN - Work.KMTContract.kmtEta wM)
            - (Work.KMTContract.kmtEta (2 * wN) - Work.KMTContract.kmtEta (2 * wM))‖ := by
          rw [show (Work.KMTContract.kmtEta wN - Work.KMTContract.kmtEta (2 * wN))
              - (Work.KMTContract.kmtEta wM - Work.KMTContract.kmtEta (2 * wM))
              = (Work.KMTContract.kmtEta wN - Work.KMTContract.kmtEta wM)
              - (Work.KMTContract.kmtEta (2 * wN) - Work.KMTContract.kmtEta (2 * wM)) by ring]
      _ ≤ ‖Work.KMTContract.kmtEta wN - Work.KMTContract.kmtEta wM‖
            + ‖Work.KMTContract.kmtEta (2 * wN) - Work.KMTContract.kmtEta (2 * wM)‖ :=
          norm_sub_le _ _
      _ ≤ 3 * Lη * |wN - wM| := by linarith

/-! ## Two abstract summation lemmas for monotone walks -/

/-- For a nondecreasing `W` with `W 0 ≥ 0` the increments of `W` over the indices where
`W (n+1) ≤ c` sum to at most `c`. -/
theorem sum_diff_filter_le {W : ℕ → ℝ} (hmono : Monotone W) (hW0 : 0 ≤ W 0) (K : ℕ)
    {c : ℝ} (hc : 0 ≤ c) :
    ∑ n ∈ (Finset.range K).filter (fun n => W (n + 1) ≤ c), (W (n + 1) - W n) ≤ c := by
  classical
  by_cases hne : ((Finset.range K).filter (fun n => W (n + 1) ≤ c)).Nonempty
  · set m := ((Finset.range K).filter (fun n => W (n + 1) ≤ c)).max' hne with hm
    have hmem : m ∈ (Finset.range K).filter (fun n => W (n + 1) ≤ c) := Finset.max'_mem _ hne
    have hmc : W (m + 1) ≤ c := (Finset.mem_filter.mp hmem).2
    have hsub : (Finset.range K).filter (fun n => W (n + 1) ≤ c) ⊆ Finset.range (m + 1) := by
      intro n hn
      simp only [Finset.mem_range]
      have := Finset.le_max' _ n hn
      omega
    calc ∑ n ∈ (Finset.range K).filter (fun n => W (n + 1) ≤ c), (W (n + 1) - W n)
        ≤ ∑ n ∈ Finset.range (m + 1), (W (n + 1) - W n) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun n _ _ => sub_nonneg.mpr (hmono (by omega)))
      _ = W (m + 1) - W 0 := Finset.sum_range_sub W (m + 1)
      _ ≤ c := by linarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.sum_empty]
    exact hc

/-- At most one index `n` where a nondecreasing walk crosses the level `c` upwards. -/
theorem card_crossing_le_one {W : ℕ → ℝ} (hmono : Monotone W) (K : ℕ) {c : ℝ} :
    ((Finset.range K).filter (fun n => W n ≤ c ∧ c < W (n + 1))).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro p hp q hq
  by_contra hpq
  rw [Finset.mem_filter] at hp hq
  rcases lt_or_gt_of_ne hpq with h | h
  · have hpq' : p + 1 ≤ q := by omega
    have h1 : W (p + 1) ≤ W q := hmono hpq'
    linarith [hp.2.2, hq.2.1, h1]
  · have hqp' : q + 1 ≤ p := by omega
    have h1 : W (q + 1) ≤ W p := hmono hqp'
    linarith [hq.2.2, hp.2.1, h1]

/-- `∑ n ∈ s, (if p n then 1 else 0) = #{n ∈ s : p n}` for real-valued sums. -/
theorem sum_ite_one_zero {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    ∑ x ∈ s, (if p x then (1 : ℝ) else 0) = ((s.filter p).card : ℝ) := by
  classical
  have h1 : ∀ x, (if p x then (1 : ℝ) else 0) = ((if p x then (1 : ℕ) else 0 : ℕ) : ℝ) := by
    intro x
    by_cases h : p x <;> simp [h]
  rw [Finset.sum_congr rfl (fun x _ => h1 x), ← Nat.cast_sum, Finset.sum_boole]
  simp

/-! ## The difference sum of the bumps (`k` arbitrary) -/

/-- `∑_{n<K} ‖φ_{⌊a(n+1)⌋}(x) - φ_{⌊a n⌋}(x)‖ ≤ 3 Lη + 2` along a lacunary sequence. -/
theorem varphiN_diff_sum_bound_main (Lη : ℝ) (hLη : 0 < Lη)
    (hη : ∀ x y : ℝ, ‖Work.KMTContract.kmtEta x - Work.KMTContract.kmtEta y‖ ≤ Lη * |x - y|)
    (Λ : NNReal) (hΛ : 1 < Λ) {a : ℕ → NNReal} (ha : PointwiseErgodicTheorems.Lacunary Λ a)
    (ha1 : ∀ n, 1 ≤ a n) (k : ℕ) (x : ℝ) (K : ℕ) :
    ∑ n ∈ Finset.range K, ‖Work.KMTAreas.A7.varphiN (Nat.floor (a (n+1))) k x
        - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x‖ ≤ 3 * Lη + 2 := by
  classical
  have hLη0 : 0 ≤ Lη := le_of_lt hLη
  set W : ℕ → ℝ := fun n =>
    (2 : ℝ) ^ ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ) - (k : ℝ)) * |x| with hW
  have hWval : ∀ m : ℕ, W m
      = (2 : ℝ) ^ ((Work.Analysis.EndVar.logN (Nat.floor (a m)) : ℝ) - (k : ℝ)) * |x| :=
    fun m => rfl
  have hWmono : Monotone W := by
    intro p q hpq
    have h1 : Nat.floor (a p) ≤ Nat.floor (a q) := lacunary_floor_mono Λ hΛ ha hpq
    have h2 : Work.Analysis.EndVar.logN (Nat.floor (a p)) ≤ Work.Analysis.EndVar.logN (Nat.floor (a q)) :=
      logN_mono h1
    have h3 : ((Work.Analysis.EndVar.logN (Nat.floor (a p)) : ℝ) - (k : ℝ))
        ≤ ((Work.Analysis.EndVar.logN (Nat.floor (a q)) : ℝ) - (k : ℝ)) := by
      have h4 : ((Work.Analysis.EndVar.logN (Nat.floor (a p)) : ℝ))
          ≤ ((Work.Analysis.EndVar.logN (Nat.floor (a q)) : ℝ)) := by exact_mod_cast h2
      linarith
    have h5 : (2 : ℝ) ^ ((Work.Analysis.EndVar.logN (Nat.floor (a p)) : ℝ) - (k : ℝ))
        ≤ (2 : ℝ) ^ ((Work.Analysis.EndVar.logN (Nat.floor (a q)) : ℝ) - (k : ℝ)) :=
      (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr h3
    have := mul_le_mul_of_nonneg_right h5 (abs_nonneg x)
    simpa only [hW] using this
  have hW0 : 0 ≤ W 0 := by
    rw [hW]
    positivity
  have hterm : ∀ n : ℕ, ‖Work.KMTAreas.A7.varphiN (Nat.floor (a (n+1))) k x
        - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x‖
      ≤ 3 * Lη * (if W (n + 1) ≤ 1 then W (n + 1) - W n else 0)
        + 2 * (if W n ≤ 1 ∧ 1 < W (n + 1) then (1:ℝ) else 0) := by
    intro n
    have hmono' : W n ≤ W (n + 1) := hWmono (Nat.le_succ n)
    have hval : ∀ m : ℕ,
        |(2 : ℝ) ^ ((Work.Analysis.EndVar.logN (Nat.floor (a m)) : ℝ) - (k : ℝ)) * x| = W m := by
      intro m
      rw [hWval m, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _)]
    by_cases hA : 1 < W n
    · have hz1 : Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x = 0 := by
        apply varphiN_eq_zero_of_one_lt
        rw [hval n]
        exact hA
      have hz2 : Work.KMTAreas.A7.varphiN (Nat.floor (a (n+1))) k x = 0 := by
        apply varphiN_eq_zero_of_one_lt
        rw [hval (n+1)]
        linarith
      have hif1 : (if W (n + 1) ≤ 1 then W (n + 1) - W n else 0) = 0 := by
        rw [if_neg]
        intro h
        linarith
      have hif2 : 2 * (if W n ≤ 1 ∧ 1 < W (n + 1) then (1:ℝ) else 0) = 0 := by
        rw [if_neg]
        · ring
        · rintro ⟨h1, -⟩
          linarith
      rw [hz1, hz2, sub_zero, norm_zero, hif1, hif2, mul_zero, add_zero]
    · push_neg at hA
      by_cases hB : W (n + 1) ≤ 1
      · have hif1 : (if W (n + 1) ≤ 1 then W (n + 1) - W n else 0) = W (n + 1) - W n :=
          if_pos hB
        have hif2 : 2 * (if W n ≤ 1 ∧ 1 < W (n + 1) then (1:ℝ) else 0) = 0 := by
          rw [if_neg]
          · ring
          · rintro ⟨-, h⟩
            linarith
        rw [hif1, hif2, add_zero]
        have hdiff := varphiN_diff_le_main Lη hη (Nat.floor (a (n+1))) (Nat.floor (a n)) k |x|
        rw [varphiN_even_abs (Nat.floor (a (n+1))) k x,
          varphiN_even_abs (Nat.floor (a n)) k x]
        refine le_trans hdiff ?_
        rw [← hWval (n+1), ← hWval n, abs_of_nonneg (sub_nonneg.mpr hmono')]
      · push_neg at hB
        have hif1 : (if W (n + 1) ≤ 1 then W (n + 1) - W n else 0) = 0 := by
          rw [if_neg]
          linarith
        have hif2 : 2 * (if W n ≤ 1 ∧ 1 < W (n + 1) then (1:ℝ) else 0) = 2 := by
          rw [if_pos ⟨hA, hB⟩]
          ring
        rw [hif1, hif2, mul_zero, zero_add]
        calc ‖Work.KMTAreas.A7.varphiN (Nat.floor (a (n+1))) k x
              - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x‖
            ≤ ‖Work.KMTAreas.A7.varphiN (Nat.floor (a (n+1))) k x‖
              + ‖Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := add_le_add (varphiN_norm_le_one _ _ _) (varphiN_norm_le_one _ _ _)
          _ = 2 := by norm_num
  have hsum1 : ∑ n ∈ Finset.range K, ‖Work.KMTAreas.A7.varphiN (Nat.floor (a (n+1))) k x
        - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x‖
      ≤ 3 * Lη * (∑ n ∈ (Finset.range K).filter (fun n => W (n + 1) ≤ 1), (W (n + 1) - W n))
        + 2 * (((Finset.range K).filter (fun n => W n ≤ 1 ∧ 1 < W (n + 1))).card : ℝ) := by
    calc ∑ n ∈ Finset.range K, ‖Work.KMTAreas.A7.varphiN (Nat.floor (a (n+1))) k x
          - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x‖
        ≤ ∑ n ∈ Finset.range K, (3 * Lη * (if W (n + 1) ≤ 1 then W (n + 1) - W n else 0)
            + 2 * (if W n ≤ 1 ∧ 1 < W (n + 1) then (1:ℝ) else 0)) :=
          Finset.sum_le_sum (fun n _ => hterm n)
      _ = 3 * Lη * (∑ n ∈ Finset.range K, (if W (n + 1) ≤ 1 then W (n + 1) - W n else 0))
            + 2 * (∑ n ∈ Finset.range K, (if W n ≤ 1 ∧ 1 < W (n + 1) then (1:ℝ) else 0)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = 3 * Lη * (∑ n ∈ (Finset.range K).filter (fun n => W (n + 1) ≤ 1), (W (n + 1) - W n))
            + 2 * (((Finset.range K).filter (fun n => W n ≤ 1 ∧ 1 < W (n + 1))).card : ℝ) := by
          have h1 : (∑ n ∈ Finset.range K, (if W (n + 1) ≤ 1 then W (n + 1) - W n else 0))
              = ∑ n ∈ (Finset.range K).filter (fun n => W (n + 1) ≤ 1), (W (n + 1) - W n) := by
            rw [← Finset.sum_filter]
          have h2 : (∑ n ∈ Finset.range K,
                (if W n ≤ 1 ∧ 1 < W (n + 1) then (1:ℝ) else 0))
              = (((Finset.range K).filter (fun n => W n ≤ 1 ∧ 1 < W (n + 1))).card : ℝ) :=
            sum_ite_one_zero _ _
          rw [h1, h2]
  have hb1 : ∑ n ∈ (Finset.range K).filter (fun n => W (n + 1) ≤ 1), (W (n + 1) - W n) ≤ 1 :=
    sum_diff_filter_le hWmono hW0 K (c := 1) (by norm_num)
  have hb2 : (((Finset.range K).filter (fun n => W n ≤ 1 ∧ 1 < W (n + 1))).card : ℝ) ≤ 1 := by
    have := card_crossing_le_one hWmono K (c := 1)
    exact_mod_cast this
  calc ∑ n ∈ Finset.range K, ‖Work.KMTAreas.A7.varphiN (Nat.floor (a (n+1))) k x
        - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x‖
      ≤ 3 * Lη * (∑ n ∈ (Finset.range K).filter (fun n => W (n + 1) ≤ 1), (W (n + 1) - W n))
        + 2 * (((Finset.range K).filter (fun n => W n ≤ 1 ∧ 1 < W (n + 1))).card : ℝ) := hsum1
    _ ≤ 3 * Lη * 1 + 2 * 1 := by
        have hnn : 0 ≤ ∑ n ∈ (Finset.range K).filter (fun n => W (n + 1) ≤ 1), (W (n + 1) - W n) :=
          Finset.sum_nonneg (fun n hn => sub_nonneg.mpr (hWmono (by omega)))
        nlinarith
    _ = 3 * Lη + 2 := by ring

/-! ## The counting lemma for lacunary windows -/

/-- A lacunary set of scales inside a multiplicative window has at most
`log (B/A)/log Λ + 1` elements. -/
theorem lacunary_window_card_main (Λ : NNReal) (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (s : Finset ℕ) {A B : ℝ} (hA : 0 < A)
    (hAB : A ≤ B) (hs : ∀ n ∈ s, A < (a n : ℝ) ∧ (a n : ℝ) ≤ B) :
    (s.card : ℝ) ≤ Real.log (B / A) / Real.log ((Λ : ℝ)) + 1 := by
  classical
  have hΛ1 : (1 : ℝ) < ((Λ : ℝ)) := by exact_mod_cast hΛ
  have hlogΛ : 0 < Real.log ((Λ : ℝ)) := Real.log_pos hΛ1
  have hBA : 1 ≤ B / A := (one_le_div hA).mpr hAB
  have hlogBA : 0 ≤ Real.log (B / A) := Real.log_nonneg hBA
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, Nat.cast_zero]
    have h0 : 0 ≤ Real.log (B / A) / Real.log ((Λ : ℝ)) := div_nonneg hlogBA hlogΛ.le
    linarith
  · set m := s.min' hne with hm
    have hmin : m ∈ s := Finset.min'_mem s hne
    have hle : ∀ n ∈ s, m ≤ n := fun n hn => Finset.min'_le s n hn
    have hstep : ∀ j : ℕ, ((Λ : ℝ)) * (a j : ℝ) ≤ (a (j + 1) : ℝ) := by
      intro j
      have hpos : (0 : ℝ≥0) < a j := by
        by_contra h
        rw [not_lt, le_zero_iff] at h
        have h0 := ha j
        rw [h, div_zero] at h0
        exact absurd h0 (not_lt.mpr zero_le)
      have h3 : ((Λ : ℝ≥0)) * a j < a (j + 1) := by
        have h4 := mul_lt_mul_of_pos_right (ha j) hpos
        rwa [div_mul_cancel₀ _ (ne_of_gt hpos)] at h4
      exact_mod_cast h3.le
    have hpow : ∀ t : ℕ, ((Λ : ℝ)) ^ t * (a m : ℝ) ≤ (a (m + t) : ℝ) := by
      intro t
      induction t with
      | zero => simp
      | succ j ih =>
        have h5 : ((Λ : ℝ)) ^ (j + 1) * (a m : ℝ)
            = ((Λ : ℝ)) * (((Λ : ℝ)) ^ j * (a m : ℝ)) := by ring
        rw [h5]
        calc ((Λ : ℝ)) * (((Λ : ℝ)) ^ j * (a m : ℝ))
            ≤ ((Λ : ℝ)) * (a (m + j) : ℝ) := mul_le_mul_of_nonneg_left ih (by positivity)
          _ ≤ (a (m + j + 1) : ℝ) := hstep (m + j)
          _ = (a (m + (j + 1)) : ℝ) := by ring_nf
    have hkey : ∀ n ∈ s, (n - m) ≤ Nat.floor (Real.log (B / A) / Real.log ((Λ : ℝ))) := by
      intro n hn
      have hmn : m ≤ n := hle n hn
      have hpn := hpow (n - m)
      have hmn' : m + (n - m) = n := Nat.add_sub_cancel' hmn
      rw [hmn'] at hpn
      have han : (a n : ℝ) ≤ B := (hs n hn).2
      have ham : A < (a m : ℝ) := (hs m hmin).1
      have hpowpos : (0 : ℝ) < ((Λ : ℝ)) ^ (n - m) := by positivity
      have hlt : ((Λ : ℝ)) ^ (n - m) * A < B := by
        calc ((Λ : ℝ)) ^ (n - m) * A < ((Λ : ℝ)) ^ (n - m) * (a m : ℝ) := by nlinarith
          _ ≤ (a n : ℝ) := hpn
          _ ≤ B := han
      have hdivlt : ((Λ : ℝ)) ^ (n - m) < B / A := by
        rw [lt_div_iff₀ hA]
        exact hlt
      have hlog : Real.log (((Λ : ℝ)) ^ (n - m)) < Real.log (B / A) :=
        Real.log_lt_log hpowpos hdivlt
      rw [Real.log_pow] at hlog
      have hcast : ((n - m : ℕ) : ℝ) < Real.log (B / A) / Real.log ((Λ : ℝ)) :=
        (lt_div_iff₀ hlogΛ).mpr hlog
      exact Nat.le_floor (le_of_lt hcast)
    have hsub : s ⊆ (Finset.range (Nat.floor (Real.log (B / A) / Real.log ((Λ : ℝ))) + 1)).image
        (fun t => m + t) := by
      intro n hn
      rw [Finset.mem_image]
      refine ⟨n - m, ?_, ?_⟩
      · rw [Finset.mem_range]
        have hk := hkey n hn
        omega
      · have hmn := hle n hn
        omega
    have hcard : s.card ≤ Nat.floor (Real.log (B / A) / Real.log ((Λ : ℝ))) + 1 := by
      calc s.card ≤ ((Finset.range (Nat.floor (Real.log (B / A) / Real.log ((Λ : ℝ))) + 1)).image
            (fun t => m + t)).card := Finset.card_le_card hsub
        _ ≤ (Finset.range (Nat.floor (Real.log (B / A) / Real.log ((Λ : ℝ))) + 1)).card :=
            Finset.card_image_le
        _ = Nat.floor (Real.log (B / A) / Real.log ((Λ : ℝ))) + 1 := Finset.card_range _
    have hfloor : ((Nat.floor (Real.log (B / A) / Real.log ((Λ : ℝ))) : ℕ) : ℝ)
        ≤ Real.log (B / A) / Real.log ((Λ : ℝ)) :=
      Nat.floor_le (div_nonneg hlogBA hlogΛ.le)
    calc (s.card : ℝ) ≤ ((Nat.floor (Real.log (B / A) / Real.log ((Λ : ℝ))) + 1 : ℕ) : ℝ) := by
          exact_mod_cast hcard
      _ ≤ Real.log (B / A) / Real.log ((Λ : ℝ)) + 1 := by
          push_cast
          linarith


/-! ## The modulation sum for `k ≥ 1` -/

/-- The modulation sum for `k ≥ 1`: the number of scales whose bump is active is bounded by the
lacunary window count. -/
theorem varphiN_modul_sum_kpos_main (Λ : NNReal) (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (k : ℕ) (hk : 1 ≤ k)
    {x : ℝ} (hx : x ≠ 0) (t : ℝ) (K : ℕ) :
    ∑ n ∈ Finset.range K, ‖Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
        - Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x)‖
        * ‖Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x‖
      ≤ 2 * (Real.log 40 / Real.log ((Λ : ℝ)) + 1) := by
  classical
  have hxabs : 0 < |x| := abs_pos.mpr hx
  have h2kpos : ∀ j : ℕ, (0:ℝ) < (2:ℝ)^(j:ℝ) := fun j =>
    Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _
  have hterm : ∀ n : ℕ,
      ‖Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
          - Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x)‖
        * ‖Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x‖
      ≤ 2 * (if Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x ≠ 0 then (1:ℝ) else 0) := by
    intro n
    by_cases h : Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x = 0
    · rw [h, norm_zero, mul_zero, if_neg (by simp [h])]
      norm_num
    · rw [if_pos h]
      have h1 : ‖Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
          - Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x)‖ ≤ 2 := by
        calc ‖Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
              - Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x)‖
            ≤ ‖Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)‖
              + ‖Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x)‖ := norm_sub_le _ _
          _ = 2 := by rw [norm_ee_eq_one, norm_ee_eq_one]; norm_num
      calc ‖Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
            - Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x)‖
          * ‖Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x‖
          ≤ 2 * 1 := mul_le_mul h1 (varphiN_norm_le_one _ _ _) (norm_nonneg _) (by norm_num)
        _ = 2 * (1:ℝ) := by norm_num
  -- lower bound for the active scales
  have hlow : ∀ n : ℕ, Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x ≠ 0 →
      (2:ℝ)^(k:ℝ) / 8 / |x| < (a n : ℝ) := by
    intro n hne
    have hN1 : 1 ≤ Nat.floor (a n) := Nat.le_floor (by exact_mod_cast ha1 n)
    have hlog := one_four_lt_of_varphiN_ne_zero (Nat.floor (a n)) k hk x hne
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _)] at hlog
    rw [Real.rpow_sub (by norm_num : (0:ℝ) < 2)] at hlog
    set L : ℝ := ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ) with hL
    set K2 : ℝ := (2:ℝ)^(k:ℝ) with hK2
    have hLpos : (0:ℝ) < (2:ℝ)^L := Real.rpow_pos_of_pos (by norm_num) _
    have hK2pos : (0:ℝ) < K2 := by rw [hK2]; exact h2kpos k
    -- multiply by 2^k
    have hmul : K2 * ((2:ℝ)^L / K2 * |x|) = (2:ℝ)^L * |x| := by
      rw [show K2 * ((2:ℝ)^L / K2 * |x|) = (K2 * ((2:ℝ)^L / K2)) * |x| by ring]
      rw [div_eq_mul_inv, mul_comm ((2:ℝ)^L) (K2⁻¹), ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hK2pos),
        one_mul]
    have h1 : K2 / 4 < (2:ℝ)^L * |x| := by
      have := mul_lt_mul_of_pos_left hlog hK2pos
      rw [hmul] at this
      linarith
    have h2 : (2:ℝ)^L / 2 ≤ (Nat.floor (a n) : ℝ) := by
      have := two_pow_logN_le_two_mul_N hN1
      rw [hL]
      linarith
    have h3 : K2 / 8 < (Nat.floor (a n) : ℝ) * |x| := by
      have h4 : (2:ℝ)^L * |x| / 2 ≤ (Nat.floor (a n) : ℝ) * |x| := by
        rw [show (2:ℝ)^L * |x| / 2 = ((2:ℝ)^L / 2) * |x| by ring]
        exact mul_le_mul_of_nonneg_right h2 (abs_nonneg x)
      linarith
    have h4 : (Nat.floor (a n) : ℝ) ≤ (a n : ℝ) := by
      have := Nat.floor_le (a := a n) zero_le
      exact_mod_cast this
    have h5 : K2 / 8 / |x| < (a n : ℝ) := by
      rw [div_lt_iff₀ hxabs]
      nlinarith [h3, h4, hxabs]
    rw [hK2] at h5
    exact h5
  -- upper bound for the active scales
  have hup : ∀ n : ℕ, Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x ≠ 0 →
      (a n : ℝ) ≤ (2:ℝ)^(k:ℝ) * 2 / |x| + 2 := by
    intro n hne
    have hN1 : 1 ≤ Nat.floor (a n) := Nat.le_floor (by exact_mod_cast ha1 n)
    have hle := varphiN_ne_zero_le (Nat.floor (a n)) k x hne
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _)] at hle
    rw [Real.rpow_sub (by norm_num : (0:ℝ) < 2)] at hle
    set L : ℝ := ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ) with hL
    set K2 : ℝ := (2:ℝ)^(k:ℝ) with hK2
    have hLpos : (0:ℝ) < (2:ℝ)^L := Real.rpow_pos_of_pos (by norm_num) _
    have hK2pos : (0:ℝ) < K2 := by rw [hK2]; exact h2kpos k
    have hle' : (2:ℝ)^L * |x| ≤ K2 := by
      have h1 : (2:ℝ)^L / K2 * |x| = (2:ℝ)^L * |x| / K2 := by
        rw [div_mul_eq_mul_div]
      rw [h1] at hle
      rwa [div_le_one hK2pos] at hle
    have h2 : (Nat.floor (a n) : ℝ) < 2 * (2:ℝ)^L := by
      have := lt_two_mul_pow_logN (Nat.floor (a n))
      rw [hL]
      exact this
    have h3 : (Nat.floor (a n) : ℝ) * |x| < K2 * 2 := by
      have := mul_lt_mul_of_pos_right h2 hxabs
      nlinarith [hle', hxabs]
    have h4 : (a n : ℝ) < (Nat.floor (a n) : ℝ) + 1 := by
      have := Nat.lt_floor_add_one (a n)
      exact_mod_cast this
    rw [hK2] at h3
    have h5 : (a n : ℝ) * |x| < (2:ℝ)^(k:ℝ) * 2 + 2 * |x| := by
      have h5a : (a n : ℝ) * |x| < ((Nat.floor (a n) : ℝ) + 1) * |x| :=
        mul_lt_mul_of_pos_right h4 hxabs
      have h5b : ((Nat.floor (a n) : ℝ) + 1) * |x| = (Nat.floor (a n) : ℝ) * |x| + |x| := by
        ring
      rw [h5b] at h5a
      linarith [h3]
    have hsplit : (2:ℝ)^(k:ℝ) * 2 / |x| + 2 = ((2:ℝ)^(k:ℝ) * 2 + 2 * |x|) / |x| := by
      rw [add_div, mul_div_cancel_right₀ _ (ne_of_gt hxabs)]
    rw [hsplit]
    apply le_of_lt
    rw [lt_div_iff₀ hxabs]
    exact h5
  have hcount : (((Finset.range K).filter
      (fun n => Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x ≠ 0)).card : ℝ)
      ≤ Real.log 40 / Real.log ((Λ : ℝ)) + 1 := by
    set sf := (Finset.range K).filter
      (fun n => Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x ≠ 0) with hsf
    have hmem : ∀ n ∈ sf, Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x ≠ 0 :=
      fun n hn => (Finset.mem_filter.mp hn).2
    have hlogΛ : 0 < Real.log ((Λ : ℝ)) := Real.log_pos (by exact_mod_cast hΛ)
    by_cases hcase : 1 ≤ (2:ℝ)^(k:ℝ) / 8 / |x|
    · have h8 : 8 * |x| ≤ (2:ℝ)^(k:ℝ) := by
        have h := hcase
        rw [div_div] at h
        rw [le_div_iff₀ (by positivity : (0:ℝ) < 8 * |x|)] at h
        linarith
      have hAB : (2:ℝ)^(k:ℝ) / 8 / |x| ≤ (2:ℝ)^(k:ℝ) * 2 / |x| + 2 := by
        rw [div_le_iff₀ hxabs]
        have h1 : ((2:ℝ)^(k:ℝ) * 2 / |x| + 2) * |x|
            = (2:ℝ)^(k:ℝ) * 2 + 2 * |x| := by
          rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hxabs)]
        rw [h1]
        nlinarith [h2kpos k, hxabs]
      have hwin := lacunary_window_card_main Λ hΛ ha sf
        (A := (2:ℝ)^(k:ℝ) / 8 / |x|) (B := (2:ℝ)^(k:ℝ) * 2 / |x| + 2)
        (by positivity) hAB (fun n hn => ⟨hlow n (hmem n hn), hup n (hmem n hn)⟩)
      refine le_trans hwin ?_
      have hratio : ((2:ℝ)^(k:ℝ) * 2 / |x| + 2) / ((2:ℝ)^(k:ℝ) / 8 / |x|) ≤ 40 := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^(k:ℝ) / 8 / |x|)]
        have hL : (2:ℝ)^(k:ℝ) * 2 / |x| + 2
            = ((2:ℝ)^(k:ℝ) * 2 + 2 * |x|) / |x| := by
          rw [add_div, mul_div_cancel_right₀ _ (ne_of_gt hxabs)]
        have hR : (40:ℝ) * ((2:ℝ)^(k:ℝ) / 8 / |x|)
            = (40 * ((2:ℝ)^(k:ℝ) / 8)) / |x| := by
          rw [mul_div_assoc']
        rw [hL, hR, div_le_div_iff_of_pos_right hxabs]
        nlinarith [h8, h2kpos k, hxabs]
      have hlog : Real.log (((2:ℝ)^(k:ℝ) * 2 / |x| + 2) / ((2:ℝ)^(k:ℝ) / 8 / |x|)) ≤
          Real.log 40 := Real.log_le_log (by positivity) hratio
      have := div_le_div_of_nonneg_right hlog hlogΛ.le
      linarith
    · push_neg at hcase
      have h2k : (2:ℝ)^(k:ℝ) < 8 * |x| := by
        rw [div_div] at hcase
        rw [div_lt_one (by positivity : (0:ℝ) < 8 * |x|)] at hcase
        linarith
      have hwin := lacunary_window_card_main Λ hΛ ha sf
        (A := (1:ℝ)/2) (B := 18) (by norm_num) (by norm_num)
        (fun n hn => ⟨by
          have h1 : (1:ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha1 n
          linarith,
          by
          have hb := hup n (hmem n hn)
          have h3 : (2:ℝ)^(k:ℝ) * 2 / |x| < 16 := by
            rw [div_lt_iff₀ hxabs]
            nlinarith [h2k]
          linarith⟩)
      refine le_trans hwin ?_
      have hlog : Real.log (18 / ((1:ℝ)/2)) ≤ Real.log 40 :=
        Real.log_le_log (by norm_num) (by norm_num)
      have := div_le_div_of_nonneg_right hlog hlogΛ.le
      linarith
  calc ∑ n ∈ Finset.range K, ‖Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
          - Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x)‖
        * ‖Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x‖
      ≤ ∑ n ∈ Finset.range K, 2 *
          (if Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x ≠ 0 then (1:ℝ) else 0) :=
        Finset.sum_le_sum (fun n _ => hterm n)
    _ = 2 * (((Finset.range K).filter
          (fun n => Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x ≠ 0)).card : ℝ) := by
        rw [← Finset.mul_sum]
        congr 1
        exact sum_ite_one_zero _ _
    _ ≤ 2 * (Real.log 40 / Real.log ((Λ : ℝ)) + 1) := by linarith [hcount]

/-! ## The modulation sum for `k = 0` -/

/-- The modulation sum for `k = 0`: the vanishing of `η` keeps the phases bounded, so the
increments of the phases telescope. -/
theorem varphiN_modul_sum_k0_main (Λ : NNReal) (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (t : ℝ)
    (ht : t ∈ Set.Icc (1/2 : ℝ) 1) (x : ℝ) (K : ℕ) :
    ∑ n ∈ Finset.range K, ‖Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
        - Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x)‖
        * ‖Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 x‖ ≤ 4 * Real.pi + 2 := by
  classical
  set W : ℕ → ℝ := fun n => (Nat.floor (a n) : ℝ) * |x| with hW
  have hWval : ∀ m : ℕ, W m = (Nat.floor (a m) : ℝ) * |x| := fun m => rfl
  have hWmono : Monotone W := by
    intro p q hpq
    have h1 : Nat.floor (a p) ≤ Nat.floor (a q) := lacunary_floor_mono Λ hΛ ha hpq
    have h2 : ((Nat.floor (a p) : ℕ) : ℝ) ≤ ((Nat.floor (a q) : ℕ) : ℝ) := by exact_mod_cast h1
    rw [hWval p, hWval q]
    exact mul_le_mul_of_nonneg_right h2 (abs_nonneg x)
  have hW0 : 0 ≤ W 0 := by rw [hWval]; positivity
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
  have hterm : ∀ n : ℕ,
      ‖Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
          - Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x)‖
        * ‖Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 x‖
      ≤ 2 * Real.pi * (if W (n+1) ≤ 2 then W (n+1) - W n else 0)
        + 2 * (if W n ≤ 2 ∧ 2 < W (n+1) then (1:ℝ) else 0) := by
    intro n
    have hmono' : W n ≤ W (n+1) := hWmono (Nat.le_succ n)
    have hNdiff : (Nat.floor (a n) : ℝ) ≤ (Nat.floor (a (n+1)) : ℝ) := by
      have := lacunary_floor_mono Λ hΛ ha (Nat.le_succ n)
      exact_mod_cast this
    by_cases hA : 2 < W n
    · have hval : W n < 2 * |(2:ℝ)^(((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)) * x| := by
        rw [hWval n, abs_mul,
          abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _)]
        have h2 := lt_two_mul_pow_logN (Nat.floor (a n))
        nlinarith [abs_nonneg x]
      have hz : Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 x = 0 := by
        apply varphiN_eq_zero_of_one_lt
        simp only [Nat.cast_zero, sub_zero]
        linarith
      rw [hz, norm_zero, mul_zero]
      have hif1 : (if W (n + 1) ≤ 2 then W (n + 1) - W n else 0) = 0 := by
        rw [if_neg]
        intro h
        linarith
      have hif2 : 2 * (if W n ≤ 2 ∧ 2 < W (n + 1) then (1:ℝ) else 0) = 0 := by
        rw [if_neg]
        · ring
        · rintro ⟨h, -⟩
          linarith
      rw [hif1, hif2]
      simp
    · push_neg at hA
      by_cases hB : W (n+1) ≤ 2
      · have hif1 : (if W (n + 1) ≤ 2 then W (n + 1) - W n else 0) = W (n + 1) - W n :=
          if_pos hB
        have hif2 : 2 * (if W n ≤ 2 ∧ 2 < W (n + 1) then (1:ℝ) else 0) = 0 := by
          rw [if_neg]
          · ring
          · rintro ⟨-, h⟩
            linarith
        rw [hif1, hif2, add_zero]
        have h1 := norm_ee_sub_le ((Nat.floor (a (n+1)) : ℝ) * t * x)
          ((Nat.floor (a n) : ℝ) * t * x)
        have h2 : |(Nat.floor (a (n+1)) : ℝ) * t * x - (Nat.floor (a n) : ℝ) * t * x|
            = t * (W (n+1) - W n) := by
          have hreq : (Nat.floor (a (n+1)) : ℝ) * t * x - (Nat.floor (a n) : ℝ) * t * x
              = t * ((Nat.floor (a (n+1)) : ℝ) - (Nat.floor (a n) : ℝ)) * x := by ring
          rw [hreq, hWval (n+1), hWval n]
          calc |t * ((Nat.floor (a (n+1)) : ℝ) - (Nat.floor (a n) : ℝ)) * x|
              = |t * ((Nat.floor (a (n+1)) : ℝ) - (Nat.floor (a n) : ℝ))| * |x| := abs_mul _ _
            _ = |t| * |(Nat.floor (a (n+1)) : ℝ) - (Nat.floor (a n) : ℝ)| * |x| := by rw [abs_mul]
            _ = t * ((Nat.floor (a (n+1)) : ℝ) - (Nat.floor (a n) : ℝ)) * |x| := by
                rw [abs_of_pos ht0, abs_of_nonneg (by linarith)]
            _ = t * ((Nat.floor (a (n+1)) : ℝ) * |x| - (Nat.floor (a n) : ℝ) * |x|) := by ring
        rw [h2] at h1
        calc ‖Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
              - Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x)‖
            * ‖Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 x‖
            ≤ (2 * Real.pi * (t * (W (n+1) - W n))) * 1 :=
              mul_le_mul h1 (varphiN_norm_le_one _ _ _) (norm_nonneg _) (by positivity)
          _ ≤ 2 * Real.pi * (W (n + 1) - W n) := by
              have hX : 0 ≤ W (n + 1) - W n := sub_nonneg.mpr hmono'
              have htX : t * (W (n+1) - W n) ≤ W (n+1) - W n := mul_le_of_le_one_left hX ht.2
              nlinarith [Real.pi_pos]
      · push_neg at hB
        have hif1 : (if W (n + 1) ≤ 2 then W (n + 1) - W n else 0) = 0 := by
          rw [if_neg]
          linarith
        have hif2 : 2 * (if W n ≤ 2 ∧ 2 < W (n + 1) then (1:ℝ) else 0) = 2 := by
          rw [if_pos ⟨hA, hB⟩]
          ring
        rw [hif1, hif2, mul_zero, zero_add]
        have h1 : ‖Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
            - Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x)‖ ≤ 2 := by
          calc _ ≤ ‖Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)‖
                + ‖Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x)‖ := norm_sub_le _ _
            _ = 2 := by rw [norm_ee_eq_one, norm_ee_eq_one]; norm_num
        calc ‖Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
              - Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x)‖
            * ‖Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 x‖
            ≤ 2 * 1 := mul_le_mul h1 (varphiN_norm_le_one _ _ _) (norm_nonneg _) (by norm_num)
          _ = 2 := by norm_num
  have hsum : ∑ n ∈ Finset.range K, ‖Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
        - Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x)‖
        * ‖Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 x‖
      ≤ 2 * Real.pi * (∑ n ∈ (Finset.range K).filter (fun n => W (n + 1) ≤ 2),
          (W (n + 1) - W n))
        + 2 * (((Finset.range K).filter (fun n => W n ≤ 2 ∧ 2 < W (n + 1))).card : ℝ) := by
    calc ∑ n ∈ Finset.range K, ‖Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
          - Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x)‖
          * ‖Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 x‖
        ≤ ∑ n ∈ Finset.range K, (2 * Real.pi * (if W (n+1) ≤ 2 then W (n+1) - W n else 0)
            + 2 * (if W n ≤ 2 ∧ 2 < W (n+1) then (1:ℝ) else 0)) :=
          Finset.sum_le_sum (fun n _ => hterm n)
      _ = 2 * Real.pi * (∑ n ∈ Finset.range K, (if W (n+1) ≤ 2 then W (n+1) - W n else 0))
            + 2 * (∑ n ∈ Finset.range K, (if W n ≤ 2 ∧ 2 < W (n+1) then (1:ℝ) else 0)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 2 * Real.pi * (∑ n ∈ (Finset.range K).filter (fun n => W (n + 1) ≤ 2),
            (W (n + 1) - W n))
            + 2 * (((Finset.range K).filter (fun n => W n ≤ 2 ∧ 2 < W (n + 1))).card : ℝ) := by
          have h1 : (∑ n ∈ Finset.range K, (if W (n + 1) ≤ 2 then W (n + 1) - W n else 0))
              = ∑ n ∈ (Finset.range K).filter (fun n => W (n + 1) ≤ 2), (W (n + 1) - W n) := by
            rw [← Finset.sum_filter]
          have h2 : (∑ n ∈ Finset.range K, (if W n ≤ 2 ∧ 2 < W (n + 1) then (1:ℝ) else 0))
              = (((Finset.range K).filter (fun n => W n ≤ 2 ∧ 2 < W (n + 1))).card : ℝ) :=
            sum_ite_one_zero _ _
          rw [h1, h2]
  have hb1 : ∑ n ∈ (Finset.range K).filter (fun n => W (n + 1) ≤ 2), (W (n + 1) - W n) ≤ 2 :=
    sum_diff_filter_le hWmono hW0 K (c := 2) (by norm_num)
  have hb2 : (((Finset.range K).filter (fun n => W n ≤ 2 ∧ 2 < W (n + 1))).card : ℝ) ≤ 1 := by
    have := card_crossing_le_one hWmono K (c := 2)
    exact_mod_cast this
  calc ∑ n ∈ Finset.range K, ‖Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
        - Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x)‖
        * ‖Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 x‖
      ≤ 2 * Real.pi * (∑ n ∈ (Finset.range K).filter (fun n => W (n + 1) ≤ 2),
          (W (n + 1) - W n))
        + 2 * (((Finset.range K).filter (fun n => W n ≤ 2 ∧ 2 < W (n + 1))).card : ℝ) := hsum
    _ ≤ 2 * Real.pi * 2 + 2 * 1 := by
        have hnn : 0 ≤ ∑ n ∈ (Finset.range K).filter (fun n => W (n + 1) ≤ 2),
            (W (n + 1) - W n) :=
          Finset.sum_nonneg (fun n hn => sub_nonneg.mpr (hWmono (by omega)))
        nlinarith [Real.pi_pos, hb1, hb2]
    _ ≤ 4 * Real.pi + 2 := by nlinarith [Real.pi_pos]

/-! ## The total variation of the modulated bump -/

/-- The uniform total variation bound for the modulated bump along a lacunary sequence. -/
theorem varBound (Lη : ℝ) (hLη : 0 < Lη)
    (hη : ∀ x y : ℝ, ‖Work.KMTContract.kmtEta x - Work.KMTContract.kmtEta y‖ ≤ Lη * |x - y|)
    (Λ : NNReal) (hΛ : 1 < Λ) (a : ℕ → NNReal) (k : ℕ) (t x : ℝ) (K : ℕ)
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
    (ht : t ∈ Set.Icc (1/2 : ℝ) 1) :
    ∑ n ∈ Finset.range K, ‖Work.KMTAreas.A7.varphiNt (Nat.floor (a (n+1))) k t x
        - Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k t x‖
      ≤ 3 * Lη + 2 + max (2 * (Real.log 40 / Real.log ((Λ : ℝ)) + 1)) (4 * Real.pi + 2) := by
  classical
  have hsplit : ∀ n : ℕ, ‖Work.KMTAreas.A7.varphiNt (Nat.floor (a (n+1))) k t x
        - Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k t x‖
      ≤ ‖Work.KMTAreas.A7.varphiN (Nat.floor (a (n+1))) k x
          - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x‖
        + ‖Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
            - Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x)‖
          * ‖Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x‖ := by
    intro n
    rw [Work.KMTAreas.A7.varphiNt, Work.KMTAreas.A7.varphiNt]
    have h1 : ‖Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)‖ = 1 :=
      norm_ee_eq_one _
    calc ‖Work.KMTAreas.A7.varphiN (Nat.floor (a (n+1))) k x
          * Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
          - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x
            * Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x)‖
        = ‖(Work.KMTAreas.A7.varphiN (Nat.floor (a (n+1))) k x
              - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x)
            * Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
            + Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x
              * (Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
                - Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x))‖ := by
          rw [show Work.KMTAreas.A7.varphiN (Nat.floor (a (n+1))) k x
                * Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
                - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x
                  * Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x)
              = (Work.KMTAreas.A7.varphiN (Nat.floor (a (n+1))) k x
                  - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x)
                * Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
                + Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x
                  * (Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
                    - Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x)) by ring]
      _ ≤ ‖(Work.KMTAreas.A7.varphiN (Nat.floor (a (n+1))) k x
              - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x)
            * Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)‖
          + ‖Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x
              * (Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
                - Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x))‖ := norm_add_le _ _
      _ = ‖Work.KMTAreas.A7.varphiN (Nat.floor (a (n+1))) k x
              - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x‖
            + ‖Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x‖
              * ‖Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
                - Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x)‖ := by
          rw [norm_mul, norm_mul, h1, mul_one]
      _ = ‖Work.KMTAreas.A7.varphiN (Nat.floor (a (n+1))) k x
              - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x‖
            + ‖Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
                - Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x)‖
              * ‖Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x‖ := by ring
  calc ∑ n ∈ Finset.range K, ‖Work.KMTAreas.A7.varphiNt (Nat.floor (a (n+1))) k t x
        - Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k t x‖
      ≤ ∑ n ∈ Finset.range K, (‖Work.KMTAreas.A7.varphiN (Nat.floor (a (n+1))) k x
            - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x‖
          + ‖Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
              - Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x)‖
            * ‖Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x‖) :=
        Finset.sum_le_sum (fun n _ => hsplit n)
    _ = (∑ n ∈ Finset.range K, ‖Work.KMTAreas.A7.varphiN (Nat.floor (a (n+1))) k x
            - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x‖)
          + ∑ n ∈ Finset.range K, ‖Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * x)
              - Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * x)‖
            * ‖Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k x‖ := Finset.sum_add_distrib
    _ ≤ (3 * Lη + 2) + max (2 * (Real.log 40 / Real.log ((Λ : ℝ)) + 1)) (4 * Real.pi + 2) := by
        apply add_le_add
        · exact varphiN_diff_sum_bound_main Lη hLη hη Λ hΛ ha ha1 k x K
        · rcases eq_or_ne k 0 with hk | hk
          · subst hk
            exact le_trans (varphiN_modul_sum_k0_main Λ hΛ ha ha1 t ht x K) (le_max_right _ _)
          · have hk1 : 1 ≤ k := by omega
            by_cases hx : x = 0
            · subst hx
              have hzero : ∑ n ∈ Finset.range K,
                  ‖Work.KMTAreas.A7.ee ((Nat.floor (a (n+1)) : ℝ) * t * 0)
                    - Work.KMTAreas.A7.ee ((Nat.floor (a n) : ℝ) * t * 0)‖
                  * ‖Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k 0‖ = 0 := by
                apply Finset.sum_eq_zero
                intro n _
                simp
              rw [hzero]
              have hmax : 0 ≤ max (2 * (Real.log 40 / Real.log ((Λ : ℝ)) + 1)) (4 * Real.pi + 2) :=
                le_max_of_le_right (by positivity)
              linarith
            · exact le_trans (varphiN_modul_sum_kpos_main Λ hΛ ha ha1 k hk1 hx t K) (le_max_left _ _)
    _ = 3 * Lη + 2 + max (2 * (Real.log 40 / Real.log ((Λ : ℝ)) + 1)) (4 * Real.pi + 2) := rfl

/-! ## The randomised symbol of the clamped bump family -/

/-- The randomised symbol of the clamped lacunary bump family is bounded by the total variation
bound of the bump family plus the two jumps of the order-convex index set `lowSmallSet`. -/
theorem randSymb_bounded_of_varBound (Λ : NNReal) (hΛ : 1 < Λ) (C₀ : ℕ) (Cv : ℝ)
    (hvar : ∀ (a : ℕ → NNReal) (k : ℕ) (t x : ℝ) (K : ℕ),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      t ∈ Set.Icc (1/2 : ℝ) 1 →
      ∑ n ∈ Finset.range K, ‖Work.KMTAreas.A7.varphiNt (Nat.floor (a (n+1))) k t x
        - Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k t x‖ ≤ Cv)
    (ρ : ℝ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε : ℕ → ℂ)
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
    (hε : ∀ n, ‖ε n‖ ≤ 1) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) (x : ℝ) :
    ‖Work.KMTAreas.A7.randSymb
      (fun n ξ => if n = 0 then 0
        else if Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
          then Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t ξ else 0) ε K x‖
      ≤ Cv + 2 := by
  classical
  have hφ : ∀ n : ℕ, ‖Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t x‖ ≤ 1 :=
    fun n => varphiNt_norm_le_one (Nat.floor (a n)) k₁ t x
  set T : Set ℕ := {n : ℕ | n ≠ 0 ∧ Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n}
    with hT
  set d : ℕ → ℂ := fun n => Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t x with hd
  set c : ℕ → ℂ := fun n => if n ∈ T then d n else 0 with hc
  have hsym : (Work.KMTAreas.A7.randSymb
      (fun n ξ => if n = 0 then 0
        else if Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
          then Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t ξ else 0) ε K) x
      = ∑ n ∈ Finset.range K, ε n * (c (n + 1) - c n) := by
    simp only [Work.KMTAreas.A7.randSymb]
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    simp only [hc, hd, hT, Set.mem_setOf_eq]
    by_cases h : n = 0 <;> simp [h]
  have hconv : ∀ {n j m : ℕ}, n ≤ j → j ≤ m → n ∈ T → m ∈ T → j ∈ T := by
    intro n j m hnj hjm hn hm
    simp only [hT, Set.mem_setOf_eq] at hn hm ⊢
    exact ⟨by omega, lowSmallSet_conv Λ hΛ ha hnj hjm hn.2 hm.2⟩
  have hterm : ∀ n : ℕ,
      ‖c (n + 1) - c n‖ ≤ ‖d (n + 1) - d n‖ +
        (if (n ∈ T ↔ n + 1 ∈ T) then 0 else 1 : ℝ) := by
    intro n
    have hdn : ‖d n‖ ≤ 1 := hφ n
    have hdn1 : ‖d (n + 1)‖ ≤ 1 := hφ (n + 1)
    by_cases h1 : n ∈ T
    · by_cases h2 : n + 1 ∈ T
      · have hc1 : c n = d n := by simp [hc, h1]
        have hc2 : c (n + 1) = d (n + 1) := by simp [hc, h2]
        have hij : (n ∈ T ↔ n + 1 ∈ T) := ⟨fun _ => h2, fun _ => h1⟩
        rw [hc1, hc2, if_pos hij]
        simp
      · have hc1 : c n = d n := by simp [hc, h1]
        have hc2 : c (n + 1) = 0 := by simp [hc, h2]
        have hij : ¬ (n ∈ T ↔ n + 1 ∈ T) := fun hh => h2 (hh.mp h1)
        rw [hc1, hc2, if_neg hij]
        simp only [zero_sub, norm_neg]
        linarith [norm_nonneg (d (n + 1) - d n)]
    · by_cases h2 : n + 1 ∈ T
      · have hc1 : c n = 0 := by simp [hc, h1]
        have hc2 : c (n + 1) = d (n + 1) := by simp [hc, h2]
        have hij : ¬ (n ∈ T ↔ n + 1 ∈ T) := fun hh => h1 (hh.mpr h2)
        rw [hc1, hc2, if_neg hij]
        simp only [sub_zero]
        linarith [norm_nonneg (d (n + 1) - d n)]
      · have hc1 : c n = 0 := by simp [hc, h1]
        have hc2 : c (n + 1) = 0 := by simp [hc, h2]
        have hij : (n ∈ T ↔ n + 1 ∈ T) := ⟨fun hh => absurd hh h1, fun hh => absurd hh h2⟩
        rw [hc1, hc2, if_pos hij]
        simp
  have hjump : ∑ n ∈ Finset.range K, (if (n ∈ T ↔ n + 1 ∈ T) then (0:ℝ) else 1)
      = (((Finset.range K).filter (fun n => ¬ (n ∈ T ↔ n + 1 ∈ T))).card : ℝ) := by
    have h1 : ∀ n : ℕ, (if (n ∈ T ↔ n + 1 ∈ T) then (0:ℝ) else 1)
        = ((if ¬ (n ∈ T ↔ n + 1 ∈ T) then (1:ℕ) else 0 : ℕ) : ℝ) := by
      intro n
      by_cases h : (n ∈ T ↔ n + 1 ∈ T) <;> simp [h]
    rw [Finset.sum_congr rfl (fun n _ => h1 n), ← Nat.cast_sum, Finset.sum_boole]
    simp
  have hcard : (((Finset.range K).filter (fun n => ¬ (n ∈ T ↔ n + 1 ∈ T))).card : ℝ) ≤ 2 := by
    have := card_jump_le_two hconv K
    exact_mod_cast this
  have hvarK := hvar a k₁ t x K ha ha1 ht
  have hsum : ∑ n ∈ Finset.range K, ‖c (n + 1) - c n‖ ≤ Cv + 2 := by
    have h1 : ∑ n ∈ Finset.range K, ‖c (n + 1) - c n‖
        ≤ ∑ n ∈ Finset.range K, (‖d (n + 1) - d n‖
            + (if (n ∈ T ↔ n + 1 ∈ T) then 0 else 1 : ℝ)) :=
      Finset.sum_le_sum fun n _ => hterm n
    have h2 : ∑ n ∈ Finset.range K, (‖d (n + 1) - d n‖
            + (if (n ∈ T ↔ n + 1 ∈ T) then 0 else 1 : ℝ))
        = (∑ n ∈ Finset.range K, ‖d (n + 1) - d n‖)
          + ∑ n ∈ Finset.range K, (if (n ∈ T ↔ n + 1 ∈ T) then 0 else 1 : ℝ) :=
      Finset.sum_add_distrib
    rw [h2, hjump] at h1
    linarith
  calc ‖(Work.KMTAreas.A7.randSymb
      (fun n ξ => if n = 0 then 0
        else if Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
          then Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t ξ else 0) ε K) x‖
      = ‖∑ n ∈ Finset.range K, ε n * (c (n + 1) - c n)‖ := by rw [hsym]
    _ ≤ ∑ n ∈ Finset.range K, ‖ε n * (c (n + 1) - c n)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range K, ‖c (n + 1) - c n‖ := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hε n)
    _ ≤ Cv + 2 := hsum

theorem randSymb_sup_le_of_lipschitz (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (Λ : NNReal) (hΛ : 1 < Λ)
    (Lη : ℝ) (hLη : 0 < Lη)
    (hη : ∀ x y : ℝ, ‖Work.KMTContract.kmtEta x - Work.KMTContract.kmtEta y‖ ≤ Lη * |x - y|) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ρ : ℝ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε : ℕ → ℂ),
        PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        (∀ n, ‖ε n‖ ≤ 1) → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
        ∀ x : ℝ,
          ‖Work.KMTAreas.A7.randSymb
            (fun n ξ => if n = 0 then 0
              else if Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
                then Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t ξ else 0) ε K x‖ ≤ C := by
  refine ⟨3 * Lη + 2 + max (2 * (Real.log 40 / Real.log ((Λ : ℝ)) + 1)) (4 * Real.pi + 2) + 2, ?_, ?_⟩
  · have hlogΛ : 0 < Real.log ((Λ : ℝ)) := Real.log_pos (by exact_mod_cast hΛ)
    have hl40 : 0 ≤ Real.log 40 / Real.log ((Λ : ℝ)) :=
      div_nonneg (Real.log_nonneg (by norm_num)) hlogΛ.le
    have h1 : 0 ≤ 2 * (Real.log 40 / Real.log ((Λ : ℝ)) + 1) := by linarith
    have h2 : 0 ≤ max (2 * (Real.log 40 / Real.log ((Λ : ℝ)) + 1)) (4 * Real.pi + 2) :=
      le_max_of_le_left h1
    linarith [Real.pi_pos]
  · intro ρ a l₁ l₂ k₁ k₂ K t ε ha ha1 hε ht x
    exact randSymb_bounded_of_varBound Λ hΛ C₀ _ (varBound Lη hLη hη Λ hΛ) ρ a l₁ l₂ k₁ k₂ K t ε
      ha ha1 hε ht x

end
end Work.KMTPlan.A6
