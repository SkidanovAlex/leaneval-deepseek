import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Rat.Star
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds

open scoped ArithmeticFunction.sigma

namespace Commons.NumberTheory.Lagarias

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

private def expLower (x : ℚ) (N : ℕ) : ℚ :=
  ∑ i ∈ Finset.range N, x ^ i / (Nat.factorial i : ℚ)

private def logOneAddLower (t : ℚ) : ℚ :=
  2 * t / (t + 2)

private def logTwoLower : ℚ := 6931471803 / 10000000000

private def logLowerAux (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | k + 1 =>
      if x < 2 then logOneAddLower (x - 1)
      else logTwoLower + logLowerAux (x / 2) k

private def logLower (x : ℚ) : ℚ := logLowerAux x 20

private def sigmaSqrt (n : ℕ) : ℕ :=
  ∑ d ∈ Finset.Icc 1 (Nat.sqrt n), if d ∣ n then (if d * d = n then d else d + n / d) else 0

private lemma one_le_harmonic {n : ℕ} (hn : 0 < n) : 1 ≤ harmonic n := by
  rw [harmonic_eq_sum_Icc]
  have hmem : 1 ∈ Finset.Icc 1 n := by
    exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hsingle := Finset.single_le_sum (s := Finset.Icc 1 n) (f := fun i : ℕ => (i : ℚ)⁻¹) ?_ hmem
  · simpa using hsingle
  · intro i hi
    positivity

private lemma expLower_nonneg {x : ℚ} (hx : 0 ≤ x) (N : ℕ) : 0 ≤ expLower x N := by
  unfold expLower
  refine Finset.sum_nonneg ?_
  intro i hi
  exact div_nonneg (pow_nonneg hx i) (by exact_mod_cast (le_of_lt (Nat.factorial_pos i)))

private lemma expLower_le_exp (x : ℚ) (hx : 0 ≤ x) (N : ℕ) :
    ((expLower x N : ℚ) : ℝ) ≤ Real.exp (x : ℝ) := by
  unfold expLower
  have hxr : 0 ≤ (x : ℝ) := by exact_mod_cast hx
  have h := Real.sum_le_exp_of_nonneg (x := (x : ℝ)) hxr N
  rw [Rat.cast_sum]
  refine le_trans ?_ h
  apply Finset.sum_le_sum
  intro i hi
  rw [Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]

private lemma logOneAddLower_le_log_one_add (t : ℚ) (ht : 0 ≤ t) :
    ((logOneAddLower t : ℚ) : ℝ) ≤ Real.log (1 + (t : ℝ)) := by
  unfold logOneAddLower
  have htr : 0 ≤ (t : ℝ) := by exact_mod_cast ht
  have h := Real.le_log_one_add_of_nonneg htr
  rw [Rat.cast_div, Rat.cast_mul]
  rw [Rat.cast_ofNat]
  rw [Rat.cast_add]
  exact h

private lemma logTwoLower_le_log_two : ((logTwoLower : ℚ) : ℝ) ≤ Real.log 2 := by
  unfold logTwoLower
  have h := Real.log_two_gt_d9
  norm_num at h ⊢
  exact le_of_lt h

private lemma logTwoLower_nonneg : 0 ≤ logTwoLower := by
  unfold logTwoLower
  norm_num

private lemma logLowerAux_nonneg : ∀ k : ℕ, ∀ x : ℚ, 1 ≤ x → 0 ≤ logLowerAux x k := by
  intro k
  induction k with
  | zero =>
      intro x hx
      simp [logLowerAux]
  | succ k ih =>
      intro x hx
      unfold logLowerAux
      by_cases h : x < 2
      · simp [h]
        have ht : 0 ≤ x - 1 := by linarith
        unfold logOneAddLower
        have hden : 0 < (x - 1) + 2 := by linarith
        exact div_nonneg (mul_nonneg zero_le_two ht) (le_of_lt hden)
      · simp [h]
        have hx2 : 2 ≤ x := by exact le_of_not_gt h
        have hxhalf : 1 ≤ x / 2 := by
          have hx2q : (2 : ℚ) ≤ x := by exact_mod_cast hx2
          rw [le_div_iff₀ (by norm_num : (0 : ℚ) < 2)]
          norm_num
          exact hx2q
        exact add_nonneg logTwoLower_nonneg (ih (x / 2) hxhalf)

private lemma logLower_nonneg (x : ℚ) (hx : 1 ≤ x) : 0 ≤ logLower x := by
  unfold logLower
  exact logLowerAux_nonneg 20 x hx

private lemma logLowerAux_le_log : ∀ k : ℕ, ∀ x : ℚ, 1 ≤ x →
    ((logLowerAux x k : ℚ) : ℝ) ≤ Real.log (x : ℝ) := by
  intro k
  induction k with
  | zero =>
      intro x hx
      simp [logLowerAux]
      exact Real.log_nonneg (by exact_mod_cast hx)
  | succ k ih =>
      intro x hx
      unfold logLowerAux
      by_cases h : x < 2
      · simp [h]
        have ht : 0 ≤ x - 1 := by linarith
        have hle := logOneAddLower_le_log_one_add (x - 1) ht
        have harg : (1 : ℝ) + ((x - 1 : ℚ) : ℝ) = (x : ℝ) := by
          norm_cast
          ring
        simpa [harg] using hle
      · simp [h]
        have hx2 : 2 ≤ x := by exact le_of_not_gt h
        have hxhalf : 1 ≤ x / 2 := by
          have hx2q : (2 : ℚ) ≤ x := by exact_mod_cast hx2
          rw [le_div_iff₀ (by norm_num : (0 : ℚ) < 2)]
          norm_num
          exact hx2q
        have hx_eq : (x : ℝ) = 2 * ((x / 2 : ℚ) : ℝ) := by
          have hx_eq_q : x = (2 : ℚ) * (x / 2) := by
            field_simp [show (2 : ℚ) ≠ 0 by norm_num]
          norm_cast
        have hxhalf_ne : ((x / 2 : ℚ) : ℝ) ≠ 0 := by
          have hxhalf_pos : 0 < ((x / 2 : ℚ) : ℝ) := by
            exact_mod_cast (lt_of_lt_of_le zero_lt_one hxhalf)
          exact ne_of_gt hxhalf_pos
        have hlog_mul := Real.log_mul (x := (2 : ℝ)) (y := ((x / 2 : ℚ) : ℝ)) (by norm_num) hxhalf_ne
        have hlog_eq : Real.log (x : ℝ) = Real.log 2 + Real.log ((x / 2 : ℚ) : ℝ) := by
          rw [hx_eq]
          exact hlog_mul
        have hle_add := add_le_add logTwoLower_le_log_two (ih (x / 2) hxhalf)
        exact le_trans hle_add (le_of_eq hlog_eq.symm)

private lemma logLower_le_log (x : ℚ) (hx : 1 ≤ x) :
    ((logLower x : ℚ) : ℝ) ≤ Real.log (x : ℝ) := by
  unfold logLower
  exact logLowerAux_le_log 20 x hx

private lemma harmonic_mono_real {a n : ℕ} (ha : a ≤ n) :
    (harmonic a : ℝ) ≤ (harmonic n : ℝ) := by
  have hQ : (harmonic a : ℚ) ≤ harmonic n := by
    rw [harmonic_eq_sum_Icc, harmonic_eq_sum_Icc]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · exact Finset.Icc_subset_Icc (le_refl 1) ha
    · intro i hi hnot
      positivity
  exact_mod_cast hQ

private lemma rhs_ge_q (n : ℕ) (q : ℚ) (hqpos : 1 ≤ q) (hqn : (q : ℝ) ≤ (harmonic n : ℝ)) :
    (q : ℝ) + Real.exp (q : ℝ) * Real.log (q : ℝ) ≤
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hqpos)
  have hlogq_nonneg : 0 ≤ Real.log (q : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hqpos)
  have hexp_le : Real.exp (q : ℝ) ≤ Real.exp (harmonic n : ℝ) :=
    Real.exp_le_exp.mpr hqn
  have hlog_le : Real.log (q : ℝ) ≤ Real.log (harmonic n : ℝ) :=
    Real.log_le_log hq0 hqn
  have hmul := mul_le_mul hexp_le hlog_le hlogq_nonneg (Real.exp_pos (harmonic n : ℝ)).le
  exact add_le_add hqn hmul

private lemma q_lower_le (q : ℚ) (C : ℕ) (hq1 : 1 ≤ q)
    (hC : ((C : ℕ) : ℚ) ≤ q + expLower q 18 * logLower q) :
    (C : ℝ) ≤ (q : ℝ) + Real.exp (q : ℝ) * Real.log (q : ℝ) := by
  have hq0 : 0 ≤ q := le_trans zero_le_one hq1
  have hE := expLower_le_exp q hq0 18
  have hL := logLower_le_log q hq1
  have hE_nonneg : 0 ≤ ((expLower q 18 : ℚ) : ℝ) := by exact_mod_cast expLower_nonneg hq0 18
  have hL_nonneg : 0 ≤ ((logLower q : ℚ) : ℝ) := by exact_mod_cast logLower_nonneg q hq1
  have hExp_pos : 0 ≤ Real.exp (q : ℝ) := by positivity
  have hmul := mul_le_mul hE hL hL_nonneg hExp_pos
  have hprod : ((expLower q 18 : ℚ) : ℝ) * ((logLower q : ℚ) : ℝ) ≤
      Real.exp (q : ℝ) * Real.log (q : ℝ) := by
    simpa [Rat.cast_mul] using hmul
  have hC' : (C : ℝ) ≤ (q : ℝ) + ((expLower q 18 : ℚ) : ℝ) * ((logLower q : ℚ) : ℝ) := by
    exact_mod_cast hC
  linarith

private lemma check_branch (n : ℕ) (q : ℚ) (C : ℕ) (hq1 : 1 ≤ q)
    (hq_harm : (q : ℝ) ≤ (harmonic n : ℝ))
    (hCq : ((C : ℕ) : ℚ) ≤ q + expLower q 18 * logLower q)
    (hsig_nat : (ArithmeticFunction.sigma 1 n : ℕ) ≤ C) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  have hsig : ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤ (C : ℝ) := by
    exact_mod_cast hsig_nat
  have hC_le := q_lower_le q C hq1 hCq
  have hrhs := rhs_ge_q n q hq1 hq_harm
  linarith

private lemma divisors_filter_le_sqrt_eq (n : ℕ) (hn : 0 < n) :
    n.divisors.filter (fun d => d ≤ Nat.sqrt n) =
      (Finset.Icc 1 (Nat.sqrt n)).filter (fun d => d ∣ n) := by
  ext d
  by_cases hdpos : 0 < d
  · simp [Nat.mem_divisors, Finset.mem_filter, hn.ne']
    constructor
    · intro h
      exact ⟨⟨by omega, h.2⟩, h.1⟩
    · intro h
      exact ⟨h.2, h.1.2⟩
  · have hd0 : d = 0 := by omega
    subst d
    simp [hn.ne']

private lemma large_divisors_sum_eq (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors.filter (fun d => Nat.sqrt n < d), d) =
      ∑ d ∈ n.divisors.filter (fun d => d ≤ Nat.sqrt n ∧ d * d ≠ n), n / d := by
  refine Finset.sum_bij (fun d hd => n / d) ?hi ?hinj ?hsurj ?h
  · intro d hd
    have hdmem := (Finset.mem_filter.mp hd).1
    have hdgt := (Finset.mem_filter.mp hd).2
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hdmem).1
    have hdpos : 0 < d := by
      have : 0 ≤ Nat.sqrt n := Nat.zero_le _
      omega
    have hndvd : n / d ∣ n := Nat.div_dvd_of_dvd hdvd
    have hndmem : n / d ∈ n.divisors := Nat.mem_divisors.mpr ⟨hndvd, by omega⟩
    have hdecomp0 : n / d * d = n := Nat.div_mul_cancel hdvd
    have hdecomp : n = d * (n / d) := by
      simpa [mul_comm] using hdecomp0.symm
    have hndpos : 0 < n / d := by
      exact Nat.div_pos (Nat.le_of_dvd hn hdvd) hdpos
    have hnd_lt_d : n / d < d := by
      have hmain : n < d * d := by
        rw [← Nat.sqrt_lt]
        exact hdgt
      rw [hdecomp] at hmain
      exact (Nat.mul_lt_mul_left hdpos).mp hmain
    have hmul : n / d * (n / d) < n := by
      have h1 : n / d * (n / d) < n / d * d := by
        exact (Nat.mul_lt_mul_left hndpos).mpr hnd_lt_d
      simpa [hdecomp0] using h1
    have hnd_le_sqrt : n / d ≤ Nat.sqrt n := by
      rw [Nat.le_sqrt]
      exact le_of_lt hmul
    have hnd_nonsq : n / d * (n / d) ≠ n := by
      omega
    exact Finset.mem_filter.mpr ⟨hndmem, ⟨hnd_le_sqrt, hnd_nonsq⟩⟩
  · intro a ha b hb hab
    have hamem := (Finset.mem_filter.mp ha).1
    have hbmem := (Finset.mem_filter.mp hb).1
    have hadvd : a ∣ n := (Nat.mem_divisors.mp hamem).1
    have hbdvd : b ∣ n := (Nat.mem_divisors.mp hbmem).1
    have hdiva : n / (n / a) = a := Nat.div_div_self hadvd (by omega)
    have hdivb : n / (n / b) = b := Nat.div_div_self hbdvd (by omega)
    calc
      a = n / (n / a) := hdiva.symm
      _ = n / (n / b) := by rw [hab]
      _ = b := hdivb
  · intro b hb
    have hbmem := (Finset.mem_filter.mp hb).1
    have hble := (Finset.mem_filter.mp hb).2.1
    have hbns := (Finset.mem_filter.mp hb).2.2
    have hbdvd : b ∣ n := (Nat.mem_divisors.mp hbmem).1
    have hbpos : 0 < b := by
      by_contra hb0
      have hb0' : b = 0 := by omega
      subst b
      simp at hbdvd
      omega
    have hdpos : 0 < n / b := Nat.div_pos (Nat.le_of_dvd hn hbdvd) hbpos
    have hdecomp0 : n / b * b = n := Nat.div_mul_cancel hbdvd
    have hdecomp : n = b * (n / b) := by
      simpa [mul_comm] using hdecomp0.symm
    have hb_le_sq : b * b ≤ n := by
      rw [Nat.le_sqrt] at hble
      exact hble
    have hb_sq_lt : b * b < n := lt_of_le_of_ne hb_le_sq hbns
    have hb_lt_nd : b < n / b := by
      rw [hdecomp] at hb_sq_lt
      exact (Nat.mul_lt_mul_left hbpos).mp hb_sq_lt
    have hndgt : Nat.sqrt n < n / b := by
      rw [Nat.sqrt_lt]
      have h1 : b * (n / b) < (n / b) * (n / b) := by
        exact (Nat.mul_lt_mul_right hdpos).mpr hb_lt_nd
      calc
        n = b * (n / b) := hdecomp
        _ < (n / b) * (n / b) := h1
    have hndvd : n / b ∣ n := Nat.div_dvd_of_dvd hbdvd
    have hndmem : n / b ∈ n.divisors := Nat.mem_divisors.mpr ⟨hndvd, by omega⟩
    refine ⟨n / b, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨hndmem, hndgt⟩
    · rw [Nat.div_div_self hbdvd (by omega)]
  · intro a ha
    have hamem := (Finset.mem_filter.mp ha).1
    have hadvd : a ∣ n := (Nat.mem_divisors.mp hamem).1
    exact (Nat.div_div_self hadvd (by omega)).symm

private lemma sigma_eq_sigmaSqrt (n : ℕ) (hn : 0 < n) :
    (ArithmeticFunction.sigma 1 n : ℕ) = sigmaSqrt n := by
  rw [ArithmeticFunction.sigma_one_apply]
  unfold sigmaSqrt
  let s : Finset ℕ := n.divisors.filter (fun d => d ≤ Nat.sqrt n)
  let t : Finset ℕ := n.divisors.filter (fun d => Nat.sqrt n < d)
  have hset := divisors_filter_le_sqrt_eq n hn
  have hsmall_final : (∑ d ∈ s, (if d * d = n then d else d + n / d)) =
      ∑ d ∈ Finset.Icc 1 (Nat.sqrt n), if d ∣ n then (if d * d = n then d else d + n / d) else 0 := by
    change (∑ d ∈ n.divisors.filter (fun d => d ≤ Nat.sqrt n), (if d * d = n then d else d + n / d)) =
      ∑ d ∈ Finset.Icc 1 (Nat.sqrt n), if d ∣ n then (if d * d = n then d else d + n / d) else 0
    rw [hset]
    rw [Finset.sum_filter]
  have hsplit_total : (∑ d ∈ n.divisors, d) =
      (∑ d ∈ s, d) + (∑ d ∈ t, d) := by
    have h := Finset.sum_filter_add_sum_filter_not (s := n.divisors) (p := fun d => d ≤ Nat.sqrt n) (f := fun d : ℕ => d)
    change (∑ d ∈ n.divisors, d) = (∑ d ∈ s, d) + (∑ d ∈ t, d)
    simpa [s, t, not_le] using h.symm
  have hsplit_small_id : (∑ d ∈ s, d) =
      (∑ d ∈ s.filter (fun d => d * d = n), d) +
        (∑ d ∈ s.filter (fun d => d * d ≠ n), d) := by
    have h := Finset.sum_filter_add_sum_filter_not (s := s) (p := fun d => d * d = n) (f := fun d : ℕ => d)
    simpa using h.symm
  have hsplit_small_f : (∑ d ∈ s, (if d * d = n then d else d + n / d)) =
      (∑ d ∈ s.filter (fun d => d * d = n), d) +
        (∑ d ∈ s.filter (fun d => d * d ≠ n), (d + n / d)) := by
    have h := Finset.sum_filter_add_sum_filter_not (s := s) (p := fun d => d * d = n) (f := fun d : ℕ => (if d * d = n then d else d + n / d))
    have hsq : (∑ d ∈ s.filter (fun d => d * d = n), (if d * d = n then d else d + n / d)) =
        ∑ d ∈ s.filter (fun d => d * d = n), d := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd' : d * d = n := (Finset.mem_filter.mp hd).2
      simp [hd']
    have hnsq : (∑ d ∈ s.filter (fun d => d * d ≠ n), (if d * d = n then d else d + n / d)) =
        ∑ d ∈ s.filter (fun d => d * d ≠ n), (d + n / d) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd' : d * d ≠ n := (Finset.mem_filter.mp hd).2
      simp [hd']
    calc
      (∑ d ∈ s, (if d * d = n then d else d + n / d)) =
          (∑ d ∈ s.filter (fun d => d * d = n), (if d * d = n then d else d + n / d)) +
            (∑ d ∈ s.filter (fun d => d * d ≠ n), (if d * d = n then d else d + n / d)) := h.symm
      _ = (∑ d ∈ s.filter (fun d => d * d = n), d) +
            (∑ d ∈ s.filter (fun d => d * d ≠ n), (d + n / d)) := by rw [hsq, hnsq]
  have hlarge := large_divisors_sum_eq n hn
  have hlarge' : (∑ d ∈ t, d) =
      ∑ d ∈ s.filter (fun d => d * d ≠ n), n / d := by
    change (∑ d ∈ n.divisors.filter (fun d => Nat.sqrt n < d), d) =
      ∑ d ∈ s.filter (fun d => d * d ≠ n), n / d
    rw [hlarge]
    have hfilter : n.divisors.filter (fun d => d ≤ Nat.sqrt n ∧ d * d ≠ n) =
        s.filter (fun d => d * d ≠ n) := by
      change n.divisors.filter (fun d => d ≤ Nat.sqrt n ∧ d * d ≠ n) =
          (n.divisors.filter (fun d => d ≤ Nat.sqrt n)).filter (fun d => d * d ≠ n)
      rw [Finset.filter_filter]
    rw [hfilter]
  calc
    ∑ d ∈ n.divisors, d = (∑ d ∈ s, d) + (∑ d ∈ t, d) := hsplit_total
    _ = ((∑ d ∈ s.filter (fun d => d * d = n), d) +
          (∑ d ∈ s.filter (fun d => d * d ≠ n), d)) +
          (∑ d ∈ s.filter (fun d => d * d ≠ n), n / d) := by rw [hsplit_small_id, hlarge']
    _ = (∑ d ∈ s.filter (fun d => d * d = n), d) +
          ((∑ d ∈ s.filter (fun d => d * d ≠ n), d) +
            (∑ d ∈ s.filter (fun d => d * d ≠ n), n / d)) := by omega
    _ = (∑ d ∈ s.filter (fun d => d * d = n), d) +
          (∑ d ∈ s.filter (fun d => d * d ≠ n), (d + n / d)) := by
          rw [← Finset.sum_add_distrib]
    _ = ∑ d ∈ s, (if d * d = n then d else d + n / d) := by
          rw [hsplit_small_f]
    _ = ∑ d ∈ Finset.Icc 1 (Nat.sqrt n), if d ∣ n then (if d * d = n then d else d + n / d) else 0 := hsmall_final

private lemma sigma_le_10416_range_3001_3200 (n : ℕ) (hL : 3001 ≤ n) (hU : n ≤ 3200) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 10416 := by
  have hn : 0 < n := by omega
  rw [sigma_eq_sigmaSqrt n hn]
  have hmem : n ∈ Finset.Icc 3001 3200 := Finset.mem_Icc.mpr ⟨hL, hU⟩
  have hcheck : ∀ k ∈ Finset.Icc 3001 3200, sigmaSqrt k ≤ 10416 := by
    intro k hk
    obtain ⟨hkL, hkU⟩ := Finset.mem_Icc.mp hk
    interval_cases k <;> decide +kernel
  exact hcheck n hmem

private lemma sigma_le_12096_range_3201_3500 (n : ℕ) (hL : 3201 ≤ n) (hU : n ≤ 3500) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 12096 := by
  have hn : 0 < n := by omega
  rw [sigma_eq_sigmaSqrt n hn]
  have hmem : n ∈ Finset.Icc 3201 3500 := Finset.mem_Icc.mpr ⟨hL, hU⟩
  have hcheck : ∀ k ∈ Finset.Icc 3201 3500, sigmaSqrt k ≤ 12096 := by
    intro k hk
    obtain ⟨hkL, hkU⟩ := Finset.mem_Icc.mp hk
    interval_cases k <;> decide +kernel
  exact hcheck n hmem

private lemma harmonic_ge_858_100_range_3001_3200 (n : ℕ) (hL : 3001 ≤ n) (hU : n ≤ 3200) :
    (((858 : ℚ) / 100 : ℚ) : ℝ) ≤ (harmonic n : ℝ) := by
  have hmono := harmonic_mono_real (a := 3001) (n := n) (by omega)
  have hbase : (((858 : ℚ) / 100 : ℚ) : ℝ) ≤ (harmonic 3001 : ℝ) := by
    norm_num [harmonic_eq_sum_Icc]
  exact le_trans hbase hmono

private lemma harmonic_ge_864_100_range_3201_3500 (n : ℕ) (hL : 3201 ≤ n) (hU : n ≤ 3500) :
    (((864 : ℚ) / 100 : ℚ) : ℝ) ≤ (harmonic n : ℝ) := by
  have hmono := harmonic_mono_real (a := 3201) (n := n) (by omega)
  have hbase : (((864 : ℚ) / 100 : ℚ) : ℝ) ≤ (harmonic 3201 : ℝ) := by
    norm_num [harmonic_eq_sum_Icc]
  exact le_trans hbase hmono

private lemma q_858_100_lower_ge_10416 :
    ((10416 : ℕ) : ℚ) ≤ ((858 : ℚ) / 100) + expLower ((858 : ℚ) / 100) 18 * logLower ((858 : ℚ) / 100) := by
  norm_num [expLower, logLower, logLowerAux, logOneAddLower, logTwoLower]

private lemma q_864_100_lower_ge_12096 :
    ((12096 : ℕ) : ℚ) ≤ ((864 : ℚ) / 100) + expLower ((864 : ℚ) / 100) 18 * logLower ((864 : ℚ) / 100) := by
  norm_num [expLower, logLower, logLowerAux, logOneAddLower, logTwoLower]

private lemma one_le_858_100 : 1 ≤ ((858 : ℚ) / 100) := by norm_num

private lemma one_le_864_100 : 1 ≤ ((864 : ℚ) / 100) := by norm_num

theorem finite_check_range_3001_3500 (n : ℕ) (hn0 : 0 < n) (hL : 3001 ≤ n) (hU : n ≤ 3500) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  by_cases hle3200 : n ≤ 3200
  · exact check_branch n ((858 : ℚ) / 100) 10416 one_le_858_100
      (harmonic_ge_858_100_range_3001_3200 n hL hle3200)
      q_858_100_lower_ge_10416
      (sigma_le_10416_range_3001_3200 n hL hle3200)
  · have hge3201 : 3201 ≤ n := by omega
    exact check_branch n ((864 : ℚ) / 100) 12096 one_le_864_100
      (harmonic_ge_864_100_range_3201_3500 n hge3201 hU)
      q_864_100_lower_ge_12096
      (sigma_le_12096_range_3201_3500 n hge3201 hU)

end Commons.NumberTheory.Lagarias