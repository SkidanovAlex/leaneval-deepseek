import Mathlib

open scoped NumberField WithZero
open IsDedekindDomain

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace Commons.Analysis.Nonarchimedean

open IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]

/-- The rational prime underlying the finite place `v`. -/
private def adicPrime (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Ideal.absNorm (Ideal.under ℤ v.asIdeal)

private lemma adicPrime_prime (v : HeightOneSpectrum (𝓞 K)) : (adicPrime v).Prime := by
  haveI : NeZero v.asIdeal := ⟨v.ne_bot⟩
  haveI : v.asIdeal.IsPrime := v.isPrime
  exact Nat.absNorm_under_prime v.asIdeal

private lemma adicPrime_mem (v : HeightOneSpectrum (𝓞 K)) :
    ((adicPrime v : ℕ) : 𝓞 K) ∈ v.asIdeal :=
  Int.absNorm_under_mem v.asIdeal

private lemma natCast_mem_iff (v : HeightOneSpectrum (𝓞 K)) (j : ℕ) :
    (j : 𝓞 K) ∈ v.asIdeal ↔ adicPrime v ∣ j := by
  have h : ((j : 𝓞 K)) = ((j : ℤ) : 𝓞 K) := by norm_cast
  rw [h, Int.cast_mem_ideal_iff]
  constructor
  · intro hdvd
    exact_mod_cast hdvd
  · intro hdvd
    exact_mod_cast (Int.natCast_dvd_natCast.mpr hdvd)

private lemma adicCompletion_natCast_val (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Valued.v ((n : ℕ) : v.adicCompletion K) = intValuation v (n : 𝓞 K) := by
  have hco : ((n : ℕ) : v.adicCompletion K) =
      algebraMap (𝓞 K) (v.adicCompletion K) ((n : ℕ) : 𝓞 K) := by
    rw [map_natCast]
  rw [hco]
  exact (valuedAdicCompletion_eq_valuation v ((n : ℕ) : 𝓞 K)).trans
    (valuation_of_algebraMap v ((n : ℕ) : 𝓞 K))

private lemma adicCompletion_natCast_lt_one_iff (v : HeightOneSpectrum (𝓞 K)) (j : ℕ) :
    Valued.v ((j : ℕ) : v.adicCompletion K) < (1 : ℤᵐ⁰) ↔ adicPrime v ∣ j := by
  rw [adicCompletion_natCast_val, intValuation_lt_one_iff_mem, natCast_mem_iff]

private lemma natCast_val_ne_zero (v : HeightOneSpectrum (𝓞 K)) {j : ℕ} (hj : j ≠ 0) :
    Valued.v ((j : ℕ) : v.adicCompletion K) ≠ 0 := by
  rw [adicCompletion_natCast_val]
  exact intValuation_ne_zero v _ (Nat.cast_ne_zero.mpr hj)

private lemma natCast_val_le_one (v : HeightOneSpectrum (𝓞 K)) (j : ℕ) :
    Valued.v ((j : ℕ) : v.adicCompletion K) ≤ (1 : ℤᵐ⁰) := by
  rw [adicCompletion_natCast_val]
  exact intValuation_le_one v _

/-- The additive exponent of the rational prime `adicPrime v`:
`Valued.v (adicPrime v) = WithZero.exp (wq v)`. -/
private def wq (v : HeightOneSpectrum (𝓞 K)) : ℤ :=
  (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)).log

private lemma adicPrime_val_ne_zero (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((adicPrime v : ℕ) : v.adicCompletion K) ≠ 0 :=
  natCast_val_ne_zero v (adicPrime_prime v).ne_zero

private lemma exp_wq (v : HeightOneSpectrum (𝓞 K)) :
    WithZero.exp (wq v) = Valued.v ((adicPrime v : ℕ) : v.adicCompletion K) :=
  WithZero.exp_log (adicPrime_val_ne_zero v)

private lemma wq_lt_zero (v : HeightOneSpectrum (𝓞 K)) : wq v < 0 := by
  have hlt : Valued.v ((adicPrime v : ℕ) : v.adicCompletion K) < (1 : ℤᵐ⁰) :=
    (adicCompletion_natCast_lt_one_iff v (adicPrime v)).mpr dvd_rfl
  rw [← exp_wq v, ← WithZero.exp_zero] at hlt
  exact WithZero.exp_lt_exp.mp hlt

private lemma wq_le_neg_one (v : HeightOneSpectrum (𝓞 K)) : wq v ≤ -1 := by
  have := wq_lt_zero v; omega

/-- Additive form of the valuation of a positive natural number. -/
private lemma natCast_val_log (v : HeightOneSpectrum (𝓞 K)) :
    ∀ j : ℕ, 1 ≤ j →
      (Valued.v ((j : ℕ) : v.adicCompletion K)).log
        = (padicValNat (adicPrime v) j : ℤ) * wq v := by
  haveI : Fact (adicPrime v).Prime := ⟨adicPrime_prime v⟩
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases eq_or_lt_of_le hj with rfl | hj2
    · have h1 : ((1 : ℕ) : v.adicCompletion K) = 1 := by norm_cast
      rw [h1, map_one, WithZero.log_one, padicValNat_one_right]
      simp
    · by_cases hdvd : adicPrime v ∣ j
      · obtain ⟨m, rfl⟩ := hdvd
        have hm0 : m ≠ 0 := by
          rintro rfl; simp at hj2
        have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
        have hmlt : m < adicPrime v * m := by
          calc m = 1 * m := (one_mul m).symm
            _ < adicPrime v * m := Nat.mul_lt_mul_of_pos_right (adicPrime_prime v).one_lt
                (Nat.pos_of_ne_zero hm0)
        have hcast : (((adicPrime v) * m : ℕ) : v.adicCompletion K)
            = ((adicPrime v : ℕ) : v.adicCompletion K) * ((m : ℕ) : v.adicCompletion K) := by
          rw [Nat.cast_mul]
        rw [hcast, map_mul,
          WithZero.log_mul (adicPrime_val_ne_zero v) (natCast_val_ne_zero v hm0)]
        rw [ih m hmlt hm1]
        have hL : (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)).log = wq v := rfl
        rw [hL]
        have hqm : padicValNat (adicPrime v) (adicPrime v * m)
            = 1 + padicValNat (adicPrime v) m := by
          rw [padicValNat.mul (adicPrime_prime v).ne_zero hm0, padicValNat_self]
        rw [hqm]
        push_cast
        ring
      · have hnotlt : ¬ Valued.v ((j : ℕ) : v.adicCompletion K) < (1 : ℤᵐ⁰) := by
          rw [adicCompletion_natCast_lt_one_iff]
          exact hdvd
        have hle := natCast_val_le_one v j
        have hone : Valued.v ((j : ℕ) : v.adicCompletion K) = 1 :=
          le_antisymm hle (not_lt.mp hnotlt)
        rw [hone, WithZero.log_one, padicValNat.eq_zero_of_not_dvd hdvd]
        simp

private lemma factorial_val_log (v : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    (Valued.v ((k.factorial : ℕ) : v.adicCompletion K)).log
      = (padicValNat (adicPrime v) k.factorial : ℤ) * wq v := by
  haveI : Fact (adicPrime v).Prime := ⟨adicPrime_prime v⟩
  induction k with
  | zero =>
      have h1 : (Valued.v ((Nat.factorial 0 : ℕ) : v.adicCompletion K)).log = 0 := by
        rw [Nat.factorial_zero]; simp
      have h2 : padicValNat (adicPrime v) (Nat.factorial 0) = 0 := by
        rw [Nat.factorial_zero]; exact padicValNat_one_right (adicPrime v)
      rw [h1, h2]; simp
  | succ k ih =>
      have hfac : ((k + 1).factorial : ℕ) = (k + 1) * k.factorial := Nat.factorial_succ k
      have hcast : (((k + 1) * k.factorial : ℕ) : v.adicCompletion K)
          = ((k + 1 : ℕ) : v.adicCompletion K) * ((k.factorial : ℕ) : v.adicCompletion K) := by
        rw [Nat.cast_mul]
      rw [hfac, hcast, map_mul,
        WithZero.log_mul (natCast_val_ne_zero v (by omega)) (natCast_val_ne_zero v (Nat.factorial_ne_zero k)),
        ih, natCast_val_log v (k + 1) (by omega)]
      have hmul : padicValNat (adicPrime v) ((k + 1) * k.factorial)
          = padicValNat (adicPrime v) (k + 1) + padicValNat (adicPrime v) (k.factorial) :=
        padicValNat.mul (by omega) (Nat.factorial_ne_zero k)
      rw [hmul]
      push_cast
      ring

private lemma padicValNat_factorial_le_pred (v : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    padicValNat (adicPrime v) k.factorial ≤ k - 1 := by
  haveI : Fact (adicPrime v).Prime := ⟨adicPrime_prime v⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using padicValNat_factorial_le (adicPrime v) 0
  · have h := padicValNat_factorial_lt_of_ne_zero (p := adicPrime v) (n := k) (by omega)
    omega

private lemma factorial_val_log_ge (v : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    ((k - 1 : ℕ) : ℤ) * wq v
      ≤ (Valued.v ((k.factorial : ℕ) : v.adicCompletion K)).log := by
  rw [factorial_val_log v k]
  have h1 : (padicValNat (adicPrime v) k.factorial : ℤ) ≤ ((k - 1 : ℕ) : ℤ) := by
    exact_mod_cast padicValNat_factorial_le_pred v k
  have h2 : wq v ≤ 0 := le_of_lt (wq_lt_zero v)
  nlinarith [h1, h2]

/-- The norm of the rational prime `adicPrime v` (a real number in `(0,1)`). -/
private def rho (v : HeightOneSpectrum (𝓞 K)) : ℝ :=
  ‖((adicPrime v : ℕ) : v.adicCompletion K)‖

private lemma rho_pos (v : HeightOneSpectrum (𝓞 K)) : 0 < rho v := by
  rw [rho, norm_pos_iff]
  intro h
  exact adicPrime_val_ne_zero v (by rw [h, map_zero])

private lemma rho_lt_one (v : HeightOneSpectrum (𝓞 K)) : rho v < 1 := by
  have hlt : Valued.v ((adicPrime v : ℕ) : v.adicCompletion K) < (1 : ℤᵐ⁰) :=
    (adicCompletion_natCast_lt_one_iff v (adicPrime v)).mpr dvd_rfl
  have h : ‖((adicPrime v : ℕ) : v.adicCompletion K)‖ < ‖(1 : v.adicCompletion K)‖ :=
    (Valued.toNormedField.norm_lt_iff).mpr (by simpa using hlt)
  simpa [rho] using h

private lemma exists_depth (v : HeightOneSpectrum (𝓞 K)) :
    ∃ D : ℕ, 1 ≤ D ∧ rho v ^ (D - 1) ≤ 1 / 3 := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / 3 by norm_num) (rho_lt_one v)
  exact ⟨N + 1, by omega, by simpa using hN.le⟩

private lemma norm_factorial_ge (v : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    rho v ^ (k - 1) ≤ ‖((k.factorial : ℕ) : v.adicCompletion K)‖ := by
  have hvk : Valued.v ((k.factorial : ℕ) : v.adicCompletion K) ≠ 0 :=
    natCast_val_ne_zero v (Nat.factorial_ne_zero k)
  have hq : Valued.v ((adicPrime v : ℕ) : v.adicCompletion K) = WithZero.exp (wq v) :=
    (exp_wq v).symm
  rw [rho, ← norm_pow, Valued.toNormedField.norm_le_iff, map_pow, hq,
    ← WithZero.exp_log hvk, ← WithZero.exp_nsmul]
  exact WithZero.exp_le_exp.mpr (factorial_val_log_ge v k)

private lemma val_le_prime_pow_norm_le (v : HeightOneSpectrum (𝓞 K)) {D : ℕ}
    {x : v.adicCompletion K}
    (hx : Valued.v x ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D) :
    ‖x‖ ≤ rho v ^ D := by
  rw [rho, ← norm_pow, Valued.toNormedField.norm_le_iff, map_pow]
  exact hx

/-- For `1 ≤ D` and `v x ≤ v(q)^D`, the `n`-th Taylor term of `exp x` is bounded by the
geometric term `(rho v^(D-1))^n`. -/
private lemma term_norm_le (v : HeightOneSpectrum (𝓞 K)) {D : ℕ} (hD1 : 1 ≤ D)
    {x : v.adicCompletion K}
    (hx : Valued.v x ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D) (n : ℕ) :
    ‖x ^ n / ((n.factorial : ℕ) : v.adicCompletion K)‖ ≤ (rho v ^ (D - 1)) ^ n := by
  have hρ := rho_pos v
  have hxnorm : ‖x‖ ≤ rho v ^ D := val_le_prime_pow_norm_le v hx
  have hfn : rho v ^ (n - 1) ≤ ‖((n.factorial : ℕ) : v.adicCompletion K)‖ :=
    norm_factorial_ge v n
  have hfn' : rho v ^ n ≤ ‖((n.factorial : ℕ) : v.adicCompletion K)‖ :=
    le_trans (pow_le_pow_of_le_one (le_of_lt hρ) (le_of_lt (rho_lt_one v)) (Nat.sub_le n 1)) hfn
  rw [norm_div, norm_pow]
  calc ‖x‖ ^ n / ‖((n.factorial : ℕ) : v.adicCompletion K)‖
      ≤ (rho v ^ D) ^ n / rho v ^ n := by
        refine div_le_div₀ (pow_nonneg (pow_nonneg (le_of_lt hρ) D) n) ?_ (pow_pos hρ _) hfn'
        exact pow_le_pow_left₀ (norm_nonneg x) hxnorm n
    _ = ((rho v ^ D) / rho v) ^ n := (div_pow _ _ _).symm
    _ = (rho v ^ (D - 1)) ^ n := by
        congr 1
        rw [pow_sub₀ (rho v) (ne_of_gt hρ) hD1, pow_one, div_eq_mul_inv]

private lemma expSeries_summable (v : HeightOneSpectrum (𝓞 K)) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : rho v ^ (D - 1) ≤ 1 / 3) {x : v.adicCompletion K}
    (hx : Valued.v x ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D) :
    Summable (fun n : ℕ => x ^ n / ((n.factorial : ℕ) : v.adicCompletion K)) := by
  refine Summable.of_norm_bounded ?_ (fun n => term_norm_le v hD1 hx n)
  have hlt : ‖(rho v ^ (D - 1))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_of_lt (rho_pos v)) _)]
    linarith
  simpa using summable_geometric_of_norm_lt_one (R := ℝ) hlt

private lemma norm_add_le_max (v : HeightOneSpectrum (𝓞 K)) (x y : v.adicCompletion K) :
    ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  rcases le_total (Valued.v x) (Valued.v y) with hle | hle
  · have h2 : Valued.v (x + y) ≤ Valued.v y := by
      simpa [max_eq_right hle] using
        Valuation.map_add (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) x y
    exact ((Valued.toNormedField.norm_le_iff).mpr h2).trans (le_max_right _ _)
  · have h2 : Valued.v (x + y) ≤ Valued.v x := by
      simpa [max_eq_left hle] using
        Valuation.map_add (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) x y
    exact ((Valued.toNormedField.norm_le_iff).mpr h2).trans (le_max_left _ _)

private lemma val_add_le_max (v : HeightOneSpectrum (𝓞 K)) (a b : v.adicCompletion K) :
    Valued.v (a + b) ≤ max (Valued.v a) (Valued.v b) :=
  Valuation.map_add (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) a b

private lemma norm_sum_range_le (v : HeightOneSpectrum (𝓞 K)) {f : ℕ → v.adicCompletion K}
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) :
    ∀ N : ℕ, ‖∑ n ∈ Finset.range N, f n‖ ≤ C := by
  intro N
  induction N with
  | zero => simpa using hC
  | succ N ih =>
      rw [Finset.sum_range_succ]
      exact (norm_add_le_max v _ _).trans (max_le ih (hf N))

private lemma norm_le_of_hasSum (v : HeightOneSpectrum (𝓞 K)) {f : ℕ → v.adicCompletion K}
    {s : v.adicCompletion K} {C : ℝ} (hC : 0 ≤ C) (h : HasSum f s)
    (hf : ∀ n, ‖f n‖ ≤ C) : ‖s‖ ≤ C := by
  have hmem : s ∈ Metric.closedBall (0 : v.adicCompletion K) C :=
    Metric.isClosed_closedBall.mem_of_tendsto h.tendsto_sum_nat
      (Filter.Eventually.of_forall fun N => by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact norm_sum_range_le v hC hf N)
  rwa [Metric.mem_closedBall, dist_zero_right] at hmem

private lemma norm_pow_sub_pow_le (v : HeightOneSpectrum (𝓞 K)) {x y : v.adicCompletion K}
    {r : ℝ} (hr : 0 ≤ r) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (m : ℕ) (hm : 1 ≤ m) :
    ‖x ^ m - y ^ m‖ ≤ r ^ (m - 1) * ‖x - y‖ := by
  induction m, hm using Nat.le_induction with
  | base => simpa using le_of_eq (by ring : x ^ 1 - y ^ 1 = x - y)
  | succ m hm ih =>
      have hstep : x ^ (m + 1) - y ^ (m + 1) = x ^ m * (x - y) + (x ^ m - y ^ m) * y := by ring
      rw [hstep]
      refine (norm_add_le_max v _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]
        have hxm : ‖x ^ m‖ ≤ r ^ m := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg x) hx m
        calc ‖x ^ m‖ * ‖x - y‖ ≤ r ^ m * ‖x - y‖ :=
              mul_le_mul_of_nonneg_right hxm (norm_nonneg _)
          _ = r ^ ((m + 1) - 1) * ‖x - y‖ := by rw [Nat.add_sub_cancel]
      · rw [norm_mul]
        have hrm : r ^ (m - 1) * r = r ^ m := by
          rw [mul_comm, ← pow_succ', Nat.sub_add_cancel hm]
        calc ‖x ^ m - y ^ m‖ * ‖y‖ ≤ (r ^ (m - 1) * ‖x - y‖) * r :=
              mul_le_mul ih hy (norm_nonneg _) (by positivity)
          _ = r ^ ((m + 1) - 1) * ‖x - y‖ := by
              rw [Nat.add_sub_cancel, mul_comm (r ^ (m - 1)) (‖x - y‖), mul_assoc, hrm, mul_comm]

/-- The `exp` power series, evaluated as an infinite sum. -/
private def expTsum (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    v.adicCompletion K :=
  ∑' n : ℕ, x ^ n / ((n.factorial : ℕ) : v.adicCompletion K)

/-- The series `∑ x^m/(m+1)!`, i.e. `(exp x - 1)/x`. -/
private def uTsum (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    v.adicCompletion K :=
  ∑' m : ℕ, x ^ m / (((m + 1).factorial : ℕ) : v.adicCompletion K)

private lemma u_term_norm_le (v : HeightOneSpectrum (𝓞 K)) {D : ℕ} (hD1 : 1 ≤ D)
    {x : v.adicCompletion K}
    (hx : Valued.v x ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D) (m : ℕ) :
    ‖x ^ m / (((m + 1).factorial : ℕ) : v.adicCompletion K)‖ ≤ (rho v ^ (D - 1)) ^ m := by
  have hρ := rho_pos v
  have hxnorm : ‖x‖ ≤ rho v ^ D := val_le_prime_pow_norm_le v hx
  have hfn : rho v ^ m ≤ ‖(((m + 1).factorial : ℕ) : v.adicCompletion K)‖ := by
    have h := norm_factorial_ge v (m + 1)
    simpa [show m + 1 - 1 = m by omega] using h
  rw [norm_div, norm_pow]
  calc ‖x‖ ^ m / ‖(((m + 1).factorial : ℕ) : v.adicCompletion K)‖
      ≤ (rho v ^ D) ^ m / rho v ^ m := by
        refine div_le_div₀ (pow_nonneg (pow_nonneg (le_of_lt hρ) D) m) ?_ (pow_pos hρ _) hfn
        exact pow_le_pow_left₀ (norm_nonneg x) hxnorm m
    _ = ((rho v ^ D) / rho v) ^ m := (div_pow _ _ _).symm
    _ = (rho v ^ (D - 1)) ^ m := by
        congr 1
        rw [pow_sub₀ (rho v) (ne_of_gt hρ) hD1, pow_one, div_eq_mul_inv]

private lemma uSeries_summable (v : HeightOneSpectrum (𝓞 K)) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : rho v ^ (D - 1) ≤ 1 / 3) {x : v.adicCompletion K}
    (hx : Valued.v x ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D) :
    Summable (fun m : ℕ => x ^ m / (((m + 1).factorial : ℕ) : v.adicCompletion K)) := by
  refine Summable.of_norm_bounded ?_ (fun m => u_term_norm_le v hD1 hx m)
  have hlt : ‖(rho v ^ (D - 1))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_of_lt (rho_pos v)) _)]
    linarith
  simpa using summable_geometric_of_norm_lt_one (R := ℝ) hlt

private lemma expTsum_sub_one_eq (v : HeightOneSpectrum (𝓞 K)) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : rho v ^ (D - 1) ≤ 1 / 3) {x : v.adicCompletion K}
    (hx : Valued.v x ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D) :
    expTsum v x - 1 = x * uTsum v x := by
  have hsum := expSeries_summable v hD1 hD hx
  have hus := uSeries_summable v hD1 hD hx
  have hsplit := hsum.tsum_eq_zero_add
  have h0 : x ^ 0 / ((Nat.factorial 0 : ℕ) : v.adicCompletion K) = 1 := by simp
  have hshift : (∑' n : ℕ, x ^ (n + 1) / (((n + 1).factorial : ℕ) : v.adicCompletion K))
      = x * uTsum v x := by
    rw [uTsum]
    rw [tsum_congr (fun n : ℕ => by rw [pow_succ', mul_div_assoc])]
    exact hus.tsum_mul_left x
  simp only [expTsum]
  rw [hsplit, h0, hshift]
  ring

private lemma norm_uTsum_sub_one_le (v : HeightOneSpectrum (𝓞 K)) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : rho v ^ (D - 1) ≤ 1 / 3) {x : v.adicCompletion K}
    (hx : Valued.v x ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D) :
    ‖uTsum v x - 1‖ ≤ 1 / 3 := by
  have hus := uSeries_summable v hD1 hD hx
  have hρ := rho_pos v
  have hsplit := hus.tsum_eq_zero_add
  have h0 : x ^ 0 / (((0 + 1).factorial : ℕ) : v.adicCompletion K) = 1 := by simp
  have hshift : (∑' m : ℕ, x ^ (m + 1) / (((m + 2).factorial : ℕ) : v.adicCompletion K))
      = uTsum v x - 1 := by
    simp only [uTsum]
    rw [hsplit, h0]
    ring
  rw [← hshift]
  have hsu : Summable (fun m : ℕ => x ^ (m + 1) / (((m + 2).factorial : ℕ) : v.adicCompletion K)) := by
    simpa [Nat.add_assoc] using (summable_nat_add_iff (G := v.adicCompletion K) (f := fun m : ℕ =>
      x ^ m / (((m + 1).factorial : ℕ) : v.adicCompletion K)) 1).mpr hus
  refine norm_le_of_hasSum v (C := 1 / 3) (by norm_num) hsu.hasSum ?_
  intro m
  have hm2 : ‖x ^ (m + 1) / (((m + 2).factorial : ℕ) : v.adicCompletion K)‖
      ≤ (rho v ^ (D - 1)) ^ (m + 1) := by
    have hxnorm : ‖x‖ ≤ rho v ^ D := val_le_prime_pow_norm_le v hx
    have hfn : rho v ^ (m + 1) ≤ ‖(((m + 2).factorial : ℕ) : v.adicCompletion K)‖ := by
      have h := norm_factorial_ge v (m + 2)
      simpa [show m + 2 - 1 = m + 1 by omega] using h
    rw [norm_div, norm_pow]
    calc ‖x‖ ^ (m + 1) / ‖(((m + 2).factorial : ℕ) : v.adicCompletion K)‖
        ≤ (rho v ^ D) ^ (m + 1) / rho v ^ (m + 1) := by
          refine div_le_div₀ (pow_nonneg (pow_nonneg (le_of_lt hρ) D) (m + 1)) ?_
            (pow_pos hρ _) hfn
          exact pow_le_pow_left₀ (norm_nonneg x) hxnorm (m + 1)
      _ = ((rho v ^ D) / rho v) ^ (m + 1) := (div_pow _ _ _).symm
      _ = (rho v ^ (D - 1)) ^ (m + 1) := by
          congr 1
          rw [pow_sub₀ (rho v) (ne_of_gt hρ) hD1, pow_one, div_eq_mul_inv]
  refine hm2.trans ?_
  have hle1 : rho v ^ (D - 1) ≤ 1 := le_trans hD (by norm_num)
  calc (rho v ^ (D - 1)) ^ (m + 1) ≤ (rho v ^ (D - 1)) ^ 1 :=
        pow_le_pow_of_le_one (pow_nonneg (le_of_lt hρ) _) hle1 (by omega)
    _ = rho v ^ (D - 1) := pow_one _
    _ ≤ 1 / 3 := hD

private lemma u_diff_term_norm_le (v : HeightOneSpectrum (𝓞 K)) {D : ℕ} (hD1 : 1 ≤ D)
    {x x' : v.adicCompletion K}
    (hx : Valued.v x ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D)
    (hx' : Valued.v x' ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D) (m : ℕ) :
    ‖x ^ m / (((m + 1).factorial : ℕ) : v.adicCompletion K)
        - x' ^ m / (((m + 1).factorial : ℕ) : v.adicCompletion K)‖ ≤ ‖x - x'‖ / rho v := by
  have hρ := rho_pos v
  have hρle : rho v ≤ 1 := le_of_lt (rho_lt_one v)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [pow_zero, Nat.factorial_one, Nat.cast_one, div_one, sub_self, norm_zero]
    exact div_nonneg (norm_nonneg _) (le_of_lt hρ)
  · have hxnorm : ‖x‖ ≤ rho v ^ D := val_le_prime_pow_norm_le v hx
    have hx'norm : ‖x'‖ ≤ rho v ^ D := val_le_prime_pow_norm_le v hx'
    have hrD : rho v ^ D ≤ rho v := by
      simpa using pow_le_pow_of_le_one (le_of_lt hρ) hρle hD1
    have hfn : rho v ^ m ≤ ‖(((m + 1).factorial : ℕ) : v.adicCompletion K)‖ := by
      have h := norm_factorial_ge v (m + 1)
      simpa [show m + 1 - 1 = m by omega] using h
    rw [← sub_div, norm_div]
    have hnum := norm_pow_sub_pow_le v (pow_nonneg (le_of_lt hρ) D) hxnorm hx'norm m hm
    have hpow : (rho v ^ D) ^ (m - 1) ≤ rho v ^ (m - 1) :=
      pow_le_pow_left₀ (pow_nonneg (le_of_lt hρ) D) hrD (m - 1)
    calc ‖x ^ m - x' ^ m‖ / ‖(((m + 1).factorial : ℕ) : v.adicCompletion K)‖
        ≤ ((rho v ^ D) ^ (m - 1) * ‖x - x'‖) / rho v ^ m :=
          div_le_div₀ (mul_nonneg (pow_nonneg (pow_nonneg (le_of_lt hρ) D) _) (norm_nonneg _))
            hnum (pow_pos hρ _) hfn
      _ ≤ (rho v ^ (m - 1) * ‖x - x'‖) / rho v ^ m := by
          refine div_le_div_of_nonneg_right ?_ (le_of_lt (pow_pos hρ _))
          exact mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ = ‖x - x'‖ / rho v := by
          have hρm : rho v ^ m = rho v ^ (m - 1) * rho v := by
            conv_lhs => rw [show m = (m - 1) + 1 by omega]
            rw [pow_succ]
          rw [div_eq_mul_inv, div_eq_mul_inv, hρm, mul_inv_rev]
          field_simp

private lemma norm_uTsum_sub_le (v : HeightOneSpectrum (𝓞 K)) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : rho v ^ (D - 1) ≤ 1 / 3) {x x' : v.adicCompletion K}
    (hx : Valued.v x ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D)
    (hx' : Valued.v x' ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D) :
    ‖uTsum v x - uTsum v x'‖ ≤ ‖x - x'‖ / rho v := by
  have hxsum := uSeries_summable v hD1 hD hx
  have hx'sum := uSeries_summable v hD1 hD hx'
  have hsub := hxsum.sub hx'sum
  have heq : uTsum v x - uTsum v x'
      = ∑' m : ℕ, (x ^ m / (((m + 1).factorial : ℕ) : v.adicCompletion K)
          - x' ^ m / (((m + 1).factorial : ℕ) : v.adicCompletion K)) := by
    simp only [uTsum]
    exact (hxsum.tsum_sub hx'sum).symm
  rw [heq]
  exact norm_le_of_hasSum v (div_nonneg (norm_nonneg _) (le_of_lt (rho_pos v)))
    hsub.hasSum (fun m => u_diff_term_norm_le v hD1 hx hx' m)

private lemma factorial_cast_ne_zero (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (((n.factorial : ℕ)) : v.adicCompletion K) ≠ 0 := by
  intro h
  have hne := natCast_val_ne_zero v (Nat.factorial_ne_zero n)
  rw [h, map_zero] at hne
  exact hne rfl

private lemma choose_mul_cast (v : HeightOneSpectrum (𝓞 K)) {n k : ℕ} (hk : k ≤ n) :
    (((n.choose k : ℕ)) : v.adicCompletion K)
      * (((k.factorial : ℕ)) : v.adicCompletion K)
      * (((n - k).factorial : ℕ) : v.adicCompletion K)
      = (((n.factorial : ℕ)) : v.adicCompletion K) := by
  have h := Nat.choose_mul_factorial_mul_factorial hk
  have h' : (((n.choose k * k.factorial * (n - k).factorial : ℕ)) : v.adicCompletion K)
      = (((n.factorial : ℕ)) : v.adicCompletion K) := by rw [h]
  push_cast at h'
  exact h' 

private lemma expSummand_eq (v : HeightOneSpectrum (𝓞 K)) (x y : v.adicCompletion K) (n k : ℕ)
    (hk : k ≤ n) :
    x ^ k / (((k.factorial : ℕ)) : v.adicCompletion K)
        * (y ^ (n - k) / (((n - k).factorial : ℕ) : v.adicCompletion K))
      = x ^ k * y ^ (n - k) * (((n.choose k : ℕ)) : v.adicCompletion K)
          / (((n.factorial : ℕ)) : v.adicCompletion K) := by
  have h := choose_mul_cast v hk
  have ha := factorial_cast_ne_zero v k
  have hb := factorial_cast_ne_zero v (n - k)
  have hc := factorial_cast_ne_zero v n
  have hC : (((n.choose k : ℕ)) : v.adicCompletion K) / (((n.factorial : ℕ)) : v.adicCompletion K)
      = 1 / ((((k.factorial : ℕ)) : v.adicCompletion K)
              * (((n - k).factorial : ℕ) : v.adicCompletion K)) := by
    rw [one_div, div_eq_iff hc, eq_comm, inv_mul_eq_iff_eq_mul₀ (mul_ne_zero ha hb)]
    rw [← h]; ring
  rw [div_mul_div_comm]
  conv_rhs => rw [mul_div_assoc]
  rw [hC, mul_one_div]

private lemma sum_range_expSummand (v : HeightOneSpectrum (𝓞 K)) (x y : v.adicCompletion K)
    (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        x ^ k / (((k.factorial : ℕ)) : v.adicCompletion K)
          * (y ^ (n - k) / (((n - k).factorial : ℕ) : v.adicCompletion K))
      = (x + y) ^ n / (((n.factorial : ℕ)) : v.adicCompletion K) := by
  rw [add_pow, Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro k hk
  exact expSummand_eq v x y n k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))

private lemma geom_summable (v : HeightOneSpectrum (𝓞 K)) {D : ℕ}
    (hD : rho v ^ (D - 1) ≤ 1 / 3) :
    Summable (fun n : ℕ => (rho v ^ (D - 1)) ^ n) := by
  have hlt : ‖(rho v ^ (D - 1))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_of_lt (rho_pos v)) _)]
    linarith
  simpa using summable_geometric_of_norm_lt_one (R := ℝ) hlt

private lemma expSeries_norm_summable (v : HeightOneSpectrum (𝓞 K)) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : rho v ^ (D - 1) ≤ 1 / 3) {x : v.adicCompletion K}
    (hx : Valued.v x ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D) :
    Summable (fun n : ℕ => ‖x ^ n / ((n.factorial : ℕ) : v.adicCompletion K)‖) :=
  Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => term_norm_le v hD1 hx n)
    (geom_summable v hD)

private lemma expTsum_add (v : HeightOneSpectrum (𝓞 K)) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : rho v ^ (D - 1) ≤ 1 / 3) {x y : v.adicCompletion K}
    (hx : Valued.v x ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D)
    (hy : Valued.v y ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D) :
    expTsum v (x + y) = expTsum v x * expTsum v y := by
  have hxn := expSeries_norm_summable v hD1 hD hx
  have hyn := expSeries_norm_summable v hD1 hD hy
  have hxy : Valued.v (x + y)
      ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D :=
    (Valuation.map_add (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) x y).trans (max_le hx hy)
  have h1 : expTsum v (x + y)
      = ∑' n : ℕ, ∑ k ∈ Finset.range (n + 1),
          x ^ k / (((k.factorial : ℕ)) : v.adicCompletion K)
            * (y ^ (n - k) / (((n - k).factorial : ℕ) : v.adicCompletion K)) := by
    simp only [expTsum]
    apply tsum_congr
    intro n
    exact (sum_range_expSummand v x y n).symm
  have h2 : (∑' n : ℕ, ∑ k ∈ Finset.range (n + 1),
          x ^ k / (((k.factorial : ℕ)) : v.adicCompletion K)
            * (y ^ (n - k) / (((n - k).factorial : ℕ) : v.adicCompletion K)))
      = expTsum v x * expTsum v y := by
    simp only [expTsum]
    exact (tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hxn hyn).symm
  rw [h1, h2]

private lemma val_uTsum_sub_one_lt_one (v : HeightOneSpectrum (𝓞 K)) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : rho v ^ (D - 1) ≤ 1 / 3) {x : v.adicCompletion K}
    (hx : Valued.v x ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D) :
    Valued.v (uTsum v x - 1) < 1 := by
  have hle := norm_uTsum_sub_one_le v hD1 hD hx
  have hlt : ‖uTsum v x - 1‖ < ‖(1 : v.adicCompletion K)‖ := by rw [norm_one]; linarith
  have h := (Valued.toNormedField.norm_lt_iff).mp hlt
  rwa [map_one] at h

private lemma val_uTsum_le_one (v : HeightOneSpectrum (𝓞 K)) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : rho v ^ (D - 1) ≤ 1 / 3) {x : v.adicCompletion K}
    (hx : Valued.v x ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D) :
    Valued.v (uTsum v x) ≤ 1 := by
  have hvlt := val_uTsum_sub_one_lt_one v hD1 hD hx
  have ha : uTsum v x = 1 + (uTsum v x - 1) := by
    rw [add_comm 1 (uTsum v x - 1), sub_add_cancel]
  rw [ha]
  refine (val_add_le_max v 1 (uTsum v x - 1)).trans ?_
  rw [map_one]
  exact max_le le_rfl (le_of_lt hvlt)

private lemma uTsum_ne_zero (v : HeightOneSpectrum (𝓞 K)) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : rho v ^ (D - 1) ≤ 1 / 3) {x : v.adicCompletion K}
    (hx : Valued.v x ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D) :
    uTsum v x ≠ 0 := by
  intro h
  have := norm_uTsum_sub_one_le v hD1 hD hx
  rw [h, zero_sub, norm_neg, norm_one] at this
  norm_num at this

private lemma expTsum_ne_zero (v : HeightOneSpectrum (𝓞 K)) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : rho v ^ (D - 1) ≤ 1 / 3) {x : v.adicCompletion K}
    (hx : Valued.v x ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D) :
    expTsum v x ≠ 0 := by
  intro h
  have heq := expTsum_sub_one_eq v hD1 hD hx
  rw [h, zero_sub] at heq
  have hmul : x * uTsum v x = (-1 : v.adicCompletion K) := heq.symm
  have hval : Valued.v x * Valued.v (uTsum v x) = 1 := by
    have h1 : Valued.v (-(1 : v.adicCompletion K)) = (1 : WithZero (Multiplicative ℤ)) := by
      rw [Valuation.map_neg, map_one]
    have h2 := congrArg (fun z => Valued.v z) hmul
    rw [map_mul, h1] at h2
    exact h2
  have hule := val_uTsum_le_one v hD1 hD hx
  have hvxge : (1 : ℤᵐ⁰) ≤ Valued.v x := by
    calc (1 : ℤᵐ⁰) = Valued.v x * Valued.v (uTsum v x) := hval.symm
      _ ≤ Valued.v x * 1 := mul_le_mul_of_nonneg_left hule (zero_le)
      _ = Valued.v x := mul_one _
  have hvq_lt : Valued.v ((adicPrime v : ℕ) : v.adicCompletion K) < 1 :=
    (adicCompletion_natCast_lt_one_iff v (adicPrime v)).mpr dvd_rfl
  have hvxle : Valued.v x ≤ Valued.v ((adicPrime v : ℕ) : v.adicCompletion K) := by
    refine hx.trans ?_
    simpa using pow_le_pow_of_le_one (zero_le) (le_of_lt hvq_lt) (m := 1) (n := D) hD1
  exact absurd (le_trans hvxge hvxle) (not_le.mpr hvq_lt)

private lemma expTsum_injective (v : HeightOneSpectrum (𝓞 K)) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : rho v ^ (D - 1) ≤ 1 / 3) {x y : v.adicCompletion K}
    (hx : Valued.v x ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D)
    (hy : Valued.v y ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D)
    (h : expTsum v x = expTsum v y) : x = y := by
  have hxy : Valued.v (x - y)
      ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D := by
    have h1 : Valued.v (x - y) = Valued.v (x + (-y)) := by rw [sub_eq_add_neg]
    rw [h1]
    refine (Valuation.map_add (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) x (-y)).trans ?_
    rw [Valuation.map_neg]
    exact max_le hx hy
  have hyne := expTsum_ne_zero v hD1 hD hy
  have hadd := expTsum_add v hD1 hD hxy hy
  have hx_y : x - y + y = x := by ring
  rw [hx_y, h] at hadd
  have hone : expTsum v (x - y) = 1 :=
    mul_right_cancel₀ hyne (by rw [← hadd, one_mul])
  have hzero : (x - y) * uTsum v (x - y) = 0 := by
    have h := expTsum_sub_one_eq v hD1 hD hxy
    rw [hone] at h
    simpa using h.symm
  rcases mul_eq_zero.mp hzero with h2 | h2
  · exact sub_eq_zero.mp h2
  · exact absurd h2 (uTsum_ne_zero v hD1 hD hxy)

private lemma exists_depth2 (v : HeightOneSpectrum (𝓞 K)) :
    ∃ D : ℕ, 2 ≤ D ∧ rho v ^ (D - 1) ≤ 1 / 3 := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / 3 by norm_num) (rho_lt_one v)
  refine ⟨N + 2, by omega, ?_⟩
  have h1 : rho v ^ (N + 2 - 1) ≤ rho v ^ N := by
    simpa using pow_le_pow_of_le_one (le_of_lt (rho_pos v)) (le_of_lt (rho_lt_one v))
      (show N ≤ N + 2 - 1 by omega)
  linarith [hN.le, h1]

private lemma val_uTsum_eq_one (v : HeightOneSpectrum (𝓞 K)) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : rho v ^ (D - 1) ≤ 1 / 3) {x : v.adicCompletion K}
    (hx : Valued.v x ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D) :
    Valued.v (uTsum v x) = 1 := by
  have hvlt := val_uTsum_sub_one_lt_one v hD1 hD hx
  rw [show uTsum v x = 1 + (uTsum v x - 1) by rw [add_comm 1, sub_add_cancel],
    Valuation.map_add_eq_of_lt_left (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
      (by rw [map_one]; exact hvlt)]
  exact map_one _

private lemma norm_eq_one_of_val_eq_one (v : HeightOneSpectrum (𝓞 K))
    {z : v.adicCompletion K} (hz : Valued.v z = 1) : ‖z‖ = 1 := by
  have h1 : ‖z‖ ≤ ‖(1 : v.adicCompletion K)‖ :=
    (Valued.toNormedField.norm_le_iff).mpr (by rw [hz, map_one])
  have h2 : ‖(1 : v.adicCompletion K)‖ ≤ ‖z‖ :=
    (Valued.toNormedField.norm_le_iff).mpr (by rw [map_one, hz])
  rw [norm_one] at h1 h2
  linarith

private lemma norm_uTsum_eq_one (v : HeightOneSpectrum (𝓞 K)) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : rho v ^ (D - 1) ≤ 1 / 3) {x : v.adicCompletion K}
    (hx : Valued.v x ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D) :
    ‖uTsum v x‖ = 1 :=
  norm_eq_one_of_val_eq_one v (val_uTsum_eq_one v hD1 hD hx)

/-- The closed ball of radius `v (adicPrime v) ^ D` on which all the estimates hold. -/
private def disk (v : HeightOneSpectrum (𝓞 K)) (D : ℕ) : Set (v.adicCompletion K) :=
  {x | Valued.v x ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D}

private lemma mem_disk (v : HeightOneSpectrum (𝓞 K)) (D : ℕ) {x : v.adicCompletion K} :
    x ∈ disk v D ↔ Valued.v x ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D :=
  Iff.rfl

private lemma uTsum_ne_zero' (v : HeightOneSpectrum (𝓞 K)) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : rho v ^ (D - 1) ≤ 1 / 3) {x : v.adicCompletion K}
    (hx : Valued.v x ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D) :
    uTsum v x ≠ 0 := by
  intro hzero
  have hu := val_uTsum_eq_one v hD1 hD hx
  rw [hzero, map_zero] at hu
  exact zero_ne_one hu

private lemma disk_eq_closedBall (v : HeightOneSpectrum (𝓞 K)) (D : ℕ) :
    disk v D = Metric.closedBall (0 : v.adicCompletion K) (rho v ^ D) := by
  ext x
  rw [mem_disk, Metric.mem_closedBall, dist_zero_right]
  constructor
  · intro hx
    have h : Valued.v x ≤ Valued.v ((((adicPrime v : ℕ) : v.adicCompletion K)) ^ D) := by
      rwa [map_pow]
    have h2 : ‖x‖ ≤ ‖(((adicPrime v : ℕ) : v.adicCompletion K)) ^ D‖ :=
      (Valued.toNormedField.norm_le_iff).mpr h
    rw [norm_pow] at h2
    simpa only [rho] using h2
  · intro hx
    rw [rho, ← norm_pow] at hx
    have h := (Valued.toNormedField.norm_le_iff).mp hx
    rwa [map_pow] at h

private lemma isClosed_disk (v : HeightOneSpectrum (𝓞 K)) (D : ℕ) : IsClosed (disk v D) := by
  rw [disk_eq_closedBall]; exact Metric.isClosed_closedBall

private lemma disk_zero_mem (v : HeightOneSpectrum (𝓞 K)) (D : ℕ) :
    (0 : v.adicCompletion K) ∈ disk v D := by
  rw [mem_disk, map_zero]; exact zero_le

private lemma completeSpace_disk (v : HeightOneSpectrum (𝓞 K)) (D : ℕ) :
    CompleteSpace ↥(disk v D) := by
  rw [completeSpace_iff_isComplete_univ, Subtype.isComplete_iff, Subtype.coe_image_univ]
  exact (isClosed_disk v D).isComplete

/-- The contraction map whose fixed points solve `expTsum v x = 1 + w`. -/
private def Tmap (v : HeightOneSpectrum (𝓞 K)) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : rho v ^ (D - 1) ≤ 1 / 3) (w : v.adicCompletion K)
    (hw : Valued.v w ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D) :
    ↥(disk v D) → ↥(disk v D) :=
  fun x => ⟨w * (uTsum v x.1)⁻¹, by
    rw [mem_disk]
    have hu : Valued.v (uTsum v x.1) = 1 := val_uTsum_eq_one v hD1 hD ((mem_disk v D).mp x.2)
    calc Valued.v (w * (uTsum v x.1)⁻¹)
        = Valued.v w := by rw [Valuation.map_mul, Valuation.map_inv, hu, inv_one, mul_one]
      _ ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D := hw⟩

private lemma Tmap_lipschitz (v : HeightOneSpectrum (𝓞 K)) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : rho v ^ (D - 1) ≤ 1 / 3) {w : v.adicCompletion K}
    (hw : Valued.v w ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D) :
    LipschitzWith (1 / 2 : NNReal) (Tmap v hD1 hD w hw) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
  have hρ := rho_pos v
  have hxmem := (mem_disk v D).mp x.2
  have hymem := (mem_disk v D).mp y.2
  have huneX := uTsum_ne_zero' v hD1 hD hxmem
  have huneY := uTsum_ne_zero' v hD1 hD hymem
  have hdiff : (Tmap v hD1 hD w hw x : v.adicCompletion K)
      - (Tmap v hD1 hD w hw y : v.adicCompletion K)
      = w * ((uTsum v y.1 - uTsum v x.1) * ((uTsum v x.1 * uTsum v y.1)⁻¹)) := by
    show (w * (uTsum v x.1)⁻¹) - (w * (uTsum v y.1)⁻¹) = _
    field_simp
  have hZ : ‖((uTsum v x.1 * uTsum v y.1)⁻¹)‖ = 1 := by
    rw [norm_inv, norm_mul, norm_uTsum_eq_one v hD1 hD hxmem,
      norm_uTsum_eq_one v hD1 hD hymem, mul_one, inv_one]
  have hwle : ‖w‖ ≤ rho v ^ D := by
    have h : Valued.v w ≤ Valued.v ((((adicPrime v : ℕ) : v.adicCompletion K)) ^ D) := by
      rwa [map_pow]
    have h2 : ‖w‖ ≤ ‖(((adicPrime v : ℕ) : v.adicCompletion K)) ^ D‖ :=
      (Valued.toNormedField.norm_le_iff).mpr h
    rw [norm_pow] at h2
    simpa only [rho] using h2
  have huxy : ‖uTsum v y.1 - uTsum v x.1‖ ≤ ‖y.1 - x.1‖ / rho v :=
    norm_uTsum_sub_le v hD1 hD hymem hxmem
  have hdx : dist x y = ‖y.1 - x.1‖ := by rw [Subtype.dist_eq, dist_eq_norm, norm_sub_rev]
  calc ‖(Tmap v hD1 hD w hw x : v.adicCompletion K)
        - (Tmap v hD1 hD w hw y : v.adicCompletion K)‖
      = ‖w‖ * ‖uTsum v y.1 - uTsum v x.1‖ * ‖((uTsum v x.1 * uTsum v y.1)⁻¹)‖ := by
        rw [hdiff, norm_mul, norm_mul, mul_assoc]
    _ = ‖w‖ * ‖uTsum v y.1 - uTsum v x.1‖ := by rw [hZ, mul_one]
    _ ≤ rho v ^ D * (‖y.1 - x.1‖ / rho v) :=
        mul_le_mul hwle huxy (norm_nonneg _) (by positivity)
    _ = rho v ^ (D - 1) * ‖y.1 - x.1‖ := by
        have hρD : rho v ^ D = rho v ^ (D - 1) * rho v := by
          conv_lhs => rw [show D = (D - 1) + 1 by omega]
          rw [pow_succ]
        rw [hρD, mul_assoc, mul_div_cancel₀ _ (ne_of_gt hρ)]
    _ ≤ (1 / 2 : NNReal) * dist x y := by
        rw [hdx]
        have h12 : rho v ^ (D - 1) ≤ ((1 / 2 : NNReal) : ℝ) := by
          rw [show ((1 / 2 : NNReal) : ℝ) = 1 / 2 by norm_num]
          exact le_trans hD (by norm_num)
        exact mul_le_mul_of_nonneg_right h12 (norm_nonneg _)

private lemma Tmap_contracting (v : HeightOneSpectrum (𝓞 K)) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : rho v ^ (D - 1) ≤ 1 / 3) {w : v.adicCompletion K}
    (hw : Valued.v w ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D) :
    ContractingWith (1 / 2 : NNReal) (Tmap v hD1 hD w hw) :=
  ⟨by norm_num, Tmap_lipschitz v hD1 hD hw⟩

/-- **Surjectivity of `exp` onto the principal units.** -/
private lemma exists_expTsum_eq (v : HeightOneSpectrum (𝓞 K)) {D : ℕ} (hD2 : 2 ≤ D)
    (hD : rho v ^ (D - 1) ≤ 1 / 3) {y : v.adicCompletion K}
    (hy : Valued.v (y - 1) ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D) :
    ∃ x : v.adicCompletion K,
      Valued.v x ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D
        ∧ expTsum v x = y := by
  have hD1 : 1 ≤ D := by omega
  haveI : Nonempty ↥(disk v D) := ⟨⟨0, disk_zero_mem v D⟩⟩
  haveI : CompleteSpace ↥(disk v D) := completeSpace_disk v D
  let T := Tmap v hD1 hD (y - 1) hy
  have hT : ContractingWith (1 / 2 : NNReal) T := Tmap_contracting v hD1 hD hy
  let x := ContractingWith.fixedPoint T hT
  have hx : T x = x := ContractingWith.fixedPoint_isFixedPt hT
  have hxval : (x : v.adicCompletion K) = (y - 1) * (uTsum v x.1)⁻¹ := by
    have h := congrArg Subtype.val hx
    simpa [T, Tmap] using h.symm
  have hune := uTsum_ne_zero' v hD1 hD ((mem_disk v D).mp x.2)
  have hmul : x.1 * uTsum v x.1 = y - 1 := by
    have h' := congrArg (fun z : v.adicCompletion K => z * uTsum v x.1) hxval
    rw [h', mul_assoc, inv_mul_cancel₀ hune, mul_one]
  refine ⟨x.1, (mem_disk v D).mp x.2, ?_⟩
  have hsub := expTsum_sub_one_eq v hD1 hD ((mem_disk v D).mp x.2)
  rw [hmul] at hsub
  exact sub_left_inj.mp hsub

theorem exists_exp_adicCompletion {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ M : ℕ, 1 ≤ M ∧ ∃ exp : v.adicCompletion K → v.adicCompletion K,
      (∀ x : v.adicCompletion K,
        Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) x ≤
            (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ)) →
          HasSum (fun n : ℕ => x ^ n / ((n.factorial : ℕ) : v.adicCompletion K)) (exp x)) ∧
      (∀ x : v.adicCompletion K,
        Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) x ≤
            (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ)) →
          Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (exp x - 1) =
            Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) x) ∧
      (exp 0 = 1) ∧
      (∀ x y : v.adicCompletion K,
        Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) x ≤
            (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ)) →
        Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) y ≤
            (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ)) →
          exp (x + y) = exp x * exp y) ∧
      (∀ y : v.adicCompletion K,
        Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (y - 1) ≤
            (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ)) →
          ∃ x : v.adicCompletion K,
            Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) x ≤
              (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ)) ∧ exp x = y) := by
  classical
  obtain ⟨D, hD2, hD⟩ := exists_depth2 v
  have hD1 : 1 ≤ D := by omega
  let e : ℕ := (-(wq v)).toNat
  let M : ℕ := e * D
  have he : (e : ℤ) = -(wq v) :=
    Int.toNat_of_nonneg (by have := wq_le_neg_one v; omega)
  have hM1 : 1 ≤ M := by
    have he1 : 1 ≤ e := by
      have h1 : (1 : ℤ) ≤ (e : ℤ) := by
        rw [he]; have := wq_le_neg_one v; omega
      omega
    calc (1 : ℕ) = 1 * 1 := (mul_one 1).symm
      _ ≤ e * D := Nat.mul_le_mul he1 hD1
  let δ : WithZero (Multiplicative ℤ) := WithZero.exp (-(M : ℤ))
  have hδ : δ = Valued.v ((adicPrime v : ℕ) : v.adicCompletion K) ^ D := by
    have h1 : -(M : ℤ) = D • (-(e : ℤ)) := by
      simp only [M, Nat.cast_mul, nsmul_eq_mul]
      ring
    have h2 : WithZero.exp (-(e : ℤ))
        = Valued.v ((adicPrime v : ℕ) : v.adicCompletion K) := by
      rw [he, neg_neg]
      exact exp_wq v
    simp only [δ]
    rw [h1, WithZero.exp_nsmul, h2]
  have hsurj : ∀ y : v.adicCompletion K, Valued.v (y - 1) ≤ δ →
      ∃ x : v.adicCompletion K, Valued.v x ≤ δ ∧ expTsum v x = y := by
    intro y hy
    have hy' : Valued.v (y - 1)
        ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D := by
      rw [← hδ]; exact hy
    obtain ⟨x, hx1, hx2⟩ := exists_expTsum_eq v hD2 hD hy'
    exact ⟨x, by rw [hδ]; exact hx1, hx2⟩
  let expFun : v.adicCompletion K → v.adicCompletion K :=
    fun x => if Valued.v x ≤ δ then expTsum v x else 1
  have hexp_apply : ∀ x : v.adicCompletion K, Valued.v x ≤ δ → expFun x = expTsum v x := by
    intro x hx; simp only [expFun]; rw [if_pos hx]
  refine ⟨M, hM1, expFun, ?_, ?_, ?_, ?_, ?_⟩
  · -- HasSum
    intro x hx
    have hx' : Valued.v x ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D := by
      rw [← hδ]; exact hx
    rw [hexp_apply x hx]
    exact (expSeries_summable v hD1 hD hx').hasSum
  · -- valuation of exp x - 1
    intro x hx
    have hx' : Valued.v x ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D := by
      rw [← hδ]; exact hx
    rw [hexp_apply x hx, expTsum_sub_one_eq v hD1 hD hx',
      Valuation.map_mul, val_uTsum_eq_one v hD1 hD hx', mul_one]
  · -- exp 0 = 1
    have h0 : Valued.v (0 : v.adicCompletion K) ≤ δ := by rw [map_zero]; exact zero_le
    rw [hexp_apply 0 h0]
    have hsub := expTsum_sub_one_eq v hD1 hD (x := 0) (by rw [map_zero]; exact zero_le)
    rw [zero_mul] at hsub
    exact sub_eq_zero.mp hsub
  · -- additivity
    intro x y hx hy
    have hx' : Valued.v x ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D := by
      rw [← hδ]; exact hx
    have hy' : Valued.v y ≤ (Valued.v ((adicPrime v : ℕ) : v.adicCompletion K)) ^ D := by
      rw [← hδ]; exact hy
    have hxy : Valued.v (x + y) ≤ δ := by
      rw [hδ]
      exact (val_add_le_max v x y).trans (max_le hx' hy')
    rw [hexp_apply (x + y) hxy, hexp_apply x hx, hexp_apply y hy,
      expTsum_add v hD1 hD hx' hy']
  · -- surjectivity
    intro y hy
    obtain ⟨x, hx1, hx2⟩ := hsurj y hy
    exact ⟨x, hx1, by rw [hexp_apply x hx1]; exact hx2⟩

end Commons.Analysis.Nonarchimedean