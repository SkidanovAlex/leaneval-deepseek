import Mathlib
import Submission.Work.NumberTheory.Chen.ri_layer_beta2
import Submission.Work.NumberTheory.Chen.VsieveOdd_mul_log_le
import Submission.Commons.NumberTheory.Mertens.prod_one_sub_inv_prime_asymptotic
import Submission.Commons.Analysis.Normed.tailProduct_norm_sub_one_le

namespace Work.NumberTheory.Chen.APSwitchUpper

open Finset
open scoped BigOperators

noncomputable section

/-!
# The sharp logarithmic ratio bound for the odd Mertens product `Vsieve`

`Vsieve Y = ∏_{3 ≤ p < Y} (1 - 1/(p-1))` is the odd Mertens product of the linear sieve.
By Mertens' third theorem together with the twin-prime constant,
`Vsieve Y · log Y → L = 2·e^{-γ}·∏_{p odd}(1 - 1/(p-1)²) ≈ 0.7413`.

Here we prove that this convergence is faster than *any* power of the logarithm:
for every `A > 0` and all `Y₀ ≤ u ≤ Z`,

`|Vsieve u · log u - Vsieve Z · log Z| ≤ c · (Vsieve Z · log Z) / (log u)^A`.

The proof combines

* the sharp two-sided Mertens estimate with arbitrary log-power error
  (`Mertens.prod_one_sub_inv_prime_asymptotic`),
* the elementary tail bound `∑_{n < p} 1/(p-1)² ≤ 1/(n-1)` for the twin factor
  (`TP_tail_le` below),
* the fact that `Vsieve Y · log Y` is bounded below by a positive constant
  (`Vsieve_bounds`),

and the elementary conversions `log (n+1) ≤ 2 log n` and `1/n ≤ A^A/(log n)^A`.
-/

/-! ## 0. `Commons.NumberTheory.Chen.Vsieve` is the odd sieve product -/

/-- `Vsieve Y = ∏_{3 ≤ p < Y} (1 - 1/(p-1))` agrees with the `primesLE`-indexed
product `ChenEight.VsieveOdd`. -/
lemma Vsieve_eq_VsieveOdd (Y : ℕ) :
    Commons.NumberTheory.Chen.Vsieve Y = Commons.NumberTheory.Chen.ChenEight.VsieveOdd Y := by
  cases Y with
  | zero =>
    simp [Commons.NumberTheory.Chen.Vsieve, Commons.NumberTheory.Chen.oddPrimesLt,
      Commons.NumberTheory.Chen.ChenEight.VsieveOdd, Commons.NumberTheory.Chen.ChenEight.oddLt]
  | succ n =>
    rw [Commons.NumberTheory.Chen.Vsieve_eq_VLE, Nat.add_sub_cancel,
      Commons.NumberTheory.Chen.ChenEight.VsieveOdd_primesLE]
    rfl

/-! ## 1. The Mertens product converges faster than any power of `log` -/

/-- The Mertens product `MP n = ∏_{p ≤ n}(1 - 1/p)` approaches its limit at a rate
faster than `(log n)^{-A}` for every `A > 0`. -/
theorem MP_mul_log_rate :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 < A → ∃ D : ℝ, 0 < D ∧
      ∀ n : ℕ, 2 ≤ n → |MP n * Real.log (n : ℝ) - C| ≤ D / (Real.log (n : ℝ)) ^ A := by
  obtain ⟨C, hCpos, hC⟩ := Commons.NumberTheory.Mertens.prod_one_sub_inv_prime_asymptotic
  refine ⟨C, hCpos, fun A hA => ?_⟩
  obtain ⟨D, hDpos, hD⟩ := hC A hA
  refine ⟨D, hDpos, fun n hn => ?_⟩
  have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h := hD (n : ℝ) h2
  rw [Nat.floor_natCast] at h
  simpa only [MP, one_div] using h

/-! ## 2. Elementary logarithmic estimates -/

/-- `log (n+1) - log n ≤ 1/n` for `n ≥ 1`. -/
lemma log_succ_sub_log_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 : Real.log (((n : ℝ) + 1) / (n : ℝ)) ≤ ((n : ℝ) + 1) / (n : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log (((n : ℝ) + 1) / (n : ℝ)) =
      Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) :=
    Real.log_div (by positivity) (by positivity)
  have h3 : ((n : ℝ) + 1) / (n : ℝ) - 1 = 1 / (n : ℝ) := by
    field_simp
    ring
  linarith [h1, h2, h3]

/-- `log (n+1) ≤ 2 log n` for `n ≥ 3`. -/
lemma log_succ_le_two_mul_log (n : ℕ) (hn : 3 ≤ n) :
    Real.log ((n : ℝ) + 1) ≤ 2 * Real.log (n : ℝ) := by
  have hlog1 : (1 : ℝ) ≤ Real.log (n : ℝ) := by
    have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_d9]
    exact le_trans hlog3 (Real.log_le_log (by norm_num) h3)
  have hstep := log_succ_sub_log_le n (by omega)
  have hinv : 1 / (n : ℝ) ≤ Real.log (n : ℝ) := by
    have hle1 : 1 / (n : ℝ) ≤ 1 := by
      rw [div_le_one (by exact_mod_cast (by omega : 0 < n))]
      exact_mod_cast (by omega : 1 ≤ n)
    linarith
  linarith [hstep, hinv]

/-- `1/(log n)^A ≤ 2^A/(log (n+1))^A` for `A > 0`, `n ≥ 3`. -/
lemma inv_log_pow_le_two_pow {A : ℝ} (hA : 0 < A) {n : ℕ} (hn : 3 ≤ n) :
    1 / (Real.log (n : ℝ)) ^ A ≤ 2 ^ A / (Real.log ((n : ℝ) + 1)) ^ A := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hlogpos' : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by linarith)
  have hle := log_succ_le_two_mul_log n hn
  have hpow : (Real.log ((n : ℝ) + 1)) ^ A ≤ (2 * Real.log (n : ℝ)) ^ A :=
    Real.rpow_le_rpow (le_of_lt hlogpos') hle (le_of_lt hA)
  have hpow2 : (2 * Real.log (n : ℝ)) ^ A = 2 ^ A * (Real.log (n : ℝ)) ^ A :=
    Real.mul_rpow (by norm_num) (le_of_lt hlogpos)
  rw [hpow2] at hpow
  rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hlogpos A) (Real.rpow_pos_of_pos hlogpos' A)]
  linarith [hpow]

/-- `1/n ≤ A^A/(log n)^A` for `A > 0`, `n ≥ 2`. -/
lemma inv_nat_le_log_pow {A : ℝ} (hA : 0 < A) {n : ℕ} (hn : 2 ≤ n) :
    1 / (n : ℝ) ≤ A ^ A / (Real.log (n : ℝ)) ^ A := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hε : 0 < 1 / A := by positivity
  have h1 : Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / A) / (1 / A) :=
    Real.log_le_rpow_div (le_of_lt hx0) hε
  have h2 : (n : ℝ) ^ (1 / A) / (1 / A) = A * (n : ℝ) ^ (1 / A) := by
    field_simp
  have h3 : Real.log (n : ℝ) ≤ A * (n : ℝ) ^ (1 / A) := by
    rw [← h2]; exact h1
  have h4 : (Real.log (n : ℝ)) ^ A ≤ (A * (n : ℝ) ^ (1 / A)) ^ A :=
    Real.rpow_le_rpow (le_of_lt hlogpos) h3 (le_of_lt hA)
  have h5 : (A * (n : ℝ) ^ (1 / A)) ^ A = A ^ A * (n : ℝ) := by
    rw [Real.mul_rpow (le_of_lt hA) (Real.rpow_nonneg (le_of_lt hx0) _)]
    have h6 : ((n : ℝ) ^ (1 / A)) ^ A = (n : ℝ) := by
      rw [← Real.rpow_mul (le_of_lt hx0) (1 / A) A, one_div_mul_cancel (ne_of_gt hA),
        Real.rpow_one]
    rw [h6]
  have hpower := h5 ▸ h4
  rw [div_le_div_iff₀ hx0 (Real.rpow_pos_of_pos hlogpos A)]
  linarith [hpower]

/-! ## 3. The tail of the twin product -/

/-- `1 - ∑ t_i ≤ ∏ (1 - t_i)` for nonnegative `t_i` with total sum at most `1`. -/
private lemma one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (t : ι → ℝ) :
    (∀ i ∈ s, 0 ≤ t i) → (∑ i ∈ s, t i ≤ 1) →
      1 - ∑ i ∈ s, t i ≤ ∏ i ∈ s, (1 - t i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro _ _
    simp
  · intro a s' ha ih h0 hsum
    have h0a : 0 ≤ t a := h0 a (by simp)
    have h0s' : ∀ i ∈ s', 0 ≤ t i := fun i hi => h0 i (by simp [hi])
    have hsum_nonneg : 0 ≤ ∑ i ∈ s', t i := Finset.sum_nonneg h0s'
    have hsuma : t a + ∑ i ∈ s', t i ≤ 1 := by
      simpa [Finset.sum_insert ha] using hsum
    have hta1 : t a ≤ 1 := by linarith
    have hs'sum_le_one : ∑ i ∈ s', t i ≤ 1 := by linarith
    have hprod : 1 - ∑ i ∈ s', t i ≤ ∏ i ∈ s', (1 - t i) := ih h0s' hs'sum_le_one
    have h1ma : 0 ≤ 1 - t a := by linarith
    calc 1 - ∑ i ∈ insert a s', t i = 1 - (t a + ∑ i ∈ s', t i) := by
          rw [Finset.sum_insert ha]
      _ ≤ (1 - t a) * (1 - ∑ i ∈ s', t i) := by nlinarith
      _ ≤ (1 - t a) * ∏ i ∈ s', (1 - t i) := mul_le_mul_of_nonneg_left hprod h1ma
      _ = ∏ i ∈ insert a s', (1 - t i) := by rw [Finset.prod_insert ha]

/-- **Tail rate of the twin product.**  For `2 ≤ n ≤ m` the twin product
`TP n = ∏_{3 ≤ p ≤ n}(1 - 1/(p-1)²)` drops by at most `1/(n-1)`. -/
lemma TP_tail_le {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) :
    TP n - TP m ≤ 1 / ((n : ℝ) - 1) := by
  classical
  set S : Finset ℕ :=
    ((Nat.primesLE m).filter (fun p : ℕ => p ≠ 2)).filter (fun p => n < p) with hS
  have hmemS : ∀ p ∈ S, n < p ∧ p ≤ m ∧ p ≠ 2 := by
    intro p hp
    rw [hS, Finset.mem_filter, Finset.mem_filter, Nat.mem_primesLE] at hp
    exact ⟨hp.2, hp.1.1.1, hp.1.2⟩
  -- splitting `TP m = TP n · ∏_{p ∈ S}(1 - 1/(p-1)²)`
  have hsplit : TP m = (∏ p ∈ S, (1 - (((p : ℝ) - 1) ^ 2)⁻¹)) * TP n := by
    have h := Finset.prod_filter_mul_prod_filter_not
      (s := (Nat.primesLE m).filter (fun p : ℕ => p ≠ 2)) (p := fun p : ℕ => n < p)
      (f := fun p : ℕ => 1 - (((p : ℝ) - 1) ^ 2)⁻¹)
    rw [← hS] at h
    rw [TP, ← h]
    congr 1
    congr 1
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, not_lt]
    constructor
    · rintro ⟨⟨⟨hpm, hpp⟩, hp2⟩, hpn⟩
      exact ⟨⟨hpn, hpp⟩, hp2⟩
    · rintro ⟨⟨hpn, hpp⟩, hp2⟩
      exact ⟨⟨⟨le_trans hpn hnm, hpp⟩, hp2⟩, hpn⟩
  -- the tail sum is at most `1/(n-1)`
  have hinj : Set.InjOn (fun p : ℕ => p - 1) (S : Set ℕ) := by
    intro p hp q hq hpq
    have hp' : n < p := (hmemS p (Finset.mem_coe.mp hp)).1
    have hq' : n < q := (hmemS q (Finset.mem_coe.mp hq)).1
    simp only at hpq
    omega
  have hcast : ∀ p ∈ S, (((p : ℝ) - 1) ^ 2)⁻¹ = ((((p - 1 : ℕ)) : ℝ) ^ 2)⁻¹ := by
    intro p hp
    have hp1 : 1 ≤ p := by have := (hmemS p hp).1; omega
    rw [Nat.cast_sub hp1]
    norm_num
  have hsum_eq : (∑ p ∈ S, (((p : ℝ) - 1) ^ 2)⁻¹)
      = ∑ j ∈ S.image (fun p : ℕ => p - 1), (((j : ℝ)) ^ 2)⁻¹ := by
    rw [Finset.sum_congr rfl hcast]
    exact (Finset.sum_image (s := S) (f := fun j : ℕ => (((j : ℝ)) ^ 2)⁻¹)
      (g := fun p : ℕ => p - 1) hinj).symm
  have hsum_le : (∑ p ∈ S, (((p : ℝ) - 1) ^ 2)⁻¹) ≤ 1 / ((n : ℝ) - 1) := by
    rw [hsum_eq]
    have htail : ∀ j ∈ S.image (fun p : ℕ => p - 1), n - 1 < j := by
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨p, hp, rfl⟩
      have hnp : n < p := (hmemS p hp).1
      omega
    have h := Commons.Analysis.Normed.sum_inv_sq_le_inv
      (S := S.image (fun p : ℕ => p - 1)) (w := n - 1) (by omega) htail
    have hw : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    rw [hw] at h
    simpa [one_div] using h
  -- conclude
  have hsum1 : (∑ p ∈ S, (((p : ℝ) - 1) ^ 2)⁻¹) ≤ 1 := by
    have hpos : (0 : ℝ) < (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hle : 1 / ((n : ℝ) - 1) ≤ 1 := by
      rw [div_le_one hpos]
      have : (1 : ℝ) ≤ (n : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      linarith
    linarith [hsum_le]
  have hprod_ge : 1 - (∑ p ∈ S, (((p : ℝ) - 1) ^ 2)⁻¹) ≤
      ∏ p ∈ S, (1 - (((p : ℝ) - 1) ^ 2)⁻¹) :=
    one_sub_sum_le_prod S _ (fun p hp => by positivity) hsum1
  have hTPn1 : TP n ≤ 1 := TP_le_one n
  have hfac : TP n - TP m = TP n * (1 - ∏ p ∈ S, (1 - (((p : ℝ) - 1) ^ 2)⁻¹)) := by
    rw [hsplit]; ring
  rw [hfac]
  have hone : 1 - ∏ p ∈ S, (1 - (((p : ℝ) - 1) ^ 2)⁻¹) ≤ (∑ p ∈ S, (((p : ℝ) - 1) ^ 2)⁻¹) := by
    linarith [hprod_ge]
  have hPle1 : ∏ p ∈ S, (1 - (((p : ℝ) - 1) ^ 2)⁻¹) ≤ 1 := by
    refine Finset.prod_le_one₀ (fun p hp => ?_) (fun p hp => ?_)
    · have hp3 : 3 ≤ p := by have h := (hmemS p hp).1; omega
      have hp3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
      have h1 : (1 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
      have h2 : (((p : ℝ) - 1) ^ 2)⁻¹ ≤ 1 := by
        have h3 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) h1
        simpa [one_div] using h3
      linarith
    · have hnn : 0 ≤ (((p : ℝ) - 1) ^ 2)⁻¹ := by positivity
      linarith
  have hnonneg : 0 ≤ 1 - ∏ p ∈ S, (1 - (((p : ℝ) - 1) ^ 2)⁻¹) := by linarith
  calc TP n * (1 - ∏ p ∈ S, (1 - (((p : ℝ) - 1) ^ 2)⁻¹))
      ≤ 1 * (∑ p ∈ S, (((p : ℝ) - 1) ^ 2)⁻¹) :=
        mul_le_mul hTPn1 hone hnonneg (by norm_num)
    _ ≤ 1 * (1 / ((n : ℝ) - 1)) := by
        exact mul_le_mul_of_nonneg_left hsum_le (by norm_num)
    _ = 1 / ((n : ℝ) - 1) := by ring

/-! ## 4. The two-scale rate estimate -/

/-- **The two-scale rate estimate.**  For every `A > 0` the difference
`Vsieve u · log u - Vsieve Z · log Z` is `O((log u)^{-A})`, uniformly over `u ≤ Z`. -/
theorem Vsieve_mul_log_diff_le (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ u Z : ℕ, N₀ ≤ u → u ≤ Z →
      |Commons.NumberTheory.Chen.Vsieve u * Real.log (u : ℝ)
        - Commons.NumberTheory.Chen.Vsieve Z * Real.log (Z : ℝ)|
        ≤ K / (Real.log (u : ℝ)) ^ A := by
  obtain ⟨CM, hCMpos, hrate⟩ := MP_mul_log_rate
  obtain ⟨D, hDpos, hD⟩ := hrate A hA
  have hAApos : 0 < A ^ A := Real.rpow_pos_of_pos hA A
  have h2Apos : 0 < (2 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) A
  set K₁ : ℝ := (D + A ^ A) * 2 ^ A with hK1
  set K₂ : ℝ := 2 * A ^ A with hK2
  set K₃ : ℝ := CM + K₁ with hK3
  have hK1pos : 0 < K₁ := by
    rw [hK1]
    exact mul_pos (by linarith) h2Apos
  have hK2pos : 0 < K₂ := by rw [hK2]; linarith
  have hK3pos : 0 < K₃ := by rw [hK3]; linarith
  refine ⟨2 * (2 * K₁ + K₃ * K₂), by nlinarith, 10, ?_⟩
  intro u Z hu huZ
  have hu4 : 4 ≤ u := by omega
  have hu3 : 3 ≤ u := by omega
  have hZ3 : 3 ≤ Z := by omega
  set n : ℕ := u - 1 with hn
  set m : ℕ := Z - 1 with hm
  have hun : u = n + 1 := by omega
  have hZm : Z = m + 1 := by omega
  have hn2 : 2 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hm2 : 2 ≤ m := by omega
  have hnm : n ≤ m := by omega
  have hnu : n ≤ u := by omega
  have hmZ : m ≤ Z := by omega
  have hcastu : (u : ℝ) = (n : ℝ) + 1 := by rw [hun]; push_cast; ring
  have hcastZ : (Z : ℝ) = (m : ℝ) + 1 := by rw [hZm]; push_cast; ring
  have hlogu_pos : 0 < Real.log (u : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < u))
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlogm_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hlogu_ge1 : 1 ≤ Real.log (u : ℝ) := by
    have hu10 : (10 : ℝ) ≤ (u : ℝ) := by exact_mod_cast (by omega : 10 ≤ u)
    have h1 : Real.log 10 ≤ Real.log (u : ℝ) := Real.log_le_log (by norm_num) hu10
    have h2 : (1 : ℝ) ≤ Real.log 10 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_d9]
    linarith
  have hlogun : Real.log (n : ℝ) ≤ Real.log (u : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hnu)
  have hlogmZ : Real.log (m : ℝ) ≤ Real.log (Z : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hmZ)
  -- factorisations
  have hfu : Commons.NumberTheory.Chen.Vsieve u = 2 * MP n * TP n := by
    rw [Vsieve_eq_VsieveOdd, hun, VsieveOdd_eq_two_MP_TP (n + 1) (by omega : 3 ≤ n + 1)]
    simp
  have hfZ : Commons.NumberTheory.Chen.Vsieve Z = 2 * MP m * TP m := by
    rw [Vsieve_eq_VsieveOdd, hZm, VsieveOdd_eq_two_MP_TP (m + 1) (by omega : 3 ≤ m + 1)]
    simp
  -- conversion helpers
  have hconv : ∀ D' : ℝ, 0 ≤ D' →
      D' / (Real.log (n : ℝ)) ^ A ≤ D' * 2 ^ A / (Real.log (u : ℝ)) ^ A := by
    intro D' hD'
    have h := inv_log_pow_le_two_pow (A := A) hA hn3
    rw [hcastu]
    have h' : D' * (1 / (Real.log (n : ℝ)) ^ A) ≤ D' * (2 ^ A / (Real.log ((n : ℝ) + 1)) ^ A) :=
      mul_le_mul_of_nonneg_left h hD'
    calc D' / (Real.log (n : ℝ)) ^ A = D' * (1 / (Real.log (n : ℝ)) ^ A) := by ring
      _ ≤ D' * (2 ^ A / (Real.log ((n : ℝ) + 1)) ^ A) := h'
      _ = D' * 2 ^ A / (Real.log ((n : ℝ) + 1)) ^ A := by ring
  have hconv_m : ∀ D' : ℝ, 0 ≤ D' →
      D' / (Real.log (m : ℝ)) ^ A ≤ D' * 2 ^ A / (Real.log (u : ℝ)) ^ A := by
    intro D' hD'
    have h1 : D' / (Real.log (m : ℝ)) ^ A ≤ D' / (Real.log (n : ℝ)) ^ A := by
      rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hlogm_pos A) (Real.rpow_pos_of_pos hlogn_pos A)]
      have h2 : (Real.log (n : ℝ)) ^ A ≤ (Real.log (m : ℝ)) ^ A :=
        Real.rpow_le_rpow (le_of_lt hlogn_pos)
          (Real.log_le_log (by positivity) (by exact_mod_cast hnm)) (le_of_lt hA)
      nlinarith [h2, hD']
    linarith [h1, hconv D' hD']
  -- rate for `MP n * log u`
  have hPU : |MP n * Real.log (u : ℝ) - CM| ≤ K₁ / (Real.log (u : ℝ)) ^ A := by
    have hr : |MP n * Real.log (n : ℝ) - CM| ≤ D / (Real.log (n : ℝ)) ^ A := hD n hn2
    have hshift : |MP n * Real.log (u : ℝ) - MP n * Real.log (n : ℝ)| ≤ 1 / (n : ℝ) := by
      have heq : MP n * Real.log (u : ℝ) - MP n * Real.log (n : ℝ)
          = MP n * (Real.log (u : ℝ) - Real.log (n : ℝ)) := by ring
      rw [heq, abs_mul, abs_of_nonneg (MP_nonneg n)]
      have hnn : 0 ≤ Real.log (u : ℝ) - Real.log (n : ℝ) := by linarith
      rw [abs_of_nonneg hnn]
      have hlog : Real.log (u : ℝ) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
        rw [hcastu]
        exact log_succ_sub_log_le n (by omega)
      have hle1 : MP n ≤ 1 := MP_le_one n
      calc MP n * (Real.log (u : ℝ) - Real.log (n : ℝ))
          ≤ 1 * (1 / (n : ℝ)) := mul_le_mul hle1 hlog hnn (by norm_num)
        _ = 1 / (n : ℝ) := by ring
    have htri : |MP n * Real.log (u : ℝ) - CM|
        ≤ |MP n * Real.log (n : ℝ) - CM| + |MP n * Real.log (u : ℝ) - MP n * Real.log (n : ℝ)| := by
      have h := abs_add_le (MP n * Real.log (n : ℝ) - CM)
        (MP n * Real.log (u : ℝ) - MP n * Real.log (n : ℝ))
      have heq : (MP n * Real.log (n : ℝ) - CM)
          + (MP n * Real.log (u : ℝ) - MP n * Real.log (n : ℝ))
          = MP n * Real.log (u : ℝ) - CM := by ring
      rwa [heq] at h
    have h1 : D / (Real.log (n : ℝ)) ^ A ≤ D * 2 ^ A / (Real.log (u : ℝ)) ^ A :=
      hconv D hDpos.le
    have h2 : 1 / (n : ℝ) ≤ A ^ A / (Real.log (n : ℝ)) ^ A := inv_nat_le_log_pow hA hn2
    have h3 : A ^ A / (Real.log (n : ℝ)) ^ A ≤ A ^ A * 2 ^ A / (Real.log (u : ℝ)) ^ A :=
      hconv (A ^ A) hAApos.le
    calc |MP n * Real.log (u : ℝ) - CM|
        ≤ D / (Real.log (n : ℝ)) ^ A + 1 / (n : ℝ) := by linarith [htri, hr, hshift]
      _ ≤ (D + A ^ A) * 2 ^ A / (Real.log (u : ℝ)) ^ A := by
          have hsum : D / (Real.log (n : ℝ)) ^ A + 1 / (n : ℝ)
              ≤ D * 2 ^ A / (Real.log (u : ℝ)) ^ A + A ^ A * 2 ^ A / (Real.log (u : ℝ)) ^ A := by
            linarith [h1, h2, h3]
          have heq : D * 2 ^ A / (Real.log (u : ℝ)) ^ A + A ^ A * 2 ^ A / (Real.log (u : ℝ)) ^ A
              = (D + A ^ A) * 2 ^ A / (Real.log (u : ℝ)) ^ A := by ring
          linarith [hsum, heq]
      _ = K₁ / (Real.log (u : ℝ)) ^ A := by rw [hK1]
  -- rate for `MP m * log Z`
  have hPZ : |MP m * Real.log (Z : ℝ) - CM| ≤ K₁ / (Real.log (u : ℝ)) ^ A := by
    have hr : |MP m * Real.log (m : ℝ) - CM| ≤ D / (Real.log (m : ℝ)) ^ A := hD m hm2
    have hshift : |MP m * Real.log (Z : ℝ) - MP m * Real.log (m : ℝ)| ≤ 1 / (m : ℝ) := by
      have heq : MP m * Real.log (Z : ℝ) - MP m * Real.log (m : ℝ)
          = MP m * (Real.log (Z : ℝ) - Real.log (m : ℝ)) := by ring
      rw [heq, abs_mul, abs_of_nonneg (MP_nonneg m)]
      have hnn : 0 ≤ Real.log (Z : ℝ) - Real.log (m : ℝ) := by linarith
      rw [abs_of_nonneg hnn]
      have hlog : Real.log (Z : ℝ) - Real.log (m : ℝ) ≤ 1 / (m : ℝ) := by
        rw [hcastZ]
        exact log_succ_sub_log_le m (by omega)
      have hle1 : MP m ≤ 1 := MP_le_one m
      calc MP m * (Real.log (Z : ℝ) - Real.log (m : ℝ))
          ≤ 1 * (1 / (m : ℝ)) := mul_le_mul hle1 hlog hnn (by norm_num)
        _ = 1 / (m : ℝ) := by ring
    have htri : |MP m * Real.log (Z : ℝ) - CM|
        ≤ |MP m * Real.log (m : ℝ) - CM| + |MP m * Real.log (Z : ℝ) - MP m * Real.log (m : ℝ)| := by
      have h := abs_add_le (MP m * Real.log (m : ℝ) - CM)
        (MP m * Real.log (Z : ℝ) - MP m * Real.log (m : ℝ))
      have heq : (MP m * Real.log (m : ℝ) - CM)
          + (MP m * Real.log (Z : ℝ) - MP m * Real.log (m : ℝ))
          = MP m * Real.log (Z : ℝ) - CM := by ring
      rwa [heq] at h
    have h1 : D / (Real.log (m : ℝ)) ^ A ≤ D * 2 ^ A / (Real.log (u : ℝ)) ^ A :=
      hconv_m D hDpos.le
    have h2 : 1 / (m : ℝ) ≤ 1 / (n : ℝ) := by
      have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (m:ℝ)) (by positivity : (0:ℝ) < (n:ℝ))]
      linarith
    have h2' : 1 / (n : ℝ) ≤ A ^ A / (Real.log (n : ℝ)) ^ A := inv_nat_le_log_pow hA hn2
    have h3 : A ^ A / (Real.log (n : ℝ)) ^ A ≤ A ^ A * 2 ^ A / (Real.log (u : ℝ)) ^ A :=
      hconv (A ^ A) hAApos.le
    calc |MP m * Real.log (Z : ℝ) - CM|
        ≤ D / (Real.log (m : ℝ)) ^ A + 1 / (m : ℝ) := by linarith [htri, hr, hshift]
      _ ≤ (D + A ^ A) * 2 ^ A / (Real.log (u : ℝ)) ^ A := by
          have hsum : D / (Real.log (m : ℝ)) ^ A + 1 / (m : ℝ)
              ≤ D * 2 ^ A / (Real.log (u : ℝ)) ^ A + A ^ A * 2 ^ A / (Real.log (u : ℝ)) ^ A := by
            linarith [h1, h2, h2', h3]
          have heq : D * 2 ^ A / (Real.log (u : ℝ)) ^ A + A ^ A * 2 ^ A / (Real.log (u : ℝ)) ^ A
              = (D + A ^ A) * 2 ^ A / (Real.log (u : ℝ)) ^ A := by ring
          linarith [hsum, heq]
      _ = K₁ / (Real.log (u : ℝ)) ^ A := by rw [hK1]
  -- `|MP m log Z| ≤ K₃`
  have hPZabs : |MP m * Real.log (Z : ℝ)| ≤ K₃ := by
    have htri : |MP m * Real.log (Z : ℝ)| ≤ |MP m * Real.log (Z : ℝ) - CM| + |CM| := by
      have h := abs_add_le (MP m * Real.log (Z : ℝ) - CM) CM
      have heq : (MP m * Real.log (Z : ℝ) - CM) + CM = MP m * Real.log (Z : ℝ) := by ring
      rwa [heq] at h
    have habs : |CM| = CM := abs_of_nonneg hCMpos.le
    have hone : 1 ≤ (Real.log (u : ℝ)) ^ A := by
      have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hlogu_ge1 (le_of_lt hA)
      rwa [Real.one_rpow] at h
    have hK1le : K₁ / (Real.log (u : ℝ)) ^ A ≤ K₁ := by
      have hinv : 1 / (Real.log (u : ℝ)) ^ A ≤ 1 := by
        rw [div_le_one (Real.rpow_pos_of_pos hlogu_pos A)]
        exact hone
      calc K₁ / (Real.log (u : ℝ)) ^ A = K₁ * (1 / (Real.log (u : ℝ)) ^ A) := by ring
        _ ≤ K₁ * 1 := mul_le_mul_of_nonneg_left hinv hK1pos.le
        _ = K₁ := by ring
    rw [habs] at htri
    rw [hK3]
    linarith [htri, hPZ, hK1le]
  -- tail rate of the twin product
  have hTPdiff : |TP n - TP m| ≤ K₂ / (Real.log (u : ℝ)) ^ A := by
    have hle : TP m ≤ TP n := TP_mono hnm
    have habs : |TP n - TP m| = TP n - TP m := abs_of_nonneg (by linarith)
    rw [habs]
    have htail : TP n - TP m ≤ 1 / ((n : ℝ) - 1) := TP_tail_le hn2 hnm
    have hcast : ((n : ℝ) - 1) = ((u : ℝ) - 2) := by rw [hcastu]; ring
    rw [hcast] at htail
    have huR : (4 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu4
    have h2 : 1 / ((u : ℝ) - 2) ≤ 2 / (u : ℝ) := by
      rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < (u : ℝ) - 2) (by linarith : (0 : ℝ) < (u : ℝ))]
      linarith
    have h3 : 2 / (u : ℝ) ≤ 2 * A ^ A / (Real.log (u : ℝ)) ^ A := by
      have h := inv_nat_le_log_pow (A := A) hA (n := u) (by omega)
      calc 2 / (u : ℝ) = 2 * (1 / (u : ℝ)) := by ring
        _ ≤ 2 * (A ^ A / (Real.log (u : ℝ)) ^ A) := mul_le_mul_of_nonneg_left h (by norm_num)
        _ = 2 * A ^ A / (Real.log (u : ℝ)) ^ A := by ring
    have h4 : 2 * A ^ A / (Real.log (u : ℝ)) ^ A = K₂ / (Real.log (u : ℝ)) ^ A := by rw [hK2]
    rw [← h4]
    linarith [htail, h2, h3]
  -- combine
  have hPUZ : |(MP n * Real.log (u : ℝ)) - (MP m * Real.log (Z : ℝ))|
      ≤ 2 * K₁ / (Real.log (u : ℝ)) ^ A := by
    have htri : |(MP n * Real.log (u : ℝ)) - (MP m * Real.log (Z : ℝ))|
        ≤ |MP n * Real.log (u : ℝ) - CM| + |MP m * Real.log (Z : ℝ) - CM| := by
      have h := abs_add_le (MP n * Real.log (u : ℝ) - CM) (CM - (MP m * Real.log (Z : ℝ)))
      have heq : (MP n * Real.log (u : ℝ) - CM) + (CM - (MP m * Real.log (Z : ℝ)))
          = (MP n * Real.log (u : ℝ)) - (MP m * Real.log (Z : ℝ)) := by ring
      rw [heq] at h
      have h2 : |CM - (MP m * Real.log (Z : ℝ))| = |MP m * Real.log (Z : ℝ) - CM| := abs_sub_comm _ _
      linarith [h]
    have : 2 * K₁ / (Real.log (u : ℝ)) ^ A
        = K₁ / (Real.log (u : ℝ)) ^ A + K₁ / (Real.log (u : ℝ)) ^ A := by ring
    linarith [htri, hPU, hPZ]
  have hkey : |TP n * (MP n * Real.log (u : ℝ)) - TP m * (MP m * Real.log (Z : ℝ))|
      ≤ (2 * K₁ + K₃ * K₂) / (Real.log (u : ℝ)) ^ A := by
    have hdecomp : TP n * (MP n * Real.log (u : ℝ)) - TP m * (MP m * Real.log (Z : ℝ))
        = TP n * ((MP n * Real.log (u : ℝ)) - (MP m * Real.log (Z : ℝ)))
          + (TP n - TP m) * (MP m * Real.log (Z : ℝ)) := by ring
    rw [hdecomp]
    have h1 : |TP n * ((MP n * Real.log (u : ℝ)) - (MP m * Real.log (Z : ℝ)))|
        ≤ TP n * (2 * K₁ / (Real.log (u : ℝ)) ^ A) := by
      rw [abs_mul, abs_of_nonneg (TP_nonneg n)]
      exact mul_le_mul_of_nonneg_left hPUZ (TP_nonneg n)
    have h2 : TP n * (2 * K₁ / (Real.log (u : ℝ)) ^ A) ≤ 2 * K₁ / (Real.log (u : ℝ)) ^ A := by
      have hnn : 0 ≤ 2 * K₁ / (Real.log (u : ℝ)) ^ A := by positivity
      calc TP n * (2 * K₁ / (Real.log (u : ℝ)) ^ A)
          ≤ 1 * (2 * K₁ / (Real.log (u : ℝ)) ^ A) :=
            mul_le_mul_of_nonneg_right (TP_le_one n) hnn
        _ = 2 * K₁ / (Real.log (u : ℝ)) ^ A := by ring
    have h3 : |(TP n - TP m) * (MP m * Real.log (Z : ℝ))|
        ≤ (K₂ / (Real.log (u : ℝ)) ^ A) * K₃ := by
      rw [abs_mul]
      exact mul_le_mul hTPdiff hPZabs (abs_nonneg _) (by positivity)
    have h4 : (K₂ / (Real.log (u : ℝ)) ^ A) * K₃ = K₃ * K₂ / (Real.log (u : ℝ)) ^ A := by ring
    calc |TP n * ((MP n * Real.log (u : ℝ)) - (MP m * Real.log (Z : ℝ)))
          + (TP n - TP m) * (MP m * Real.log (Z : ℝ))|
        ≤ |TP n * ((MP n * Real.log (u : ℝ)) - (MP m * Real.log (Z : ℝ)))|
          + |(TP n - TP m) * (MP m * Real.log (Z : ℝ))| := abs_add_le _ _
      _ ≤ 2 * K₁ / (Real.log (u : ℝ)) ^ A + K₃ * K₂ / (Real.log (u : ℝ)) ^ A := by
          linarith [h1, h2, h3, h4]
      _ = (2 * K₁ + K₃ * K₂) / (Real.log (u : ℝ)) ^ A := by ring
  -- put everything together
  have hfinal : |Commons.NumberTheory.Chen.Vsieve u * Real.log (u : ℝ)
      - Commons.NumberTheory.Chen.Vsieve Z * Real.log (Z : ℝ)|
      ≤ 2 * (2 * K₁ + K₃ * K₂) / (Real.log (u : ℝ)) ^ A := by
    rw [hfu, hfZ]
    have heq : 2 * MP n * TP n * Real.log (u : ℝ) - 2 * MP m * TP m * Real.log (Z : ℝ)
        = 2 * (TP n * (MP n * Real.log (u : ℝ)) - TP m * (MP m * Real.log (Z : ℝ))) := by ring
    rw [heq, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc 2 * |TP n * (MP n * Real.log (u : ℝ)) - TP m * (MP m * Real.log (Z : ℝ))|
        ≤ 2 * ((2 * K₁ + K₃ * K₂) / (Real.log (u : ℝ)) ^ A) :=
          mul_le_mul_of_nonneg_left hkey (by norm_num)
      _ = 2 * (2 * K₁ + K₃ * K₂) / (Real.log (u : ℝ)) ^ A := by ring
  exact hfinal

/-! ## 5. The target -/

theorem Vsieve_log_ratio_sharp (A : ℝ) (hA : 0 < A) :
    ∃ c : ℝ, 0 < c ∧ ∃ Y₀ : ℕ, ∀ u Z : ℕ, Y₀ ≤ u → u ≤ Z →
      |Commons.NumberTheory.Chen.Vsieve u * Real.log (u : ℝ)
        - Commons.NumberTheory.Chen.Vsieve Z * Real.log (Z : ℝ)|
        ≤ c * (Commons.NumberTheory.Chen.Vsieve Z * Real.log (Z:ℝ)) / (Real.log (u : ℝ))^A := by
  obtain ⟨K, hKpos, N₀, hK⟩ := Vsieve_mul_log_diff_le A hA
  obtain ⟨cv, Cv, hcvpos, _hCvpos, hVb⟩ := Commons.NumberTheory.Chen.Vsieve_bounds
  refine ⟨K / cv, div_pos hKpos hcvpos, max N₀ 4, fun u Z hu huZ => ?_⟩
  have hN : N₀ ≤ u := le_trans (le_max_left _ _) hu
  have hu4 : 4 ≤ u := le_trans (le_max_right _ _) hu
  have hZ4 : 4 ≤ Z := le_trans hu4 huZ
  have h1 : |Commons.NumberTheory.Chen.Vsieve u * Real.log (u : ℝ)
      - Commons.NumberTheory.Chen.Vsieve Z * Real.log (Z : ℝ)|
      ≤ K / (Real.log (u : ℝ)) ^ A := hK u Z hN huZ
  have hlogZ : 0 < Real.log (Z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Z))
  have hlow : cv ≤ Commons.NumberTheory.Chen.Vsieve Z * Real.log (Z : ℝ) := by
    have h := (hVb Z hZ4).1
    rw [div_le_iff₀ hlogZ] at h
    linarith
  have h2 : K / (Real.log (u : ℝ)) ^ A
      ≤ (K / cv) * (Commons.NumberTheory.Chen.Vsieve Z * Real.log (Z : ℝ)) / (Real.log (u : ℝ)) ^ A := by
    have hx : 0 < (Real.log (u : ℝ)) ^ A :=
      Real.rpow_pos_of_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < u))) A
    have hKcv : 0 ≤ K / cv := div_nonneg hKpos.le hcvpos.le
    have hKle : K ≤ (K / cv) * (Commons.NumberTheory.Chen.Vsieve Z * Real.log (Z : ℝ)) := by
      have h1 : (K / cv) * cv ≤ (K / cv) * (Commons.NumberTheory.Chen.Vsieve Z * Real.log (Z : ℝ)) :=
        mul_le_mul_of_nonneg_left hlow hKcv
      have h2 : (K / cv) * cv = K := by
        field_simp
      linarith [h1, h2]
    rw [div_le_div_iff₀ hx hx]
    exact mul_le_mul_of_nonneg_right hKle hx.le
  linarith [h1, h2]

end

end Work.NumberTheory.Chen.APSwitchUpper
