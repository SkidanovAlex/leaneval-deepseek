import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.ulcm_le_four_pow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! # `lcm(1,…,k) ≤ 3^k`  (Hanson's theorem)

This file proves Hanson's bound `lcm(1,2,…,k) ≤ 3^k` for all `k`, equivalently
`ψ(k) ≤ k log 3` for the Chebyshev function `ψ`.

The proof follows D. Hanson, *On the product of the primes*, Canad. Math. Bull. **15** (1972),
33–37, with completely elementary estimates:

* Let `syl` be Sylvester's sequence (`syl 0 = 2`, `syl (n+1) = syl n * (syl n - 1) + 1`), so that
  `syl (n+1) - 1 = syl 0 * ⋯ * syl n`.
* For `n ≥ 1` put `sylBlocks n = ∏_{i ≤ n} (n / syl i)!` and `C(n) = n! / sylBlocks n`.
  Hanson's key lemma is `lcm(1,…,n) ∣ C(n)`; it follows from Legendre's formula and the
  "floor lemma" `⌊x⌋ - ∑_{i} ⌊x / syl i⌋ ≥ 1` (`x ≥ 1`), which is proved from the Egyptian
  fraction identity `∑_{i<k} 1/syl i = 1 - 1/(syl k - 1)`.
* `log C(n) ≤ log n + log (n+1) + 1 + n * Lw n` where `Lw n = ∑_{syl i ≤ n} log (syl i)/syl i`
  (from `log n! ≤ n log n - n + log (n+1) + 1` and `log m! ≥ m log m - m + 1`).
* `Lw n ≤ 1.0783` for `1024 ≤ n < 1807` and `Lw n ≤ 1.0826` always, while `log 3 ≥ 1.0986`;
  this gives `C(n) ≤ 3^n` for `n ≥ 1024`.  The finitely many `n < 1024` are checked
  by computation.
-/

namespace Work.BW

open Finset

/-- Sylvester's sequence `2, 3, 7, 43, 1807, …`. -/
def syl : ℕ → ℕ
  | 0 => 2
  | n + 1 => syl n * (syl n - 1) + 1

@[simp] lemma syl_zero : syl 0 = 2 := rfl
@[simp] lemma syl_succ (n : ℕ) : syl (n + 1) = syl n * (syl n - 1) + 1 := rfl

lemma syl_two_le : ∀ n : ℕ, 2 ≤ syl n := by
  intro n
  induction n with
  | zero => decide
  | succ n ih =>
      rw [syl_succ]
      have h1 : 1 ≤ syl n - 1 := by omega
      have h2 : 1 ≤ syl n * (syl n - 1) := by
        have : 0 < syl n * (syl n - 1) := Nat.mul_pos (by omega) (by omega)
        omega
      omega

lemma syl_mono : Monotone syl := by
  apply monotone_nat_of_le_succ
  intro n
  rw [syl_succ]
  have h1 : 1 ≤ syl n - 1 := by have := syl_two_le n; omega
  have h2 : syl n ≤ syl n * (syl n - 1) := by
    calc syl n = syl n * 1 := (mul_one _).symm
      _ ≤ syl n * (syl n - 1) := Nat.mul_le_mul_left _ h1
  omega

lemma syl_ge (n : ℕ) : n + 2 ≤ syl n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [syl_succ]
      have h3 : syl n ≤ syl n * (syl n - 1) := by
        have h1 : 1 ≤ syl n - 1 := by have := syl_two_le n; omega
        calc syl n = syl n * 1 := (mul_one _).symm
          _ ≤ syl n * (syl n - 1) := Nat.mul_le_mul_left _ h1
      omega

lemma syl_lt_of_lt {i k : ℕ} (h : i < k) : syl i < syl k := by
  have hstep : syl i < syl (i + 1) := by
    rw [syl_succ]
    have h1 : 1 ≤ syl i - 1 := by have := syl_two_le i; omega
    have h2 : syl i ≤ syl i * (syl i - 1) := by
      calc syl i = syl i * 1 := (mul_one _).symm
        _ ≤ syl i * (syl i - 1) := Nat.mul_le_mul_left _ h1
    omega
  exact lt_of_lt_of_le hstep (syl_mono (by omega))

/-- The product of the first `k` Sylvester numbers is `syl k - 1`. -/
lemma syl_prod (k : ℕ) : (∏ i ∈ Finset.range k, syl i) = syl k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.prod_range_succ, ih, syl_succ]
      have h := syl_two_le k
      have : (syl k - 1) * syl k = syl k * (syl k - 1) := mul_comm _ _
      omega

/-- `syl i` divides `syl k - 1` for `i < k`. -/
lemma syl_dvd_pred {i k : ℕ} (h : i < k) : syl i ∣ syl k - 1 := by
  rw [← syl_prod k]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr h)

/-- `syl k ≡ 1` mod `syl i` for `i < k`. -/
lemma syl_mod {i k : ℕ} (h : i < k) : syl k % syl i = 1 := by
  have hd := syl_dvd_pred h
  obtain ⟨q, hq⟩ := hd
  have h2 : 1 < syl i := by have := syl_two_le i; omega
  have hk : 1 ≤ syl k := by have := syl_two_le k; omega
  have hq' : syl k = syl i * q + 1 := by omega
  rw [hq', Nat.add_mod, Nat.mul_mod_right]
  simp [Nat.mod_eq_of_lt h2]

/-- The reciprocal sum identity for the Sylvester sequence. -/
lemma syl_sum_inv (k : ℕ) :
    (∑ i ∈ Finset.range k, (1 : ℚ) / syl i) = 1 - 1 / (syl k - 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have h2 : 2 ≤ syl k := syl_two_le k
      have hsk1 : (syl k : ℚ) - 1 ≠ 0 := by
        have : (2:ℚ) ≤ (syl k : ℚ) := by exact_mod_cast h2
        intro h; linarith
      have hcast : ((syl (k+1) : ℕ) : ℚ) - 1 = (syl k : ℚ) * ((syl k : ℚ) - 1) := by
        rw [syl_succ]
        push_cast [Nat.cast_sub (show 1 ≤ syl k by omega)]
        ring
      rw [hcast]
      field_simp
      ring

lemma syl_sum_inv_lt_one (k : ℕ) :
    (∑ i ∈ Finset.range k, (1 : ℚ) / syl i) < 1 := by
  rw [syl_sum_inv]
  have h2 : 2 ≤ syl k := syl_two_le k
  have : (0:ℚ) < (syl k : ℚ) - 1 := by
    have : (2:ℚ) ≤ (syl k : ℚ) := by exact_mod_cast h2
    linarith
  rw [sub_lt_iff_lt_add]
  have hpos : 0 < 1 / ((syl k : ℚ) - 1) := by positivity
  linarith

/-! ## Hanson's multinomial-type integer and the logarithmic weight `Lw` -/

/-- `∏_{i ≤ n} (n / syl i)!` (Hanson's multinomial-type integer `n!/…`). -/
def sylBlocks (n : ℕ) : ℕ := ∏ i ∈ Finset.range (n + 1), Nat.factorial (n / syl i)

/-- `Lw n = ∑_{syl i ≤ n} log (syl i) / syl i`. -/
noncomputable def Lw (n : ℕ) : ℝ :=
  ∑ i ∈ (Finset.range (n + 1)).filter (fun i => syl i ≤ n), Real.log (syl i) / (syl i)

/-! ## Elementary factorial estimates -/

lemma log_one_add_le (t : ℝ) (ht : 0 < t) : Real.log (1 + t) ≤ t := by
  have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + t by linarith)
  linarith

lemma le_log_one_add (t : ℝ) (ht : 0 < t) : t / (1 + t) ≤ Real.log (1 + t) := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 / (1 + t) by positivity)
  rw [Real.log_div (by norm_num) (by positivity), Real.log_one] at h
  have h2 : 1 / (1 + t) - 1 = -(t / (1 + t)) := by field_simp; ring
  rw [h2] at h
  linarith

lemma factorial_eq_prod (n : ℕ) : n.factorial = ∏ i ∈ Finset.range n, (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_range_succ, Nat.factorial_succ, ih]; ring

/-- `∑_{i<n} log (i+1) ≤ (n+1) log (n+1) - n`. -/
lemma log_sum_range_le (n : ℕ) :
    (∑ i ∈ Finset.range n, Real.log ((i : ℝ) + 1)) ≤ (n + 1 : ℝ) * Real.log (n + 1) - n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have ih' := ih
      have h2 : ((n:ℝ) + 2) / ((n:ℝ) + 1) = 1 + 1/((n:ℝ)+1) := by field_simp; ring
      have h3 : (1/((n:ℝ)+1)) / (1 + 1/((n:ℝ)+1)) ≤ Real.log (1 + 1/((n:ℝ)+1)) :=
        le_log_one_add (1/((n:ℝ)+1)) (by positivity)
      rw [← h2] at h3
      have h4 : 1/((n:ℝ)+2) ≤ Real.log (((n:ℝ)+2)/((n:ℝ)+1)) := by
        have h5 : (1/((n:ℝ)+1)) / (((n:ℝ)+2)/((n:ℝ)+1)) = 1/((n:ℝ)+2) := by
          field_simp
        linarith [h3, h5]
      have h6 : 1 ≤ ((n:ℝ)+2) * (Real.log ((n:ℝ)+2) - Real.log ((n:ℝ)+1)) := by
        rw [Real.log_div (by positivity) (by positivity)] at h4
        have hmul := mul_le_mul_of_nonneg_left h4 (show (0:ℝ) ≤ (n:ℝ)+2 by positivity)
        have he : ((n:ℝ)+2) * (1/((n:ℝ)+2)) = 1 := by field_simp
        linarith [hmul, he]
      push_cast
      have hcast3 : (↑n + 1 + 1 : ℝ) = ↑n + 2 := by ring
      rw [hcast3]
      nlinarith [ih', h6]

/-- `log n! ≤ (n+1) log (n+1) - n`. -/
lemma log_factorial_le (n : ℕ) : Real.log (n.factorial) ≤ (n + 1 : ℝ) * Real.log (n + 1) - n := by
  have h := log_sum_range_le n
  rw [factorial_eq_prod, Nat.cast_prod, Real.log_prod]
  · push_cast
    exact h
  · intro i _; positivity

/-- `log n! ≤ n log n - n + log (n+1) + 1` for `n ≥ 1`. -/
lemma log_factorial_le' (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial) ≤ (n:ℝ) * Real.log n - n + Real.log (n + 1) + 1 := by
  have h := log_factorial_le n
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have h2 : ((n:ℝ)+1) * Real.log ((n:ℝ)+1) ≤
      (n:ℝ) * Real.log n + Real.log ((n:ℝ)+1) + 1 := by
    have hlog : ((n:ℝ)+1) * Real.log ((n:ℝ)+1)
        = (n:ℝ) * Real.log ((n:ℝ)+1) + Real.log ((n:ℝ)+1) := by ring
    rw [hlog]
    have h3 : (n:ℝ) * Real.log ((n:ℝ)+1) ≤ (n:ℝ) * Real.log n + 1 := by
      have h4 := log_one_add_le (1/(n:ℝ)) (by positivity)
      have hq : 1 + 1/(n:ℝ) = ((n:ℝ)+1)/(n:ℝ) := by field_simp; try ring
      rw [hq] at h4
      rw [Real.log_div (by positivity) (by positivity)] at h4
      have h5 := mul_le_mul_of_nonneg_left h4 (le_of_lt hn')
      have he : (n:ℝ)*(1/(n:ℝ)) = 1 := by field_simp
      linarith [h5, he]
    linarith [h3]
  linarith [h, h2]

/-- `∑_{i<m} log (i+1) ≥ m log m - m + 1` for `m ≥ 1`. -/
lemma log_factorial_ge_sum (m : ℕ) (hm : 1 ≤ m) :
    (m:ℝ) * Real.log m - m + 1 ≤ (∑ i ∈ Finset.range m, Real.log ((i:ℝ)+1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  induction j with
  | zero => norm_num
  | succ j ih =>
      rw [Finset.sum_range_succ]
      have ih' : ((j:ℝ)+1) * Real.log ((j:ℝ)+1) - ((j:ℝ)+1) + 1 ≤
          ∑ i ∈ range (j+1), Real.log ((i:ℝ)+1) := by
        have h := ih (by omega)
        push_cast at h
        exact h
      have hcast3 : (((j:ℝ)+1)+1) = ((j:ℝ)+2) := by ring
      have hmul : ((j:ℝ)+1) * (Real.log ((j:ℝ)+2) - Real.log ((j:ℝ)+1)) ≤ 1 := by
        have hlog : Real.log ((j:ℝ)+2) - Real.log ((j:ℝ)+1)
            = Real.log (((j:ℝ)+2)/((j:ℝ)+1)) := by
          rw [Real.log_div (by positivity) (by positivity)]
        rw [hlog]
        have hx : (0:ℝ) < ((j:ℝ)+2)/((j:ℝ)+1) := by positivity
        have h := Real.log_le_sub_one_of_pos hx
        have hsub : ((j:ℝ)+2)/((j:ℝ)+1) - 1 = 1/((j:ℝ)+1) := by
          field_simp
          try ring
        rw [hsub] at h
        have hm2 := mul_le_mul_of_nonneg_left h (show (0:ℝ) ≤ (j:ℝ)+1 by positivity)
        have he : ((j:ℝ)+1) * (1/((j:ℝ)+1)) = 1 := by field_simp
        linarith [hm2, he]
      have hstep : ((j:ℝ)+1) * Real.log ((j:ℝ)+2) ≤ ((j:ℝ)+1) * Real.log ((j:ℝ)+1) + 1 := by
        linarith [hmul]
      push_cast
      rw [hcast3]
      nlinarith [ih', hstep]

/-- `log m! ≥ m log m - m + 1` for `m ≥ 1`. -/
lemma log_factorial_ge (m : ℕ) (hm : 1 ≤ m) :
    (m:ℝ) * Real.log m - m + 1 ≤ Real.log m.factorial := by
  have h := log_factorial_ge_sum m hm
  rw [factorial_eq_prod, Nat.cast_prod, Real.log_prod]
  · push_cast
    exact h
  · intro i _; positivity


/-! ## Inlined results of delegated sub-lemmas (Hanson's divisibility, and the Sylvester `Lw` bounds)

The following two blocks are `Work.BW.syl_divisibility` and `Work.BW.syl_log_facts`, proved in
`Submission/Work/BW/syl_divisibility.lean` and `Submission/Work/BW/syl_log_facts.lean`.
They cannot be *imported* here (they import this file to get `syl`, `sylBlocks`, `Lw`), so their
proofs are inlined. -/

open Finset

lemma sylBlocks_ne_zero (n : ℕ) : sylBlocks n ≠ 0 := by
  rw [sylBlocks]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero (n / syl i)

/-- **The floor lemma.** For `1 ≤ m ≤ N`, `∑_{i ≤ N} ⌊m / syl i⌋ + 1 ≤ m`.

Only the terms with `i ≤ m` can be nonzero (for `i > m` one has `m < i + 2 ≤ syl i`), so it
suffices to bound `∑_{i ≤ m} ⌊m / syl i⌋`.  Since `⌊x⌋ ≤ x` and the Egyptian-fraction identity
`∑_{i ≤ m} 1 / syl i = 1 - 1 / (syl (m+1) - 1)` holds (`syl_sum_inv`), the exact rational sum is
`m * (1 - 1 / (syl (m+1) - 1)) < m`, and an integer strictly below `m` is at most `m - 1`. -/
lemma syl_div_sum_le {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    (∑ i ∈ Finset.range (N + 1), m / syl i) + 1 ≤ m := by
  have hsub : Finset.range (m + 1) ⊆ Finset.range (N + 1) := Finset.range_mono (by omega)
  have hzero : ∀ x ∈ Finset.range (N + 1), x ∉ Finset.range (m + 1) → m / syl x = 0 := by
    intro x _ hx
    simp only [Finset.mem_range, not_lt] at hx
    exact Nat.div_eq_of_lt (by have := syl_ge x; omega)
  rw [← Finset.sum_subset hsub hzero]
  have hkey : (∑ i ∈ Finset.range (m + 1), m / syl i) ≤ m - 1 := by
    have hlt : ((∑ i ∈ Finset.range (m + 1), m / syl i : ℕ) : ℚ) < (m : ℚ) := by
      have h1 : ((∑ i ∈ Finset.range (m + 1), m / syl i : ℕ) : ℚ)
          ≤ ∑ i ∈ Finset.range (m + 1), (m : ℚ) / (syl i : ℚ) := by
        push_cast
        exact Finset.sum_le_sum fun i _ => Nat.cast_div_le
      have h2 : (∑ i ∈ Finset.range (m + 1), (m : ℚ) / (syl i : ℚ))
          = (m : ℚ) * (1 - 1 / (syl (m + 1) - 1)) := by
        have hmul : (∑ i ∈ Finset.range (m + 1), (m : ℚ) / (syl i : ℚ))
            = (m : ℚ) * (∑ i ∈ Finset.range (m + 1), (1 : ℚ) / (syl i : ℚ)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => (mul_one_div (m : ℚ) (syl i : ℚ)).symm
        rw [hmul]
        exact congrArg (fun x : ℚ => (m : ℚ) * x) (syl_sum_inv (m + 1))
      have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (show 0 < m by omega)
      have hKpos : (0 : ℚ) < 1 / (syl (m + 1) - 1) := by
        rw [one_div_pos]
        have h2le : 2 ≤ syl (m + 1) := syl_two_le (m + 1)
        have hcast : (2 : ℚ) ≤ (syl (m + 1) : ℚ) := by exact_mod_cast h2le
        linarith
      have hmK : (0 : ℚ) < (m : ℚ) * (1 / (syl (m + 1) - 1)) := mul_pos hmpos hKpos
      have heq : (m : ℚ) * (1 - 1 / (syl (m + 1) - 1))
          = (m : ℚ) - (m : ℚ) * (1 / (syl (m + 1) - 1)) := by
        rw [mul_sub, mul_one]
      rw [h2, heq] at h1
      linarith
    have hlt' : (∑ i ∈ Finset.range (m + 1), m / syl i) < m := by exact_mod_cast hlt
    omega
  omega

/-- **Hanson's divisibility (Lemma 2 of Hanson 1972)**: `lcm(1,…,n) * ∏_{i≤n} (n / syl i)! ∣ n!`,
where `syl` is Sylvester's sequence (`syl 0 = 2`, `syl (n+1) = syl n * (syl n - 1) + 1`) and
`ulcm n = lcm(1,…,n)` (definitions in `Submission/Work/BW/ulcm_le_three_pow.lean`).

Route.  Compare `p`-adic valuations: it suffices that for every prime `p` with `p^j ≤ n`,
`(∑_{i} n / (syl i * p^j)) + 1 ≤ n / p^j`.  (Indeed `(ulcm n).factorization p = Nat.log p n`
for `ulcm k = Nat.lcmUpto k` (`Nat.factorization_lcmUpto`), `n.factorial.factorization p =
∑_{i ∈ Ico 1 b} n / p ^ i` for `b > Nat.log p n` (`Nat.factorization_factorial`), and
`Nat.factorization_prod`, `Nat.factorization_mul`, `Nat.factorization_prime_le_iff_dvd`.)

That "floor lemma" follows from the Sylvester identities `∏_{i<k} syl i = syl k - 1`,
`∑_{i<k} 1/syl i = 1 - 1/(syl k - 1)` and `syl k % syl i = 1` (`i < k`), by strong induction on
`m = n / p^j`: write `m = syl k + s` with `syl k ≤ m < syl (k+1)`; for `i < k`,
`m / syl i = (syl k - 1)/syl i + (s + 1)/syl i` (exact, using `syl k % syl i = 1`), and
`∑_{i<k} (syl k - 1)/syl i = syl k - 2`, so the induction hypothesis at `s + 1 < m` applies. -/
theorem syl_divisibility (n : ℕ) : ulcm n * sylBlocks n ∣ Nat.factorial n := by
  refine (Nat.factorization_prime_le_iff_dvd
    (mul_ne_zero (ulcm_ne_zero n) (sylBlocks_ne_zero n)) (Nat.factorial_ne_zero n)).mp ?_
  intro p hp
  have hfac_ulcm : (ulcm n).factorization p = Nat.log p n := ulcm_factorization n hp
  have hfac_blocks : (sylBlocks n).factorization p
      = ∑ i ∈ Finset.range (n + 1), ((n / syl i).factorial).factorization p := by
    rw [sylBlocks, Nat.factorization_prod (fun i _ => Nat.factorial_ne_zero (n / syl i)),
      Finsupp.finsetSum_apply]
  rw [Nat.factorization_mul (ulcm_ne_zero n) (sylBlocks_ne_zero n), Finsupp.add_apply,
    hfac_ulcm, hfac_blocks]
  have hlog : ∀ i : ℕ, Nat.log p (n / syl i) < Nat.log p n + 1 := by
    intro i
    have h := Nat.log_mono_right (b := p) (Nat.div_le_self n (syl i))
    omega
  have h1 : (∑ i ∈ Finset.range (n + 1), ((n / syl i).factorial).factorization p)
      ≤ ∑ i ∈ Finset.range (n + 1),
          ∑ j ∈ Finset.Ico 1 (Nat.log p n + 1), (n / syl i) / p ^ j :=
    Finset.sum_le_sum fun i _ =>
      le_of_eq (Nat.factorization_factorial hp (n := n / syl i)
        (b := Nat.log p n + 1) (hlog i))
  have hinner : ∀ j : ℕ, (∑ i ∈ Finset.range (n + 1), (n / syl i) / p ^ j)
      = ∑ i ∈ Finset.range (n + 1), (n / p ^ j) / syl i := by
    intro j
    exact Finset.sum_congr rfl fun i _ => by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm (syl i) (p ^ j)]
  have hswap : (∑ i ∈ Finset.range (n + 1),
          ∑ j ∈ Finset.Ico 1 (Nat.log p n + 1), (n / syl i) / p ^ j)
      = ∑ j ∈ Finset.Ico 1 (Nat.log p n + 1),
          ∑ i ∈ Finset.range (n + 1), (n / p ^ j) / syl i := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => hinner j
  have hcard : (Finset.Ico 1 (Nat.log p n + 1)).card = Nat.log p n := by
    rw [Nat.card_Ico]; omega
  have h2 : Nat.log p n + ∑ j ∈ Finset.Ico 1 (Nat.log p n + 1),
          (∑ i ∈ Finset.range (n + 1), (n / p ^ j) / syl i)
      = ∑ j ∈ Finset.Ico 1 (Nat.log p n + 1),
          ((∑ i ∈ Finset.range (n + 1), (n / p ^ j) / syl i) + 1) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, hcard, smul_eq_mul, mul_one]
    omega
  have h3 : ∀ j ∈ Finset.Ico 1 (Nat.log p n + 1),
      (∑ i ∈ Finset.range (n + 1), (n / p ^ j) / syl i) + 1 ≤ n / p ^ j := by
    intro j hj
    obtain ⟨hj1, hjk⟩ := Finset.mem_Ico.mp hj
    have hpow : p ^ j ≤ n := by
      have hjn : n ≠ 0 := by
        rintro rfl
        simp only [Nat.log_zero_right] at hjk
        omega
      exact le_trans (Nat.pow_le_pow_right hp.pos (by omega))
        (Nat.pow_log_le_self p hjn)
    exact syl_div_sum_le (m := n / p ^ j) (N := n)
      ((Nat.le_div_iff_mul_le (pow_pos hp.pos j)).mpr (by simpa using hpow))
      (Nat.div_le_self n (p ^ j))
  have hmain : Nat.log p n + ∑ i ∈ Finset.range (n + 1),
        ((n / syl i).factorial).factorization p
      ≤ ∑ j ∈ Finset.Ico 1 (Nat.log p n + 1), n / p ^ j := by
    have hadd : Nat.log p n + ∑ i ∈ Finset.range (n + 1),
          ((n / syl i).factorial).factorization p
        ≤ Nat.log p n + ∑ i ∈ Finset.range (n + 1),
          ∑ j ∈ Finset.Ico 1 (Nat.log p n + 1), (n / syl i) / p ^ j :=
      Nat.add_le_add_left h1 _
    rw [hswap] at hadd
    rw [h2] at hadd
    exact le_trans hadd (Finset.sum_le_sum h3)
  rw [Nat.factorization_factorial hp (n := n) (b := Nat.log p n + 1) (by omega)]
  exact hmain

/-! # Numeric facts for the Sylvester weights -/


open Finset

noncomputable section

private lemma syl_two_le' : ∀ n : ℕ, 2 ≤ syl n := by
  intro n
  induction n with
  | zero => show 2 ≤ 2; norm_num
  | succ n ih =>
      show 2 ≤ syl n * (syl n - 1) + 1
      have h1 : 1 ≤ syl n - 1 := by omega
      have h2 : 0 < syl n * (syl n - 1) := Nat.mul_pos (by omega) (by omega)
      omega

private lemma syl_mono' : Monotone syl := by
  apply monotone_nat_of_le_succ
  intro n
  show syl n ≤ syl n * (syl n - 1) + 1
  have h1 : 1 ≤ syl n - 1 := by have := syl_two_le' n; omega
  have h2 : syl n * 1 ≤ syl n * (syl n - 1) := Nat.mul_le_mul_left _ h1
  omega

private lemma syl_four : syl 4 = 1807 := rfl

private lemma syl_ge_1807 {i : ℕ} (hi : 4 ≤ i) : 1807 ≤ syl i := by
  have h := syl_mono' hi
  rwa [syl_four] at h

private lemma syl_succ_cast (i : ℕ) :
    (syl (i + 1) : ℝ) = (syl i : ℝ) * ((syl i : ℝ) - 1) + 1 := by
  have h1 : 1 ≤ syl i := by have := syl_two_le' i; omega
  have h : syl (i + 1) = syl i * (syl i - 1) + 1 := rfl
  rw [h, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_sub h1]
  ring

private lemma syl_succ_le_sq (i : ℕ) : (syl (i + 1) : ℝ) ≤ (syl i : ℝ) ^ 2 := by
  rw [syl_succ_cast i]
  have h : (2 : ℝ) ≤ (syl i : ℝ) := by exact_mod_cast syl_two_le' i
  nlinarith [sq_nonneg ((syl i : ℝ) - 1)]

private lemma syl_sq_le_succ (i : ℕ) : (syl i : ℝ) ^ 2 ≤ 2 * (syl (i + 1) : ℝ) := by
  rw [syl_succ_cast i]
  have h : (2 : ℝ) ≤ (syl i : ℝ) := by exact_mod_cast syl_two_le' i
  nlinarith [sq_nonneg ((syl i : ℝ) - 1)]

private def aw (i : ℕ) : ℝ := Real.log (syl i) / (syl i : ℝ)

private lemma aw_nonneg (i : ℕ) : 0 ≤ aw i := by
  have h1 : (1 : ℝ) ≤ (syl i : ℝ) := by
    have := syl_two_le' i
    exact_mod_cast (show (1 : ℕ) ≤ syl i by omega)
  rw [aw]
  exact div_nonneg (Real.log_nonneg h1) (by linarith)

private lemma aw_succ_le (i : ℕ) : aw (i + 1) ≤ 4 * aw i / (syl i : ℝ) := by
  have hpos : (0 : ℝ) < (syl i : ℝ) := by
    have := syl_two_le' i
    exact_mod_cast (show (0 : ℕ) < syl i by omega)
  have hlog_nonneg : 0 ≤ Real.log (syl i : ℝ) := by
    apply Real.log_nonneg
    have := syl_two_le' i
    exact_mod_cast (show (1 : ℕ) ≤ syl i by omega)
  have hpos' : (0 : ℝ) < (syl (i + 1) : ℝ) := by
    have := syl_two_le' (i + 1)
    exact_mod_cast (show (0 : ℕ) < syl (i + 1) by omega)
  have hlog : Real.log (syl (i + 1) : ℝ) ≤ 2 * Real.log (syl i : ℝ) := by
    have h : Real.log (syl (i + 1) : ℝ) ≤ Real.log ((syl i : ℝ) ^ 2) :=
      Real.log_le_log hpos' (syl_succ_le_sq i)
    rwa [Real.log_pow] at h
  have hnum : 0 ≤ Real.log (syl (i + 1) : ℝ) := by
    apply Real.log_nonneg
    have := syl_two_le' (i + 1)
    exact_mod_cast (show (1 : ℕ) ≤ syl (i + 1) by omega)
  have hden_pos : 0 < (syl i : ℝ) ^ 2 / 2 := by positivity
  have hden : (syl i : ℝ) ^ 2 / 2 ≤ (syl (i + 1) : ℝ) := by linarith [syl_sq_le_succ i]
  calc aw (i + 1) = Real.log (syl (i + 1) : ℝ) / (syl (i + 1) : ℝ) := rfl
    _ ≤ (2 * Real.log (syl i : ℝ)) / ((syl i : ℝ) ^ 2 / 2) :=
        div_le_div₀ (by linarith) hlog hden_pos hden
    _ = 4 * aw i / (syl i : ℝ) := by
        rw [aw]
        field_simp
        ring

private lemma aw_succ_le_half {i : ℕ} (hi : 4 ≤ i) : aw (i + 1) ≤ (1 / 2) * aw i := by
  have h := aw_succ_le i
  have h1807 : (1807 : ℝ) ≤ (syl i : ℝ) := by
    have := syl_ge_1807 hi
    exact_mod_cast this
  have haw : 0 ≤ aw i := aw_nonneg i
  have hstep : 4 * aw i / (syl i : ℝ) ≤ (4 / 1807) * aw i := by
    have h1 : 4 * aw i / (syl i : ℝ) ≤ 4 * aw i / 1807 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) h1807
    have h2 : 4 * aw i / (1807 : ℝ) = (4 / 1807) * aw i := by ring
    linarith [h1, h2]
  have h3 : (4 / 1807 : ℝ) * aw i ≤ (1 / 2) * aw i := by nlinarith
  linarith [h, hstep, h3]

private lemma log7_le : Real.log 7 ≤ (73 / 26 : ℝ) * Real.log 2 := by
  have h : (7 : ℝ) ^ 26 ≤ (2 : ℝ) ^ 73 := by norm_num
  have hlog : (26 : ℝ) * Real.log 7 ≤ (73 : ℝ) * Real.log 2 := by
    have := Real.log_le_log (by positivity : (0 : ℝ) < (7 : ℝ) ^ 26) h
    rwa [Real.log_pow, Real.log_pow] at this
  rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 26)]
  linarith

private lemma log43_le : Real.log 43 ≤ (38 / 7 : ℝ) * Real.log 2 := by
  have h : (43 : ℝ) ^ 7 ≤ (2 : ℝ) ^ 38 := by norm_num
  have hlog : (7 : ℝ) * Real.log 43 ≤ (38 : ℝ) * Real.log 2 := by
    have := Real.log_le_log (by positivity : (0 : ℝ) < (43 : ℝ) ^ 7) h
    rwa [Real.log_pow, Real.log_pow] at this
  rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 7)]
  linarith

private lemma log1807_le : Real.log 1807 ≤ (65 / 6 : ℝ) * Real.log 2 := by
  have h : (1807 : ℝ) ^ 6 ≤ (2 : ℝ) ^ 65 := by norm_num
  have hlog : (6 : ℝ) * Real.log 1807 ≤ (65 : ℝ) * Real.log 2 := by
    have := Real.log_le_log (by positivity : (0 : ℝ) < (1807 : ℝ) ^ 6) h
    rwa [Real.log_pow, Real.log_pow] at this
  rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 6)]
  linarith

private def C0 : ℝ := 0.6931471808 / 2
private def C1 : ℝ := 1.0986122888 / 3
private def C2 : ℝ := (73 / 26) * 0.6931471808 / 7
private def C3 : ℝ := (38 / 7) * 0.6931471808 / 43
private def C4 : ℝ := (65 / 6) * 0.6931471808 / 1807
private def B5 : ℝ := (65 / 3) * 0.6931471808 / 3263443

private lemma B5_nonneg : 0 ≤ B5 := by unfold B5; norm_num

private lemma aw0_le : aw 0 ≤ C0 := by
  have h : syl 0 = 2 := rfl
  have haw : aw 0 = Real.log 2 / 2 := by simp only [aw, h]; norm_num
  rw [haw, C0]
  linarith [Real.log_two_lt_d9]

private lemma aw1_le : aw 1 ≤ C1 := by
  have h : syl 1 = 3 := rfl
  have haw : aw 1 = Real.log 3 / 3 := by simp only [aw, h]; norm_num
  rw [haw, C1]
  linarith [Real.log_three_lt_d9]

private lemma aw2_le : aw 2 ≤ C2 := by
  have h : syl 2 = 7 := rfl
  have haw : aw 2 = Real.log 7 / 7 := by simp only [aw, h]; norm_num
  have h1 : (73 / 26 : ℝ) * Real.log 2 ≤ (73 / 26 : ℝ) * 0.6931471808 :=
    mul_le_mul_of_nonneg_left (le_of_lt Real.log_two_lt_d9) (by norm_num)
  rw [haw, C2]
  linarith [log7_le, h1]

private lemma aw3_le : aw 3 ≤ C3 := by
  have h : syl 3 = 43 := rfl
  have haw : aw 3 = Real.log 43 / 43 := by simp only [aw, h]; norm_num
  have h1 : (38 / 7 : ℝ) * Real.log 2 ≤ (38 / 7 : ℝ) * 0.6931471808 :=
    mul_le_mul_of_nonneg_left (le_of_lt Real.log_two_lt_d9) (by norm_num)
  rw [haw, C3]
  linarith [log43_le, h1]

private lemma aw4_le : aw 4 ≤ C4 := by
  have h : syl 4 = 1807 := rfl
  have haw : aw 4 = Real.log 1807 / 1807 := by simp only [aw, h]; norm_num
  have h1 : (65 / 6 : ℝ) * Real.log 2 ≤ (65 / 6 : ℝ) * 0.6931471808 :=
    mul_le_mul_of_nonneg_left (le_of_lt Real.log_two_lt_d9) (by norm_num)
  rw [haw, C4]
  linarith [log1807_le, h1]

private lemma aw5_le : aw 5 ≤ B5 := by
  have h : syl 5 = 3263443 := rfl
  have haw : aw 5 = Real.log 3263443 / 3263443 := by simp only [aw, h]; norm_num
  have hle : (3263443 : ℝ) ≤ (1807 : ℝ) ^ 2 := by norm_num
  have hlog : Real.log (3263443 : ℝ) ≤ 2 * Real.log 1807 := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3263443) hle
    rwa [Real.log_pow] at hh
  have h1 : (65 / 6 : ℝ) * Real.log 2 ≤ (65 / 6 : ℝ) * 0.6931471808 :=
    mul_le_mul_of_nonneg_left (le_of_lt Real.log_two_lt_d9) (by norm_num)
  have h2 : (2 : ℝ) * Real.log 1807 ≤ (2 : ℝ) * ((65 / 6) * 0.6931471808) :=
    mul_le_mul_of_nonneg_left (by linarith [log1807_le, h1]) (by norm_num)
  have h3 : Real.log (3263443 : ℝ) ≤ (65 / 3) * 0.6931471808 := by linarith
  rw [haw, B5]
  linarith

private lemma aw_geo (j : ℕ) : aw (5 + j) ≤ B5 * (1 / 2) ^ j := by
  induction j with
  | zero => simpa using aw5_le
  | succ j ih =>
      have hstep : 5 + (j + 1) = (5 + j) + 1 := by omega
      rw [hstep]
      have h1 : aw ((5 + j) + 1) ≤ (1 / 2) * aw (5 + j) := aw_succ_le_half (by omega)
      have h2 : (1 / 2) * aw (5 + j) ≤ (1 / 2) * (B5 * (1 / 2) ^ j) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      calc aw ((5 + j) + 1) ≤ (1 / 2) * aw (5 + j) := h1
        _ ≤ (1 / 2) * (B5 * (1 / 2) ^ j) := h2
        _ = B5 * (1 / 2) ^ (j + 1) := by rw [pow_succ]; ring

private lemma tail_le (m : ℕ) : (∑ j ∈ Finset.range m, aw (5 + j)) ≤ 2 * B5 := by
  have h1 : (∑ j ∈ Finset.range m, aw (5 + j)) ≤ ∑ j ∈ Finset.range m, B5 * (1 / 2) ^ j :=
    Finset.sum_le_sum (fun j _ => aw_geo j)
  have h2 : (∑ j ∈ Finset.range m, B5 * (1 / 2) ^ j) = B5 * ∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ j := by
    rw [Finset.mul_sum]
  have h3 : (∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ j) ≤ 2 := by
    have hgeom : ∀ k : ℕ, (∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j) ≤ 2 - 2 * (1 / 2) ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [Finset.sum_range_succ, pow_succ]
          have hpow : (0 : ℝ) < (1 / 2) ^ k := by positivity
          linarith
    have hp : 0 ≤ 2 * (1 / 2 : ℝ) ^ m := by positivity
    linarith [hgeom m]
  have h5 : B5 * (∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ j) ≤ B5 * 2 :=
    mul_le_mul_of_nonneg_left h3 B5_nonneg
  linarith [h1, h2, h5]

private lemma prefix_le : (∑ i ∈ Finset.range 5, aw i) ≤ C0 + C1 + C2 + C3 + C4 := by
  have h0 := aw0_le
  have h1 := aw1_le
  have h2 := aw2_le
  have h3 := aw3_le
  have h4 := aw4_le
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith

private def K : ℝ := C0 + C1 + C2 + C3 + C4 + 2 * B5

private lemma K_le : K ≤ 1.0826 := by
  unfold K C0 C1 C2 C3 C4 B5
  norm_num

private lemma sum_le (N : ℕ) : (∑ i ∈ Finset.range N, aw i) ≤ K := by
  rcases le_or_gt N 5 with hN | hN
  · have hsub : Finset.range N ⊆ Finset.range 5 := Finset.range_subset_range.mpr hN
    have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => aw_nonneg i)
    have hpre := prefix_le
    have hB5 := B5_nonneg
    unfold K
    linarith
  · obtain ⟨m, rfl⟩ : ∃ m, N = 5 + m := ⟨N - 5, by omega⟩
    rw [Finset.sum_range_add]
    have h1 := prefix_le
    have h2 := tail_le m
    unfold K
    linarith

/-- Numeric facts for the Sylvester weights (`Lw n = ∑_{syl i ≤ n} log (syl i)/syl i`, with `syl`
Sylvester's sequence from `Submission/Work/BW/ulcm_le_three_pow.lean`):
`1.0986 ≤ log 3 ≤ 1.0987`, `log 2 ≤ 0.6932`, and `Lw n ≤ 1.0826` for every `n`
(the first four terms give `1.07824`, then `log 1807/1807 < 0.00416`, `log 3263443/3263443 < 5·10⁻⁶`
and the tail decays doubly exponentially since `syl (i+1) ≥ syl i ^ 2 / 2`). -/
private theorem syl_log_facts :
    (1.0986 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ 1.0987 ∧ Real.log 2 ≤ 0.6932 ∧
      (∀ n : ℕ, Lw n ≤ 1.0826) := by
  refine ⟨by linarith [Real.log_three_gt_d9], by linarith [Real.log_three_lt_d9],
    by linarith [Real.log_two_lt_d9], ?_⟩
  intro n
  have hle : Lw n ≤ ∑ i ∈ Finset.range (n + 1), aw i := by
    unfold Lw
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => ?_)
    exact aw_nonneg i
  exact le_trans hle (le_trans (sum_le (n + 1)) K_le)

end


/-! ## Inlined proofs of the delegated numeric sub-lemmas -/

/-- `x ↦ (log x)^2 / x` is antitone for `x ≥ exp 2`.

This is the key monotonicity: on `[exp 2, ∞)` the derivative `log x (2 - log x)/x^2`
is nonpositive.  We instead derive it from `Real.log_div_sqrt_antitoneOn` for
`g x = log x / √x`: for `x > 0`, `(log x)^2 / x = (log x / √x)^2`, and the square of
a nonnegative antitone function is antitone. -/
lemma logsq_div_antitoneOn :
    AntitoneOn (fun x : ℝ => (Real.log x) ^ 2 / x) (Set.Ici (Real.exp 2)) := by
  intro x hx y hy hxy
  have hx2 : Real.exp 2 ≤ x := hx
  have hy2 : Real.exp 2 ≤ y := hy
  have hxpos : 0 < x := (Real.exp_pos 2).trans_le hx2
  have hypos : 0 < y := (Real.exp_pos 2).trans_le hy2
  have hlogy : 0 ≤ Real.log y := by
    have h2 : 2 ≤ Real.log y := by
      rw [← Real.log_exp 2]
      exact Real.log_le_log (Real.exp_pos 2) hy2
    linarith
  have hgy : 0 ≤ Real.log y / Real.sqrt y :=
    div_nonneg hlogy (Real.sqrt_nonneg y)
  have hg : Real.log y / Real.sqrt y ≤ Real.log x / Real.sqrt x :=
    Real.log_div_sqrt_antitoneOn hx2 hy2 hxy
  have hsq : (Real.log y / Real.sqrt y) ^ 2 ≤ (Real.log x / Real.sqrt x) ^ 2 := by
    have := mul_self_le_mul_self hgy hg
    simpa [pow_two] using this
  have hyeq : (Real.log y) ^ 2 / y = (Real.log y / Real.sqrt y) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hypos.le]
  have hxeq : (Real.log x) ^ 2 / x = (Real.log x / Real.sqrt x) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hxpos.le]
  simpa only [hyeq, hxeq] using hsq

/-- For `n ≥ 2^20`, the function `x ↦ (log x)^2 / x` is at most its value at `2^20`:
`2^20 * (log n)^2 ≤ n * (log 2^20)^2`. -/
theorem logsq_le_of_ge_N (n : ℕ) (hn : 1048576 ≤ n) :
    (1048576 : ℝ) * (Real.log n) ^ 2 ≤ (n : ℝ) * (Real.log 1048576) ^ 2 := by
  have hNpos : (0 : ℝ) < 1048576 := by norm_num
  have hnpos : (0 : ℝ) < n := by
    have : (0 : ℝ) < 1048576 := by norm_num
    exact this.trans_le (by exact_mod_cast hn)
  -- `log 2^20 = 20 log 2 ≥ 2`, hence `2^20 ≥ exp 2` and also `n ≥ exp 2`.
  have hlogN : Real.log 1048576 = 20 * Real.log 2 := by
    rw [show (1048576 : ℝ) = 2 ^ 20 by norm_num, Real.log_pow]
    norm_num
  have hN2 : (2 : ℝ) ≤ Real.log 1048576 := by
    rw [hlogN]; nlinarith [Real.log_two_gt_d9]
  have hexp2N : Real.exp 2 ≤ (1048576 : ℝ) :=
    (Real.le_log_iff_exp_le hNpos).mp hN2
  have hexp2n : Real.exp 2 ≤ (n : ℝ) := hexp2N.trans (by exact_mod_cast hn)
  have hle : (Real.log n) ^ 2 / n ≤ (Real.log 1048576) ^ 2 / 1048576 :=
    logsq_div_antitoneOn hexp2N hexp2n (by exact_mod_cast hn)
  rw [div_le_div_iff₀ hnpos hNpos] at hle
  linarith [hle]

/-- Tangent-line bound at `N = 2^20`: for `n ≥ N`, `log n ≤ log N + n/N - 1 ≤ (log N)·(n/N)`. -/
theorem log_le_logN_mul (n : ℕ) (hn : 1048576 ≤ n) :
    Real.log n ≤ Real.log 1048576 * ((n : ℝ) / 1048576) := by
  have hNpos : (0 : ℝ) < 1048576 := by norm_num
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  -- tangent-line (concavity) bound for `log` at `x = n / N`
  have hx : (0 : ℝ) < (n : ℝ) / 1048576 := by positivity
  have ht := Real.log_le_sub_one_of_pos hx
  rw [Real.log_div (ne_of_gt hnpos) (ne_of_gt hNpos)] at ht
  -- `log N ≥ 1` since `N = 2^20 = exp(log 2)^20` and `log 2 > 0.69`
  have hlogN : (1 : ℝ) ≤ Real.log 1048576 := by
    have h2 : (1048576 : ℝ) = 2 ^ 20 := by norm_num
    rw [h2, Real.log_pow]
    push_cast
    nlinarith [Real.log_two_gt_d9]
  -- `n / N ≥ 1`
  have hB : (1 : ℝ) ≤ (n : ℝ) / 1048576 := by
    rw [le_div_iff₀ hNpos]
    have : (1048576 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  -- `(log N + n/N - 1) ≤ (log N)·(n/N)` because `(log N - 1)(n/N - 1) ≥ 0`
  have hprod : 0 ≤ (Real.log 1048576 - 1) * ((n : ℝ) / 1048576 - 1) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [ht, hprod]

/-- Tangent-line (concavity) bound for the logarithm at the point `4096`:
for every `x > 0`, `log x ≤ log 4096 + (x - 4096) / 4096`.
This follows from `Real.log_le_sub_one_of_pos` applied to `x / 4096`. -/
lemma log_le_log4096_add {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ Real.log 4096 + (x - 4096) / 4096 := by
  have h4096 : (4096 : ℝ) ≠ 0 := by norm_num
  have h := Real.log_le_sub_one_of_pos (x := x / 4096) (by positivity)
  rw [Real.log_div (ne_of_gt hx) h4096] at h
  have hx' : x / 4096 - 1 = (x - 4096) / 4096 := by ring
  linarith [h, hx']

theorem num_regime1 (n : ℕ) (hn : 4096 ≤ n) :
    6 * Real.log n + Real.log (n + 1) + 1 + 1.0826 * n ≤ n * Real.log 3 := by
  have hnR : (4096 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have h1 : Real.log n ≤ Real.log 4096 + ((n : ℝ) - 4096) / 4096 :=
    log_le_log4096_add hnpos
  have h2 : Real.log (n + 1) ≤ Real.log 4096 + ((n : ℝ) + 1 - 4096) / 4096 := by
    have h := log_le_log4096_add (x := (n : ℝ) + 1) hn1pos
    simpa using h
  have hlog4096 : Real.log 4096 = 12 * Real.log 2 := by
    have h : (4096 : ℝ) = 2 ^ 12 := by norm_num
    rw [h, Real.log_pow]
    norm_num
  have h4 : Real.log 4096 ≤ 8.3184 := by
    rw [hlog4096]
    have hlt := Real.log_two_lt_d9
    nlinarith
  have h5 : (1.0986122885 : ℝ) ≤ Real.log 3 := le_of_lt Real.log_three_gt_d9
  -- The linear part: substitute the two tangent bounds and the bound on `log 4096`.
  have hmain : 6 * Real.log n + Real.log (n + 1) + 1 + 1.0826 * n
      ≤ (n : ℝ) * 1.0986122885 := by
    linarith [h1, h2, h4, hnR]
  -- Multiply the lower bound on `log 3` by the nonnegative factor `n`.
  have hmult : (n : ℝ) * 1.0986122885 ≤ (n : ℝ) * Real.log 3 :=
    mul_le_mul_of_nonneg_left h5 (le_of_lt hnpos)
  linarith [hmain, hmult]

/-- For `n < 3263443 = syl 5`, at most `5` Sylvester terms are `≤ n`:
`#{i ≤ n : syl i ≤ n} ≤ 5`.
Route: the filtered set is a subset of `Finset.range 5`, since `syl i ≤ n` with `i ≥ 5` gives
`syl 5 ≤ syl i ≤ n` by `Work.BW.syl_mono`, contradicting `n < 3263443 = syl 5` (`syl 5` is `rfl`). -/
theorem syl_card_le_five (n : ℕ) (hn : n < 3263443) :
    ((Finset.range (n + 1)).filter (fun i => syl i ≤ n)).card ≤ 5 := by
  have hsyl5 : syl 5 = 3263443 := by decide
  calc ((Finset.range (n + 1)).filter (fun i => syl i ≤ n)).card
      ≤ (Finset.range 5).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi
        simp only [Finset.mem_range]
        by_contra hcon
        have h5i : 5 ≤ i := by omega
        have hle : syl 5 ≤ syl i := syl_mono h5i
        omega
    _ = 5 := Finset.card_range 5

open Finset

/-- `2 ^ i ≤ syl i` for every `i`: from `syl_prod`, `syl i - 1 = ∏_{j<i} syl j ≥ ∏_{j<i} 2 = 2^i`. -/
lemma syl_two_pow_le (i : ℕ) : 2 ^ i ≤ syl i := by
  have hprod : (∏ j ∈ Finset.range i, syl j) = syl i - 1 := syl_prod i
  have h2 : 2 ^ i ≤ ∏ j ∈ Finset.range i, syl j := by
    calc 2 ^ i = ∏ _j ∈ Finset.range i, (2 : ℕ) := by rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ j ∈ Finset.range i, syl j := Finset.prod_le_prod (fun j _ => syl_two_le j)
  omega

/-- The number of Sylvester terms `≤ n` is at most `log₂ n + 1`:
`#{i ≤ n : syl i ≤ n} ≤ log n / log 2 + 1`.
Route: from `Work.BW.syl_prod`, `syl i - 1 = ∏_{j<i} syl j ≥ 2^i` (`syl_two_le`), so `2^i ≤ syl i` for
all `i`.  Hence any `i` in the filtered set satisfies `2^i ≤ n` (or `i = 0`), i.e. `i ≤ Nat.floor (log n / log 2)`;
the filtered set is contained in `Finset.range (Nat.floor (Real.log n / Real.log 2) + 1)`
(`Nat.le_floor`), and `Nat.floor_le`. -/
theorem syl_card_le_log (n : ℕ) :
    (((Finset.range (n + 1)).filter (fun i => syl i ≤ n)).card : ℝ) ≤ Real.log n / Real.log 2 + 1 := by
  set S := (Finset.range (n + 1)).filter (fun i => syl i ≤ n) with hS
  set m := Nat.floor (Real.log n / Real.log 2) with hm
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hsub : S ⊆ Finset.range (m + 1) := by
    intro i hi
    rw [hS, Finset.mem_filter] at hi
    obtain ⟨hirange, hsyl⟩ := hi
    rw [Finset.mem_range] at hirange ⊢
    have h2i : 2 ^ i ≤ syl i := syl_two_pow_le i
    have hle : (2 : ℝ) ^ i ≤ (n : ℝ) := by
      have : ((2 ^ i : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans h2i hsyl
      simpa using this
    have hlog : ((i : ℕ) : ℝ) * Real.log 2 ≤ Real.log n := by
      have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ i) hle
      rwa [Real.log_pow] at h
    have hile : ((i : ℕ) : ℝ) ≤ Real.log n / Real.log 2 := by
      rw [le_div_iff₀ hlog2pos]
      linarith
    have : i ≤ m := by
      rw [hm]
      exact Nat.le_floor hile
    omega
  have hcard_nat : S.card ≤ m + 1 := by
    simpa using Finset.card_le_card hsub
  have hcard : (S.card : ℝ) ≤ (m : ℝ) + 1 := by
    have h : ((S.card : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hcard_nat
    push_cast at h
    linarith
  have hmle : (m : ℝ) ≤ Real.log n / Real.log 2 := by
    apply Nat.floor_le
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp [Real.log_zero]
    · exact div_nonneg (Real.log_nonneg (by exact_mod_cast h)) (le_of_lt hlog2pos)
  linarith

/-- Numeric inequality for the regime `n ≥ 2^20 = 1048576`:
`(log n)^2 / log 2 + 2 log n + log (n+1) + 1 + 1.0826 n ≤ n log 3`.
Route: put `N = 1048576 = 2^20`, `u = log N = 20 log 2`, `t = n/N ≥ 1`.
(a) `x ↦ (log x)^2/x` is antitone on `[N,∞)`: the step `n (log (n+1))^2 ≤ (n+1) (log n)^2` follows
from `log (n+1) ≤ log n + 1/n` and `log n ≥ 13`; conclude `(log n)^2 / n ≤ u^2 / N`.
(b) tangent bound at `N`: `log n ≤ u + t - 1 ≤ u t` and `log (n+1) + 1 ≤ (u+1) t + 1/N`.
Then the LHS is `≤ t (u^2/log 2 + 3u + 1 + 1/N)`, and `u ≤ 13.864`, `u^2/log 2 = 400 log 2 ≤ 277.28`,
so `u^2/log 2 + 3u + 1 + 1/N ≤ 0.016 · N`; hence LHS `≤ 0.016 n ≤ n (log 3 - 1.0826)`
(`Real.log_three_gt_d9`, `Real.log_two_lt_d9`). -/
theorem num_regime2 (n : ℕ) (hn : 1048576 ≤ n) :
    (Real.log n) ^ 2 / Real.log 2 + 2 * Real.log n + Real.log (n + 1) + 1 + 1.0826 * n
      ≤ n * Real.log 3 := by
  have hNpos : (0:ℝ) < 1048576 := by norm_num
  have hnR : (1048576:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  have hnnonneg : (0:ℝ) ≤ (n:ℝ) := le_of_lt hnpos
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2half : (1:ℝ)/2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 2 by norm_num)
    norm_num at this ⊢; linarith
  have hlog2one : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    norm_num at this; linarith
  have hlogN : Real.log (1048576:ℝ) = 20 * Real.log 2 := by
    have h : (1048576:ℝ) = (2:ℝ)^20 := by norm_num
    rw [h, Real.log_pow]; norm_num
  have hu_le : Real.log (1048576:ℝ) ≤ 20 := by rw [hlogN]; nlinarith [hlog2one]
  have hu_nonneg : 0 ≤ Real.log (1048576:ℝ) := by rw [hlogN]; positivity
  have hu_sq_le : (Real.log (1048576:ℝ))^2 ≤ 400 := by nlinarith [hu_le, hu_nonneg]
  have hlogmono : Real.log (1048576:ℝ) ≤ Real.log (n:ℝ) := Real.log_le_log (by norm_num) hnR
  have hLn_ge : (10:ℝ) ≤ Real.log (n:ℝ) := by
    rw [hlogN] at hlogmono; nlinarith [Real.log_two_gt_d9, hlogmono]
  have hlogNP2 := logsq_le_of_ge_N n hn
  have htan := log_le_logN_mul n hn
  have h1 : (Real.log n)^2 / Real.log 2 ≤ 2*(Real.log n)^2 := by
    rw [div_le_iff₀ hlog2pos]; nlinarith [sq_nonneg (Real.log n)]
  have h2 : Real.log (n+1) ≤ 2 * Real.log n := by
    have hle : Real.log ((n:ℝ)+1) ≤ Real.log (2*(n:ℝ)) := by
      apply Real.log_le_log (by positivity)
      linarith
    rw [Real.log_mul (by norm_num) (ne_of_gt hnpos)] at hle
    have hlog2L : Real.log 2 ≤ Real.log (n:ℝ) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have h3 : (1:ℝ) ≤ Real.log (n:ℝ)/10 := by linarith
  have h4 : (Real.log n)^2 ≤ 400 * ((n:ℝ)/1048576) := by
    have step1 : (n:ℝ) * (Real.log (1048576:ℝ))^2 ≤ 400 * (n:ℝ) := by
      calc (n:ℝ) * (Real.log (1048576:ℝ))^2 ≤ (n:ℝ) * 400 :=
            mul_le_mul_of_nonneg_left hu_sq_le hnnonneg
        _ = 400 * (n:ℝ) := by ring
    have hNL : (1048576:ℝ) * (Real.log n)^2 ≤ 400 * (n:ℝ) := le_trans hlogNP2 step1
    have hNL' : (Real.log n)^2 * (1048576:ℝ) ≤ 400 * (n:ℝ) := by
      calc (Real.log n)^2 * (1048576:ℝ) = (1048576:ℝ) * (Real.log n)^2 := by ring
        _ ≤ 400 * (n:ℝ) := hNL
    have hdiv : (Real.log n)^2 ≤ 400 * (n:ℝ) / 1048576 := (le_div_iff₀ hNpos).mpr hNL'
    calc (Real.log n)^2 ≤ 400 * (n:ℝ) / 1048576 := hdiv
      _ = 400 * ((n:ℝ)/1048576) := by ring
  have h5 : Real.log (n:ℝ) ≤ 20 * ((n:ℝ)/1048576) := by
    have ht : (0:ℝ) ≤ (n:ℝ)/1048576 := by positivity
    have := mul_le_mul_of_nonneg_right hu_le ht
    linarith [htan, this]
  have hNnum : (882:ℝ)/1048576 ≤ 0.016 := by norm_num
  have ht : (0:ℝ) ≤ (n:ℝ)/1048576 := by positivity
  have hlog3 : (1.0986122885:ℝ) < Real.log 3 := Real.log_three_gt_d9
  nlinarith [h1, h2, h3, h4, h5, hNnum, ht, hnnonneg, hlog3]

open Finset

/-- Numeric inequality for the main estimate: for `n ≥ 4096`,
`K * log n + log n + log (n+1) + 1 + 1.0826 n ≤ n * log 3`, where `K = #{i ≤ n : syl i ≤ n}` is the
number of Sylvester terms `syl i ≤ n` (`syl` is defined in
`Submission/Work/BW/ulcm_le_three_pow.lean`: `syl 0 = 2`, `syl (n+1) = syl n * (syl n - 1) + 1`).

Route.  `K ≤ 5` for `n < 3263443` (since `syl 0,1,2,3,4 = 2,3,7,43,1807` and `syl 5 = 3263443`), and
in general `K ≤ log₂ n + 1` because `syl i ≥ 2 ^ (i-1)` for `i ≥ 1`.  Hence it suffices to prove
`5 log n + log n + log (n+1) + 1 + 1.0826 n ≤ n log 3` on `[4096, 3263443)` and
`(log₂ n + 1) log n + log n + log (n+1) + 1 + 1.0826 n ≤ n log 3` for `n ≥ 3263443`; in both regimes
the gap `n log 3 - (… )` has a positive increment, so a single check at the left endpoint of each
regime suffices, using only `log 2 ≤ 0.6932` and `log 3 ≥ 1.0986`
(`Real.log_le_iff_le_exp`, `Real.sum_le_exp_of_nonneg`, `Real.log_two_lt_d9` may help). -/
theorem num_syl_ineq (n : ℕ) (hn : 4096 ≤ n) :
    (((Finset.range (n + 1)).filter (fun i => syl i ≤ n)).card : ℝ) * Real.log n
      + Real.log n + Real.log (n + 1) + 1 + n * 1.0826 ≤ n * Real.log 3 := by
  set K : ℕ := ((Finset.range (n + 1)).filter (fun i => syl i ≤ n)).card with hK
  have hn1 : 1 ≤ n := by omega
  have hlogpos : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  rcases lt_or_ge n 1048576 with hlt | hge
  · -- regime 1: `K ≤ 5`
    have hK5 : K ≤ 5 := syl_card_le_five n (by omega)
    have hK5r : (K : ℝ) ≤ 5 := by exact_mod_cast hK5
    have hmul : (K : ℝ) * Real.log n ≤ 5 * Real.log n :=
      mul_le_mul_of_nonneg_right hK5r hlogpos
    have hr := num_regime1 n hn
    linarith [hmul, hr]
  · -- regime 2: `K ≤ log₂ n + 1`
    have hKl : (K : ℝ) ≤ Real.log n / Real.log 2 + 1 := by
      rw [hK]; exact syl_card_le_log n
    have hmul : (K : ℝ) * Real.log n ≤ (Real.log n / Real.log 2 + 1) * Real.log n :=
      mul_le_mul_of_nonneg_right hKl hlogpos
    have hr := num_regime2 n hge
    have hid : (Real.log n / Real.log 2 + 1) * Real.log n
        = (Real.log n) ^ 2 / Real.log 2 + Real.log n := by ring
    linarith [hmul, hr, hid.le, hid.ge]


/-! ## Inlined proof of the delegated entropy (size) bound -/

/-! # Notation for the Sylvester entropy bound

The index set `Kset n = {i ≤ n : syl i ≤ n}` (an initial segment of `ℕ`, since `syl` is strictly
increasing) and the floor sum `Ssum n = ∑_{i ∈ Kset n} n / syl i` that the proof of
`Work.BW.syl_entropy_bound` controls. -/


open Finset

/-- The index set `{i ≤ n : syl i ≤ n}`. -/
def Kset (n : ℕ) : Finset ℕ := (Finset.range (n + 1)).filter (fun i => syl i ≤ n)

/-- `Ssum n = ∑_{i ∈ Kset n} n / syl i`. -/
def Ssum (n : ℕ) : ℕ := ∑ i ∈ Kset n, n / syl i

@[simp] lemma mem_Kset {n i : ℕ} : i ∈ Kset n ↔ i ≤ n ∧ syl i ≤ n := by
  simp [Kset, Nat.lt_succ_iff]

lemma Lw_eq_Kset (n : ℕ) :
    Lw n = ∑ i ∈ Kset n, Real.log (syl i) / (syl i) := rfl

/-- `Kset n` is downward closed. -/
lemma Kset_downclosed {n i j : ℕ} (hi : i ∈ Kset n) (hj : j ≤ i) : j ∈ Kset n := by
  rw [mem_Kset] at hi ⊢
  exact ⟨le_trans hj hi.1, le_trans (syl_mono hj) hi.2⟩

/-! # The logarithm of `sylBlocks`

`sylBlocks n = ∏_{i ≤ n} (n / syl i)!` is a product over *all* indices `i ≤ n`, while the sum in
`Work.BW.Lw` runs only over `Kset n = {i ≤ n : syl i ≤ n}`.  The two agree because the extra
factors are trivial: if `syl i > n` then `n / syl i = 0` and `0! = 1`, so `log 1 = 0`.

This file records that identity:

  `log (sylBlocks n) = ∑_{i ∈ Kset n} log ((n / syl i)!)`. -/


open Finset

lemma log_sylBlocks_eq (n : ℕ) :
    Real.log (sylBlocks n : ℝ) = ∑ i ∈ Kset n, Real.log ((n / syl i).factorial : ℝ) := by
  -- every factor of the product is a nonzero (real) factorial
  have hpos : ∀ i : ℕ, ((n / syl i).factorial : ℝ) ≠ 0 := fun i => by
    exact_mod_cast Nat.factorial_ne_zero (n / syl i)
  -- rewrite `sylBlocks` as a product of real factorials
  have hcast : (sylBlocks n : ℝ) = ∏ i ∈ Finset.range (n + 1),
      ((n / syl i).factorial : ℝ) := by
    rw [sylBlocks, Nat.cast_prod]
  -- turn the log of the product into a sum of logs
  rw [hcast, Real.log_prod (fun i _ => hpos i)]
  -- and drop the terms with `syl i > n`, which are `log 1 = 0`
  refine (Finset.sum_subset ?hsub ?hzero).symm
  · intro x hx
    rw [Kset, Finset.mem_filter] at hx
    exact hx.1
  · intro x hx hxn
    rw [Finset.mem_range, Nat.lt_succ_iff] at hx
    have hsyl : n < syl x := by
      by_contra hcon
      exact hxn (by
        rw [Kset, Finset.mem_filter]
        exact ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hx), not_lt.mp hcon⟩)
    rw [Nat.div_eq_of_lt hsyl, Nat.factorial_zero, Nat.cast_one, Real.log_one]

lemma per_term_log_factorial (n i : ℕ) (hi : i ∈ Kset n) :
    ((n / syl i : ℕ) : ℝ) * (Real.log n - Real.log (syl i))
      - ((n : ℝ) / (syl i : ℝ) - ((n / syl i : ℕ) : ℝ))
      - ((n / syl i : ℕ) : ℝ) + 1
    ≤ Real.log ((n / syl i).factorial : ℝ) := by
  rw [mem_Kset] at hi
  obtain ⟨hin, hsin⟩ := hi
  have hspos : (0:ℕ) < syl i := by have := syl_two_le i; omega
  have hm1 : 1 ≤ n / syl i := by
    rw [Nat.one_le_div_iff hspos]; exact hsin
  set m := n / syl i with hm
  set x := (n:ℝ)/(syl i:ℝ) with hx
  have hmpos : (0:ℝ) < (m:ℝ) := by
    have : (0:ℕ) < m := by omega
    exact_mod_cast this
  have hmne : (m:ℝ) ≠ 0 := ne_of_gt hmpos
  have hnne : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsne : ((syl i : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hxne : x ≠ 0 := by rw [hx]; exact div_ne_zero hnne hsne
  have hxm : (m:ℝ) ≤ x := by rw [hx, hm]; exact Nat.cast_div_le
  have hlogx : Real.log x = Real.log (n:ℝ) - Real.log ((syl i:ℕ):ℝ) := by
    rw [hx]; exact Real.log_div hnne hsne
  rw [← hlogx]
  have hsplit : (m:ℝ) * Real.log x
      = (m:ℝ) * Real.log (m:ℝ) + (m:ℝ) * Real.log (x/(m:ℝ)) := by
    have hxx : Real.log x = Real.log (m:ℝ) + Real.log (x/(m:ℝ)) := by
      have h := Real.log_mul hmne (div_ne_zero hxne hmne)
      rw [mul_div_cancel₀ x hmne] at h
      exact h
    rw [hxx]; ring
  have hlast : (m:ℝ) * Real.log (x/(m:ℝ)) - (x - (m:ℝ)) ≤ 0 := by
    have hlog1 : Real.log (1 + (x - (m:ℝ))/(m:ℝ)) ≤ (x - (m:ℝ))/(m:ℝ) := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + (x-(m:ℝ))/(m:ℝ) by
        have : (0:ℝ) ≤ (x - (m:ℝ))/(m:ℝ) := div_nonneg (by linarith) (le_of_lt hmpos)
        linarith)
      linarith
    have hxmm : x/(m:ℝ) = 1 + (x - (m:ℝ))/(m:ℝ) := by field_simp; ring
    rw [hxmm]
    have h1 := mul_le_mul_of_nonneg_left hlog1 (le_of_lt hmpos)
    have hcancel : (m:ℝ) * ((x - (m:ℝ))/(m:ℝ)) = x - (m:ℝ) := mul_div_cancel₀ _ hmne
    linarith
  calc (m:ℝ) * Real.log x - (x - (m:ℝ)) - (m:ℝ) + 1
      = ((m:ℝ) * Real.log (m:ℝ) - (m:ℝ) + 1)
        + ((m:ℝ) * Real.log (x/(m:ℝ)) - (x - (m:ℝ))) := by rw [hsplit]; ring
    _ ≤ Real.log (m.factorial:ℝ) + 0 := add_le_add (log_factorial_ge m hm1) hlast
    _ = Real.log (m.factorial:ℝ) := by ring

open Finset

/-- Each floor `n / syl i` is at most the real quotient `n / syl i`, and `log (syl i) ≥ 0`
(`syl i ≥ 2`), so termwise
`(n / syl i) · log (syl i) ≤ n · (log (syl i) / syl i)`; summing over `Kset n` gives the claim,
since `Lw n = ∑_{i ∈ Kset n} log (syl i) / syl i`. -/
lemma sum_div_mul_log_syl_le (n : ℕ) :
    ∑ i ∈ Kset n, ((n / syl i : ℕ) : ℝ) * Real.log (syl i) ≤ (n : ℝ) * Lw n := by
  rw [Lw_eq_Kset, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hlog : 0 ≤ Real.log (syl i : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by have := syl_two_le i; omega : 1 ≤ syl i))
  calc ((n / syl i : ℕ) : ℝ) * Real.log (syl i)
      ≤ ((n : ℝ) / (syl i : ℝ)) * Real.log (syl i) :=
        mul_le_mul_of_nonneg_right Nat.cast_div_le hlog
    _ = (n : ℝ) * (Real.log (syl i) / (syl i : ℝ)) := by ring

open Finset

/-- The fractional part `a / k - ⌊a / k⌋` of the quotient of two naturals is `< 1`:
writing `a = k * (a / k) + a % k` (`Nat.div_add_mod`) and recalling `a % k < k`. -/
lemma cast_div_frac_lt_one (a k : ℕ) :
    (a : ℝ) / (k : ℝ) - ((a / k : ℕ) : ℝ) < 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hmodR : ((a % k : ℕ) : ℝ) < (k : ℝ) := by
      exact_mod_cast Nat.mod_lt a hk
    have hdecomp : (a : ℝ) = (k : ℝ) * ((a / k : ℕ) : ℝ) + ((a % k : ℕ) : ℝ) := by
      have h := Nat.div_add_mod a k
      have h2 : ((k * (a / k) + a % k : ℕ) : ℝ) = (a : ℝ) := by rw [h]
      push_cast at h2
      linarith [h2]
    have hsplit : (a : ℝ) / (k : ℝ) = ((a / k : ℕ) : ℝ) + ((a % k : ℕ) : ℝ) / (k : ℝ) := by
      rw [hdecomp, add_div, mul_div_cancel_left₀ _ (ne_of_gt hkR)]
    rw [hsplit]
    have : ((a % k : ℕ) : ℝ) / (k : ℝ) < 1 := by
      rw [div_lt_one hkR]; exact hmodR
    linarith

lemma sum_frac_le_card (n : ℕ) :
    ∑ i ∈ Kset n, ((n : ℝ) / (syl i : ℝ) - ((n / syl i : ℕ) : ℝ)) ≤ ((Kset n).card : ℝ) := by
  calc ∑ i ∈ Kset n, ((n : ℝ) / (syl i : ℝ) - ((n / syl i : ℕ) : ℝ))
      ≤ ∑ _i ∈ Kset n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => le_of_lt (cast_div_frac_lt_one n (syl i))
    _ = ((Kset n).card : ℝ) := by simp

open Finset

private lemma syl_pos_aux (i : ℕ) : 0 < syl i := by
  have := syl_two_le i; omega

/-- `Kset n` is an initial segment of `ℕ`: it equals `Finset.range (Kset n).card`. -/
lemma Kset_eq_range_aux (n : ℕ) : Kset n = Finset.range (Kset n).card := by
  set I := Kset n with hI
  have hmem : ∀ i, i ∈ I ↔ i ≤ n ∧ syl i ≤ n := fun i => by rw [hI]; exact mem_Kset
  have hsub : I ⊆ Finset.range I.card := by
    intro i hi
    have hi' : i ≤ n ∧ syl i ≤ n := (hmem i).mp hi
    rw [Finset.mem_range]
    by_contra hcon
    push_neg at hcon
    have h1 : Finset.range (i + 1) ⊆ I := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [hmem]
      exact ⟨by omega, le_trans (syl_mono (by omega)) hi'.2⟩
    have h2 := Finset.card_le_card h1
    rw [Finset.card_range] at h2
    omega
  exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_range])

/-- The Egyptian-fraction identity for the Sylvester sequence, over `ℝ`. -/
lemma syl_sum_inv_real_aux (m : ℕ) :
    (∑ i ∈ Finset.range m, (1 : ℝ) / (syl i : ℝ)) = 1 - 1 / ((syl m : ℝ) - 1) := by
  induction m with
  | zero => norm_num [syl_zero]
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have h2 : 2 ≤ syl m := syl_two_le m
      have hcast : ((syl (m + 1) : ℕ) : ℝ) - 1 = (syl m : ℝ) * ((syl m : ℝ) - 1) := by
        rw [syl_succ]
        push_cast [Nat.cast_sub (show 1 ≤ syl m by omega)]
        ring
      have hne : (syl m : ℝ) - 1 ≠ 0 := by
        have h3 : (2 : ℝ) ≤ (syl m : ℝ) := by exact_mod_cast h2
        intro h; linarith
      rw [hcast]
      field_simp
      ring

lemma Ssum_ge (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) - (1 + (Kset n).card) ≤ (Ssum n : ℝ) := by
  classical
  set I : Finset ℕ := Kset n with hI
  set k : ℕ := I.card with hk
  have hIrange : I = Finset.range k := by
    have h := Kset_eq_range_aux n
    rw [← hI] at h
    rw [← hk] at h
    exact h
  have hmem : ∀ i, i ∈ I ↔ i ≤ n ∧ syl i ≤ n := fun i => by rw [hI]; exact mem_Kset
  -- `Ssum n`, cast to `ℝ`, is the sum of the floors `n / syl i`.
  have hsum_eq : ((Ssum n : ℕ) : ℝ) = ∑ i ∈ I, ((n / syl i : ℕ) : ℝ) := by
    rw [Ssum, hI]
    push_cast
    rfl
  -- Termwise: `n / syl i - 1 ≤ ⌊n / syl i⌋`.
  have hfloor : ∀ i ∈ I, (n : ℝ) / (syl i : ℝ) - 1 ≤ ((n / syl i : ℕ) : ℝ) := by
    intro i _
    have hs : 0 < syl i := syl_pos_aux i
    have hsi : (0 : ℝ) < (syl i : ℝ) := by exact_mod_cast hs
    have hmod : n % syl i < syl i := Nat.mod_lt n hs
    have hdecomp : (n : ℝ) = (syl i : ℝ) * ((n / syl i : ℕ) : ℝ) + ((n % syl i : ℕ) : ℝ) := by
      have h := Nat.div_add_mod n (syl i)
      have h' : (n : ℝ) = ((syl i * (n / syl i) + n % syl i : ℕ) : ℝ) := by rw [h]
      push_cast at h'
      exact h'
    have hlt : ((n % syl i : ℕ) : ℝ) < (syl i : ℝ) := by exact_mod_cast hmod
    have hle : (n : ℝ) / (syl i : ℝ) ≤ ((n / syl i : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hsi]
      nlinarith [hdecomp, hlt]
    linarith
  have hstep1 : ∑ i ∈ I, ((n : ℝ) / (syl i : ℝ) - 1) ≤ (Ssum n : ℝ) := by
    rw [hsum_eq]
    exact Finset.sum_le_sum hfloor
  -- Evaluate the left-hand sum.
  have hsum_inv : (∑ i ∈ I, (1 : ℝ) / (syl i : ℝ)) = 1 - 1 / ((syl k : ℝ) - 1) := by
    rw [hIrange]
    exact syl_sum_inv_real_aux k
  have hconst : (∑ _i ∈ I, (1 : ℝ)) = (k : ℝ) := by
    rw [Finset.sum_const, hk]
    simp
  have hsplit : (∑ i ∈ I, ((n : ℝ) / (syl i : ℝ) - 1))
      = (n : ℝ) * (1 - 1 / ((syl k : ℝ) - 1)) - (k : ℝ) := by
    rw [Finset.sum_sub_distrib, ← hsum_inv, ← hconst, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_one_div]
  -- `n + 1 ≤ syl k`.
  have hnsyl : n + 1 ≤ syl k := by
    have hk_notin : k ∉ I := by rw [hIrange]; simp
    have hnot : n < k ∨ n < syl k := by
      by_contra hcon
      push_neg at hcon
      exact hk_notin ((hmem k).mpr hcon)
    rcases hnot with h | h
    · have := syl_ge k; omega
    · omega
  have hdenpos : (0 : ℝ) < (syl k : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (syl k : ℝ) := by exact_mod_cast syl_two_le k
    linarith
  have hdiv1 : (n : ℝ) / ((syl k : ℝ) - 1) ≤ 1 := by
    rw [div_le_one hdenpos]
    have h3 : (n : ℝ) + 1 ≤ (syl k : ℝ) := by exact_mod_cast hnsyl
    linarith
  have hmain : (n : ℝ) - (1 + (k : ℝ)) ≤ (Ssum n : ℝ) := by
    have h1 := hstep1
    rw [hsplit] at h1
    have heq : (n : ℝ) * (1 - 1 / ((syl k : ℝ) - 1)) - (k : ℝ)
        = (n : ℝ) - (n : ℝ) / ((syl k : ℝ) - 1) - (k : ℝ) := by
      field_simp
    linarith [h1, hdiv1]
  exact hmain

open Finset

/-- `Ssum n = ∑_{i ∈ Kset n} ⌊n / syl i⌋ ≤ n`, where `Kset n = {i ≤ n : syl i ≤ n}`.

This is the easy half of the Sylvester entropy estimate: the floor lemma
`Work.BW.syl_div_sum_le` gives `∑_{i ≤ n} ⌊n / syl i⌋ + 1 ≤ n`, and `Kset n` is a subset of
`Finset.range (n + 1)`, so restricting the sum to `Kset n` can only decrease it. -/
lemma Ssum_le (n : ℕ) : (Ssum n : ℝ) ≤ (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [Ssum]
  · -- `Kset n ⊆ Finset.range (n + 1)`
    have hsub : Kset n ⊆ Finset.range (n + 1) := by
      intro i hi
      rw [mem_Kset] at hi
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hi.1)
    -- Restricting the sum to `Kset n` only decreases it.
    have hle : Ssum n ≤ ∑ i ∈ Finset.range (n + 1), n / syl i := by
      rw [Ssum]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Nat.zero_le _)
    -- The full floor sum is at most `n - 1`.
    have hkey := syl_div_sum_le (m := n) (N := n) hn le_rfl
    have hbound : (∑ i ∈ Finset.range (n + 1), n / syl i) ≤ n := by omega
    exact_mod_cast le_trans hle hbound

open Finset

/-- Splitting a sum of the expression `P i - Q i - R i - S i + 1` into the constituent sums. -/
private lemma sum_split_four {ι : Type*} (s : Finset ι) (P Q R S : ι → ℝ) :
    (∑ i ∈ s, (P i - Q i - R i - S i + 1))
      = (∑ i ∈ s, P i) - (∑ i ∈ s, Q i) - (∑ i ∈ s, R i) - (∑ i ∈ s, S i)
        + (s.card : ℝ) := by
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The lower bound on `log (sylBlocks n)` feeding the entropy bound:
`S n · log n - n · Lw n - S n ≤ log (sylBlocks n)`, where `S n = ∑_{i ∈ Kset n} n / syl i`. -/
lemma log_sylBlocks_ge (n : ℕ) :
    (Ssum n : ℝ) * Real.log n - (n : ℝ) * Lw n - (Ssum n : ℝ)
      ≤ Real.log (sylBlocks n : ℝ) := by
  rw [log_sylBlocks_eq n]
  have hpoint : ∀ i ∈ Kset n,
      ((n / syl i : ℕ) : ℝ) * Real.log n - ((n / syl i : ℕ) : ℝ) * Real.log (syl i)
        - ((n : ℝ) / (syl i : ℝ) - ((n / syl i : ℕ) : ℝ))
        - ((n / syl i : ℕ) : ℝ) + 1 ≤ Real.log ((n / syl i).factorial : ℝ) := by
    intro i hi
    have h := per_term_log_factorial n i hi
    have heq : ((n / syl i : ℕ) : ℝ) * (Real.log n - Real.log (syl i))
        = ((n / syl i : ℕ) : ℝ) * Real.log n
          - ((n / syl i : ℕ) : ℝ) * Real.log (syl i) := by ring
    rw [heq] at h
    exact h
  have hsum_le : (∑ i ∈ Kset n,
        (((n / syl i : ℕ) : ℝ) * Real.log n - ((n / syl i : ℕ) : ℝ) * Real.log (syl i)
          - ((n : ℝ) / (syl i : ℝ) - ((n / syl i : ℕ) : ℝ))
          - ((n / syl i : ℕ) : ℝ) + 1))
      ≤ ∑ i ∈ Kset n, Real.log ((n / syl i).factorial : ℝ) :=
    Finset.sum_le_sum hpoint
  have h2 : (∑ i ∈ Kset n,
        (((n / syl i : ℕ) : ℝ) * Real.log n - ((n / syl i : ℕ) : ℝ) * Real.log (syl i)
          - ((n : ℝ) / (syl i : ℝ) - ((n / syl i : ℕ) : ℝ))
          - ((n / syl i : ℕ) : ℝ) + 1))
      = (Ssum n : ℝ) * Real.log n
        - (∑ i ∈ Kset n, ((n / syl i : ℕ) : ℝ) * Real.log (syl i))
        - (∑ i ∈ Kset n, ((n : ℝ) / (syl i : ℝ) - ((n / syl i : ℕ) : ℝ)))
        - (Ssum n : ℝ) + ((Kset n).card : ℝ) := by
    rw [sum_split_four (Kset n)
      (fun i => ((n / syl i : ℕ) : ℝ) * Real.log n)
      (fun i => ((n / syl i : ℕ) : ℝ) * Real.log (syl i))
      (fun i => ((n : ℝ) / (syl i : ℝ) - ((n / syl i : ℕ) : ℝ)))
      (fun i => ((n / syl i : ℕ) : ℝ))]
    have hS : ((Ssum n : ℕ) : ℝ) = ∑ i ∈ Kset n, ((n / syl i : ℕ) : ℝ) := by
      simp [Ssum]
    rw [← Finset.sum_mul]
    simp only [← hS]
  have h4 := sum_div_mul_log_syl_le n
  have h5 := sum_frac_le_card n
  have hX : (Ssum n : ℝ) * Real.log n - (n : ℝ) * Lw n - (Ssum n : ℝ)
      ≤ (Ssum n : ℝ) * Real.log n
        - (∑ i ∈ Kset n, ((n / syl i : ℕ) : ℝ) * Real.log (syl i))
        - (∑ i ∈ Kset n, ((n : ℝ) / (syl i : ℝ) - ((n / syl i : ℕ) : ℝ)))
        - (Ssum n : ℝ) + ((Kset n).card : ℝ) := by
    linarith [h4, h5]
  rw [← h2] at hX
  exact le_trans hX hsum_le

/-- **The size bound for Hanson's multinomial-type integer**: with
`sylBlocks n = ∏_{i ≤ n} (n / syl i)!` (`syl` Sylvester's sequence) and
`Lw n = ∑_{syl i ≤ n} log (syl i)/syl i` (both defined in `Submission/Work/BW/ulcm_le_three_pow.lean`),
for `n ≥ 1`
`log (n!/sylBlocks n) ≤ log n + log (n+1) + 1 + n * Lw n + K * log n`,
where `K = #{i ≤ n : syl i ≤ n}` is the number of Sylvester terms not exceeding `n`.

Route.  `log n! ≤ n log n - n + log (n+1) + 1` (proved in the same workspace from
`∑_{i<n} log (i+1) ≤ (n+1) log (n+1) - n`) and `log m! ≥ m log m - m + 1` for `m ≥ 1`
(`Work.BW.log_factorial_ge`).  Writing `m_i = n / syl i` (so `m_i = 0` for `syl i > n`) and
`r = n - ∑_i m_i`, concavity of `log` (`log u - log v ≤ (u - v)/v` for `0 < v ≤ u`) gives
`m_i log m_i ≥ m_i (log n - log (syl i)) - (n/syl i - m_i)`.  Hence
`log (n!/sylBlocks n) ≤ r log n + log (n+1) + 1 + ∑_i m_i log (syl i) + ∑_{m_i ≥ 1} (n/syl i - m_i) - K`,
the last sum `- K` is `≤ 0` (each fractional part is `< 1`), and
`∑_i m_i log (syl i) ≤ ∑_{syl i ≤ n} (n/syl i) log (syl i) = n * Lw n`.
Finally `r ≤ 1 + K`: `∑_{i: syl i ≤ n} 1/syl i = 1 - 1/(syl (K+1) - 1)` with `syl (K+1) - 1 ≥ n`
(use `Work.BW.syl_sum_inv_lt_one`, `Work.BW.syl_prod`), so `∑_{i: syl i ≤ n} n/syl i ≥ n - 1`, and
each floor `n / syl i` loses at most `1`.  (The naive claim `r ≤ 1` is FALSE: at `n = 5`, `r = 2`.) -/
theorem syl_entropy_bound (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((Nat.factorial n : ℝ) / (sylBlocks n : ℝ)) ≤
      Real.log n + Real.log (n + 1) + 1 + n * Lw n
        + (((Finset.range (n + 1)).filter (fun i => syl i ≤ n)).card : ℝ) * Real.log n := by
  show Real.log ((Nat.factorial n : ℝ) / (sylBlocks n : ℝ)) ≤
      Real.log n + Real.log (n + 1) + 1 + (n : ℝ) * Lw n
        + ((Kset n).card : ℝ) * Real.log n
  have hfac_nz : (Nat.factorial n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hblk_nz : (sylBlocks n : ℝ) ≠ 0 := by
    have h : 0 < sylBlocks n := by
      rw [sylBlocks]
      exact Finset.prod_pos (fun i _ => Nat.factorial_pos _)
    exact_mod_cast h.ne'
  have hlog := Real.log_div hfac_nz hblk_nz
  have hfac := log_factorial_le' n hn
  have hblk := log_sylBlocks_ge n
  have hS := Ssum_ge n hn
  have hSle := Ssum_le n
  have hnlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hX0 : 0 ≤ (n : ℝ) - (Ssum n : ℝ) := by linarith
  have hXK : (n : ℝ) - (Ssum n : ℝ) ≤ 1 + ((Kset n).card : ℝ) := by linarith
  calc
    Real.log ((Nat.factorial n : ℝ) / (sylBlocks n : ℝ))
        = Real.log (Nat.factorial n : ℝ) - Real.log (sylBlocks n : ℝ) := hlog
    _ ≤ ((n : ℝ) * Real.log n - n + Real.log (n + 1) + 1)
          - ((Ssum n : ℝ) * Real.log n - (n : ℝ) * Lw n - (Ssum n : ℝ)) := by
          linarith [hfac, hblk]
    _ = ((n : ℝ) - (Ssum n : ℝ)) * Real.log n - ((n : ℝ) - (Ssum n : ℝ))
          + (n : ℝ) * Lw n + Real.log (n + 1) + 1 := by ring
    _ ≤ ((n : ℝ) - (Ssum n : ℝ)) * Real.log n + (n : ℝ) * Lw n + Real.log (n + 1) + 1 := by
          linarith [hX0]
    _ ≤ (1 + ((Kset n).card : ℝ)) * Real.log n + (n : ℝ) * Lw n + Real.log (n + 1) + 1 := by
          have hml := mul_le_mul_of_nonneg_right hXK hnlog
          linarith [hml]
    _ = Real.log n + Real.log (n + 1) + 1 + (n : ℝ) * Lw n
          + ((Kset n).card : ℝ) * Real.log n := by ring

/-! ## The finitely many small cases (kernel-checked) -/

/-- `ulcmChk fuel k l p` checks `l ≤ p` and recurses with `lcm(l, k+1)`, `3p`; started at
`l = ulcm k`, `p = 3^k` it certifies `lcm(1..j) ≤ 3^j` for `k ≤ j < k + fuel`. -/
def ulcmChk : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _ => true
  | fuel + 1, k, l, p => Nat.ble l p && ulcmChk fuel (k + 1) (Nat.lcm l (k + 1)) (3 * p)

theorem ulcm_succ_lcm (k : ℕ) : ulcm (k + 1) = Nat.lcm (ulcm k) (k + 1) := by
  rw [ulcm, ulcm, Finset.range_add_one, Finset.lcm_insert]
  exact Nat.lcm_comm _ _

theorem ulcmChk_sound : ∀ (fuel k : ℕ), ulcmChk fuel k (ulcm k) (3 ^ k) = true →
    ∀ j, k ≤ j → j < k + fuel → ulcm j ≤ 3 ^ j := by
  intro fuel
  induction fuel with
  | zero => intro k _ j h1 h2; omega
  | succ n ih =>
    intro k h j h1 h2
    simp only [ulcmChk, Bool.and_eq_true, Nat.ble_eq] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact h.1
    · have h' : ulcmChk n (k + 1) (ulcm (k + 1)) (3 ^ (k + 1)) = true := by
        rw [ulcm_succ_lcm, pow_succ, mul_comm]; exact h.2
      exact ih (k + 1) h' j hlt (by omega)

theorem ulcmChk_4096 : ulcmChk 4096 0 1 1 = true := by decide +kernel

/-- For `k < 4096`, `lcm(1,…,k) ≤ 3^k` (kernel check). -/
theorem ulcm_le_three_pow_small (j : ℕ) (hj : j < 4096) : ulcm j ≤ 3 ^ j :=
  ulcmChk_sound 4096 0 (by simpa [ulcm] using ulcmChk_4096) j (Nat.zero_le _) (by omega)

/-! ## The theorem -/

/-- BW §12: `u(k) = lcm(1,…,k) ≤ 3^k` (Hanson 1972; BW cite Yu). Shared with `aux_poly`; the `4^k` bound in the workspace is not enough for (13). -/
theorem ulcm_le_three_pow (k : ℕ) : (ulcm k : ℝ) ≤ 3 ^ k := by
  rcases lt_or_ge k 4096 with hk | hk
  · -- finitely many small cases, checked in the kernel
    have h := ulcm_le_three_pow_small k hk
    have : ((ulcm k : ℕ) : ℝ) ≤ ((3 ^ k : ℕ) : ℝ) := by exact_mod_cast h
    simpa using this
  · -- Hanson's multinomial argument
    have hMpos : 0 < sylBlocks k := by
      rw [sylBlocks]
      exact Finset.prod_pos fun i _ => Nat.factorial_pos _
    have hdvd_raw : ulcm k * sylBlocks k ∣ k.factorial := syl_divisibility k
    have hdvd : sylBlocks k ∣ k.factorial := (dvd_mul_left (sylBlocks k) (ulcm k)).trans hdvd_raw
    have hle : ulcm k ≤ k.factorial / sylBlocks k := by
      rw [Nat.le_div_iff_mul_le hMpos]
      exact Nat.le_of_dvd (Nat.factorial_pos k) hdvd_raw
    have hcast : ((k.factorial / sylBlocks k : ℕ) : ℝ) = (k.factorial : ℝ) / (sylBlocks k : ℝ) :=
      Nat.cast_div hdvd (by positivity)
    have hcastle : (ulcm k : ℝ) ≤ (k.factorial : ℝ) / (sylBlocks k : ℝ) := by
      rw [← hcast]; exact_mod_cast hle
    have hlog1 : Real.log (ulcm k : ℝ) ≤ Real.log ((k.factorial : ℝ) / (sylBlocks k : ℝ)) :=
      Real.log_le_log (by exact_mod_cast ulcm_pos k) hcastle
    have hlog2 : Real.log ((k.factorial : ℝ) / (sylBlocks k : ℝ)) ≤
        Real.log k + Real.log (k + 1) + 1 + k * Lw k
          + (((Finset.range (k + 1)).filter (fun i => syl i ≤ k)).card : ℝ) * Real.log k := by
      exact syl_entropy_bound k (by omega)
    have hlog3 : Real.log ((k.factorial : ℝ) / (sylBlocks k : ℝ)) ≤ k * Real.log 3 := by
      have hL : Lw k ≤ 1.0826 := syl_log_facts.2.2.2 k
      have hnum := num_syl_ineq k hk
      have hLk : (k:ℝ) * Lw k ≤ (k:ℝ) * 1.0826 :=
        mul_le_mul_of_nonneg_left hL (by positivity)
      linarith [hlog2, hLk, hnum]
    have hfinal : Real.log (ulcm k : ℝ) ≤ Real.log (3 ^ k : ℝ) := by
      rw [Real.log_pow]
      exact le_trans hlog1 hlog3
    exact (Real.log_le_log_iff (by exact_mod_cast ulcm_pos k) (by positivity)).mp hfinal

end Work.BW
