/-
# `Work.FIArea2.sum_tau_pow_le`

For every fixed `k` there is `C > 0` with `∑_{n ≤ X} τ(n)^k ≤ C·X·(log X + 2)^{2^k}`, where
`τ(n) = #(n.divisors)`.

The proof is the classical elementary "double induction on the logarithmic summatory function".
Write `S_m(X) = ∑_{n ≤ X} τ(n)^m` and `A_m(X) = ∑_{n ≤ X} τ(n)^m / n`.  Then

* `A_0(X) = H_X ≤ log X + 1`,
* `A_{m+1}(X) ≤ A_m(X)^2`,
* `S_{m+1}(X) ≤ X·A_m(X)^2`,

whence `A_m(X) ≤ (log X + 1)^{2^m}` and `S_k(X) ≤ X (log X + 2)^{2^k}`.  The two arithmetic
inputs are the sub-multiplicativity `τ(mn) ≤ τ(m)τ(n)` of the divisor function and the elementary
regrouping identity `∑_{n ≤ X} τ(n)·g(n) = ∑_{d ≤ X} ∑_{m ≤ X/d} g(d·m)`.
-/
import Mathlib

namespace Work.FIArea2

open Finset

noncomputable section

/-- `τ(n) = #(n.divisors)`, viewed as a real number. -/
def tauR (n : ℕ) : ℝ := (n.divisors.card : ℝ)

lemma tauR_nonneg (n : ℕ) : 0 ≤ tauR n := Nat.cast_nonneg _

/-- Sub-multiplicativity of the divisor function: for all `m n`, `τ(mn) ≤ τ(m)τ(n)`. -/
lemma tauR_mul_le (m n : ℕ) : tauR (m * n) ≤ tauR m * tauR n := by
  have h : (m * n).divisors.card ≤ m.divisors.card * n.divisors.card := by
    rw [Nat.divisors_mul]
    exact Finset.card_mul_le
  have h' : (((m * n).divisors.card : ℕ) : ℝ) ≤ ((m.divisors.card * n.divisors.card : ℕ) : ℝ) := by
    exact_mod_cast h
  simpa [tauR, Nat.cast_mul] using h'

/-- For `n ∈ [1,X]` the divisors of `n` are exactly the elements of `[1,X]` that divide `n`. -/
lemma divisors_eq_filter_Icc {n X : ℕ} (hn : n ∈ Icc 1 X) :
    n.divisors = (Icc 1 X).filter (fun d => d ∣ n) := by
  have hn0 : n ≠ 0 := by
    have := (mem_Icc.mp hn).1
    omega
  ext d
  rw [Nat.mem_divisors, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hdvd, _⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn0),
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd).trans (mem_Icc.mp hn).2⟩, hdvd⟩
  · rintro ⟨⟨hd1, hd2⟩, hdvd⟩
    exact ⟨hdvd, hn0⟩

/-- The multiples of `d` in `[1,X]` are exactly `d·m` for `m ∈ [1, X/d]`. -/
lemma image_mul_Icc_eq_filter {d X : ℕ} (hd : 1 ≤ d) :
    ((Icc 1 (X / d)).image (fun m => d * m)) = (Icc 1 X).filter (fun n => d ∣ n) := by
  ext n
  simp only [mem_image, mem_Icc, mem_filter]
  constructor
  · rintro ⟨m, ⟨hm1, hm2⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, ⟨m, rfl⟩⟩
    · nlinarith [hm1, hd]
    · calc d * m ≤ d * (X / d) := Nat.mul_le_mul_left d hm2
        _ ≤ X := Nat.mul_div_le X d
  · rintro ⟨⟨hn1, hn2⟩, hdvd⟩
    refine ⟨n / d, ⟨?_, ?_⟩, Nat.mul_div_cancel' hdvd⟩
    · rw [Nat.one_le_div_iff (by omega)]
      exact Nat.le_of_dvd (by omega) hdvd
    · exact Nat.div_le_div_right hn2

/-- Regrouping identity: `∑_{n ≤ X} τ(n)·g(n) = ∑_{d ≤ X} ∑_{m ≤ X/d} g(d·m)`. -/
lemma sum_tauR_mul (g : ℕ → ℝ) (X : ℕ) :
    ∑ n ∈ Icc 1 X, tauR n * g n
      = ∑ d ∈ Icc 1 X, ∑ m ∈ Icc 1 (X / d), g (d * m) := by
  have h1 : ∑ n ∈ Icc 1 X, tauR n * g n
      = ∑ n ∈ Icc 1 X, ∑ d ∈ (Icc 1 X).filter (fun d => d ∣ n), g n := by
    refine sum_congr rfl fun n hn => ?_
    rw [tauR, divisors_eq_filter_Icc hn, sum_const, nsmul_eq_mul]
  rw [h1]
  rw [show (∑ n ∈ Icc 1 X, ∑ d ∈ (Icc 1 X).filter (fun d => d ∣ n), g n)
        = ∑ n ∈ Icc 1 X, ∑ d ∈ Icc 1 X, (if d ∣ n then g n else 0) from by
      refine sum_congr rfl fun n hn => ?_
      rw [sum_filter]]
  rw [sum_comm]
  rw [show (∑ d ∈ Icc 1 X, ∑ n ∈ Icc 1 X, (if d ∣ n then g n else 0))
        = ∑ d ∈ Icc 1 X, ∑ n ∈ (Icc 1 X).filter (fun n => d ∣ n), g n from by
      refine sum_congr rfl fun d hd => ?_
      rw [sum_filter]]
  refine sum_congr rfl fun d hd => ?_
  have hd1 : 1 ≤ d := (mem_Icc.mp hd).1
  rw [← image_mul_Icc_eq_filter hd1]
  exact sum_image (fun a ha b hb hab => Nat.mul_left_cancel (by omega) hab)

/-- The logarithmic summatory function `A_m(X) = ∑_{n ≤ X} τ(n)^m / n`. -/
def Asum (m X : ℕ) : ℝ := ∑ n ∈ Icc 1 X, (tauR n) ^ m / (n : ℝ)

/-- The (plain) summatory function `S_m(X) = ∑_{n ≤ X} τ(n)^m`. -/
def Ssum (m X : ℕ) : ℝ := ∑ n ∈ Icc 1 X, (tauR n) ^ m

lemma Asum_nonneg (m X : ℕ) : 0 ≤ Asum m X :=
  sum_nonneg fun n _ => div_nonneg (pow_nonneg (tauR_nonneg n) m) (Nat.cast_nonneg n)

lemma Ssum_nonneg (m X : ℕ) : 0 ≤ Ssum m X :=
  sum_nonneg fun n _ => pow_nonneg (tauR_nonneg n) m

lemma Asum_mono {Y X : ℕ} (h : Y ≤ X) (m : ℕ) : Asum m Y ≤ Asum m X := by
  refine sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right h) ?_
  intro n hn hnnot
  exact div_nonneg (pow_nonneg (tauR_nonneg n) m) (Nat.cast_nonneg n)

lemma Asum_zero_eq_harmonic (X : ℕ) : Asum 0 X = (harmonic X : ℝ) := by
  rw [Asum, harmonic_eq_sum_Icc, Rat.cast_sum]
  refine sum_congr rfl fun n hn => ?_
  simp

lemma Asum_zero_le (X : ℕ) : Asum 0 X ≤ Real.log X + 1 := by
  rw [Asum_zero_eq_harmonic]
  have := harmonic_le_one_add_log X
  linarith

/-- `∑_{n ≤ Y} τ(n)^m ≤ Y · A_m(Y)`. -/
lemma Ssum_le_mul_Asum (m Y : ℕ) : Ssum m Y ≤ (Y : ℝ) * Asum m Y := by
  rw [Ssum, Asum, Finset.mul_sum]
  refine sum_le_sum fun n hn => ?_
  obtain ⟨hn1, hn2⟩ := mem_Icc.mp hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hcast : (n : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hn2
  have hA : 0 ≤ (tauR n) ^ m := pow_nonneg (tauR_nonneg n) m
  rw [← mul_div_assoc, le_div_iff₀ hnpos]
  calc (tauR n) ^ m * (n : ℝ) ≤ (tauR n) ^ m * (Y : ℝ) := mul_le_mul_of_nonneg_left hcast hA
    _ = (Y : ℝ) * (tauR n) ^ m := by ring

/-- `A_{m+1}(X) ≤ A_m(X)^2`. -/
lemma Asum_succ_le (m X : ℕ) : Asum (m + 1) X ≤ (Asum m X) ^ 2 := by
  have h1 : Asum (m + 1) X = ∑ n ∈ Icc 1 X, tauR n * (tauR n ^ m / (n : ℝ)) := by
    rw [Asum]
    refine sum_congr rfl fun n hn => ?_
    rw [pow_succ, mul_div_assoc]
    ring
  rw [h1, sum_tauR_mul (fun n => tauR n ^ m / (n : ℝ)) X]
  calc ∑ d ∈ Icc 1 X, ∑ m' ∈ Icc 1 (X / d), tauR (d * m') ^ m / ((d * m' : ℕ) : ℝ)
      ≤ ∑ d ∈ Icc 1 X, ∑ m' ∈ Icc 1 (X / d),
          (tauR d ^ m * tauR m' ^ m) / ((d : ℝ) * (m' : ℝ)) := by
        refine sum_le_sum fun d hd => sum_le_sum fun m' hm' => ?_
        have hp := pow_le_pow_left₀ (tauR_nonneg (d * m')) (tauR_mul_le d m') m
        rw [mul_pow] at hp
        rw [Nat.cast_mul]
        exact div_le_div_of_nonneg_right hp (by positivity)
      _ = ∑ d ∈ Icc 1 X, ∑ m' ∈ Icc 1 (X / d),
            (tauR d ^ m / (d : ℝ)) * (tauR m' ^ m / (m' : ℝ)) := by
        refine sum_congr rfl fun d hd => sum_congr rfl fun m' hm' => ?_
        rw [div_mul_div_comm]
      _ = ∑ d ∈ Icc 1 X, (tauR d ^ m / (d : ℝ)) * Asum m (X / d) := by
        refine sum_congr rfl fun d hd => ?_
        rw [Asum, Finset.mul_sum]
      _ ≤ ∑ d ∈ Icc 1 X, (tauR d ^ m / (d : ℝ)) * Asum m X := by
        refine sum_le_sum fun d hd => ?_
        refine mul_le_mul_of_nonneg_left (Asum_mono (Nat.div_le_self X d) m) ?_
        exact div_nonneg (pow_nonneg (tauR_nonneg d) m) (Nat.cast_nonneg d)
      _ = (Asum m X) ^ 2 := by
        rw [← Finset.sum_mul]
        have h2 : (∑ d ∈ Icc 1 X, tauR d ^ m / (d : ℝ)) = Asum m X := rfl
        rw [h2]
        ring

/-- `S_{m+1}(X) ≤ X · A_m(X)^2`. -/
lemma Ssum_succ_le (m X : ℕ) : Ssum (m + 1) X ≤ (X : ℝ) * (Asum m X) ^ 2 := by
  have h1 : Ssum (m + 1) X = ∑ n ∈ Icc 1 X, tauR n * tauR n ^ m := by
    rw [Ssum]
    refine sum_congr rfl fun n hn => ?_
    rw [pow_succ]
    ring
  rw [h1, sum_tauR_mul (fun n => tauR n ^ m) X]
  calc ∑ d ∈ Icc 1 X, ∑ m' ∈ Icc 1 (X / d), tauR (d * m') ^ m
      ≤ ∑ d ∈ Icc 1 X, ∑ m' ∈ Icc 1 (X / d), tauR d ^ m * tauR m' ^ m := by
        refine sum_le_sum fun d hd => sum_le_sum fun m' hm' => ?_
        calc tauR (d * m') ^ m ≤ (tauR d * tauR m') ^ m :=
              pow_le_pow_left₀ (tauR_nonneg (d * m')) (tauR_mul_le d m') m
          _ = tauR d ^ m * tauR m' ^ m := mul_pow _ _ _
      _ = ∑ d ∈ Icc 1 X, tauR d ^ m * Ssum m (X / d) := by
        refine sum_congr rfl fun d hd => ?_
        rw [Ssum, Finset.mul_sum]
      _ ≤ ∑ d ∈ Icc 1 X, tauR d ^ m * (((X / d : ℕ) : ℝ) * Asum m X) := by
        refine sum_le_sum fun d hd => ?_
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (tauR_nonneg d) m)
        calc Ssum m (X / d) ≤ ((X / d : ℕ) : ℝ) * Asum m (X / d) := Ssum_le_mul_Asum m (X / d)
          _ ≤ ((X / d : ℕ) : ℝ) * Asum m X :=
              mul_le_mul_of_nonneg_left (Asum_mono (Nat.div_le_self X d) m) (Nat.cast_nonneg _)
      _ ≤ ∑ d ∈ Icc 1 X, (X : ℝ) * Asum m X * (tauR d ^ m / (d : ℝ)) := by
        refine sum_le_sum fun d hd => ?_
        have hcast : (((X / d : ℕ)) : ℝ) ≤ (X : ℝ) / (d : ℝ) := Nat.cast_div_le
        have hA : 0 ≤ Asum m X := Asum_nonneg m X
        have hp : 0 ≤ (tauR d) ^ m := pow_nonneg (tauR_nonneg d) m
        calc tauR d ^ m * (((X / d : ℕ) : ℝ) * Asum m X)
            ≤ tauR d ^ m * (((X : ℝ) / (d : ℝ)) * Asum m X) := by
              refine mul_le_mul_of_nonneg_left ?_ hp
              exact mul_le_mul_of_nonneg_right hcast hA
          _ = (X : ℝ) * Asum m X * (tauR d ^ m / (d : ℝ)) := by ring
      _ = (X : ℝ) * (Asum m X) ^ 2 := by
        rw [← Finset.mul_sum]
        have h2 : (∑ d ∈ Icc 1 X, tauR d ^ m / (d : ℝ)) = Asum m X := rfl
        rw [h2]
        ring

/-- `A_m(X) ≤ (log X + 1)^{2^m}`. -/
lemma Asum_le_pow (m X : ℕ) : Asum m X ≤ (Real.log X + 1) ^ (2 ^ m) := by
  induction m with
  | zero => simpa using Asum_zero_le X
  | succ m ih =>
    calc Asum (m + 1) X ≤ (Asum m X) ^ 2 := Asum_succ_le m X
      _ ≤ ((Real.log X + 1) ^ 2 ^ m) ^ 2 := pow_le_pow_left₀ (Asum_nonneg m X) ih 2
      _ = (Real.log X + 1) ^ 2 ^ (m + 1) := by
          rw [← pow_mul, show (2 : ℕ) ^ (m + 1) = 2 ^ m * 2 from by rw [pow_succ]]

/-- The elementary divisor-sum bound behind *FI* §9: for every fixed `k` there is a constant `C` (depending on `k`) with `∑_{n ≤ X} τ(n)^k ≤ C·X·(log X + 2)^{2^k}`.  The classical sharp order is `X(log X)^{2^k − 1}`; the extra power is harmless here and the `+2` keeps the base away from `1`. -/
theorem sum_tau_pow_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ,
      (∑ n ∈ Finset.Icc 1 X, ((n.divisors.card : ℝ)) ^ k)
        ≤ C * (X : ℝ) * (Real.log (X : ℝ) + 2) ^ (2 ^ k) := by
  refine ⟨1, one_pos, fun X => ?_⟩
  rw [one_mul]
  have hX0 : 0 ≤ (X : ℝ) := Nat.cast_nonneg X
  have hlog : 0 ≤ Real.log (X : ℝ) + 1 := by
    rcases Nat.eq_zero_or_pos X with h | h
    · subst h; simp
    · have h1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast h
      have := Real.log_nonneg h1
      linarith
  cases k with
  | zero =>
    have hsum : (∑ n ∈ Finset.Icc 1 X, ((n.divisors.card : ℝ)) ^ 0) = (X : ℝ) := by
      simp only [pow_zero]
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc]
      congr 1
    rw [hsum]
    simp only [pow_zero, pow_one]
    calc (X : ℝ) = (X : ℝ) * 1 := by ring
      _ ≤ (X : ℝ) * (Real.log (X : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left (by linarith) hX0
  | succ j =>
    have hS : (∑ n ∈ Finset.Icc 1 X, ((n.divisors.card : ℝ)) ^ (j + 1)) = Ssum (j + 1) X :=
      rfl
    rw [hS]
    calc Ssum (j + 1) X ≤ (X : ℝ) * (Asum j X) ^ 2 := Ssum_succ_le j X
      _ ≤ (X : ℝ) * ((Real.log (X : ℝ) + 1) ^ 2 ^ j) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Asum_nonneg j X) (Asum_le_pow j X) 2) hX0
      _ = (X : ℝ) * (Real.log (X : ℝ) + 1) ^ 2 ^ (j + 1) := by
            congr 1
            rw [← pow_mul, show (2 : ℕ) ^ (j + 1) = 2 ^ j * 2 from by rw [pow_succ]]
      _ ≤ (X : ℝ) * (Real.log (X : ℝ) + 2) ^ 2 ^ (j + 1) := by
            refine mul_le_mul_of_nonneg_left ?_ hX0
            exact pow_le_pow_left₀ hlog (by linarith) _

end

end Work.FIArea2
