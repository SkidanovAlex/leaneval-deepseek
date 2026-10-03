import Mathlib
import Submission.Commons.NumberTheory.Divisors.sum_tau_pow_div_le
import Submission.Commons.Analysis.Real.pow_mul_exp_neg_le

open Finset

namespace Commons.NumberTheory.Divisors

private lemma key_div_le (m n : ℕ) (hm : 1 ≤ m) (hmn : m < n) :
    m * 2 ^ (Nat.log 2 (n / m)) ≤ n := by
  have hn0 : n / m ≠ 0 := by
    rw [Nat.div_ne_zero_iff]; exact ⟨by omega, by omega⟩
  have h1 := Nat.pow_log_le_self 2 hn0
  calc m * 2 ^ Nat.log 2 (n / m) ≤ m * (n / m) := Nat.mul_le_mul_left m h1
    _ ≤ n := Nat.mul_div_le n m

private lemma key_lt (m n : ℕ) (hm : 1 ≤ m) (hmn : m < n) :
    n < m * 2 ^ (Nat.log 2 (n / m) + 1) := by
  have hn0 : n / m ≠ 0 := by
    rw [Nat.div_ne_zero_iff]; exact ⟨by omega, by omega⟩
  have h1 := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) (n / m)
  have hnn : n / m + 1 ≤ 2 ^ (Nat.log 2 (n / m) + 1) := by omega
  have hnm : n = m * (n / m) + n % m := (Nat.div_add_mod n m).symm
  have hr : n % m < m := Nat.mod_lt n (by omega)
  calc n = m * (n / m) + n % m := hnm
    _ < m * (n / m) + m := by omega
    _ = m * (n / m + 1) := (Nat.mul_succ m (n / m)).symm
    _ ≤ m * 2 ^ (Nat.log 2 (n / m) + 1) := Nat.mul_le_mul_left m hnn

private lemma pointwise (m n k : ℕ) (hm : 1 ≤ m) (hmn : m < n) :
    ((n.divisors.card : ℝ) ^ k) / (n : ℝ) ^ 2
      ≤ (1 / (m : ℝ)) * (((n.divisors.card : ℝ) ^ k) / (n : ℝ))
          / (2 : ℝ) ^ (Nat.log 2 (n / m)) := by
  have hm2 : m * 2 ^ (Nat.log 2 (n / m)) ≤ n := key_div_le m n hm hmn
  have hm2' : ((m : ℝ) * (2 : ℝ) ^ (Nat.log 2 (n / m))) ≤ (n : ℝ) := by exact_mod_cast hm2
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hden : (m : ℝ) * (2 : ℝ) ^ (Nat.log 2 (n / m)) * (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [hm2', hnpos]
  have hstep := div_le_div_of_nonneg_left (show (0:ℝ) ≤ (n.divisors.card : ℝ) ^ k by positivity)
      (by positivity : (0:ℝ) < (m : ℝ) * (2 : ℝ) ^ (Nat.log 2 (n / m)) * (n : ℝ)) hden
  have hgoal : ((n.divisors.card : ℝ) ^ k) / ((m : ℝ) * (2 : ℝ) ^ (Nat.log 2 (n / m)) * (n : ℝ))
      = (1 / (m : ℝ)) * (((n.divisors.card : ℝ) ^ k) / (n : ℝ)) / (2 : ℝ) ^ (Nat.log 2 (n / m)) := by
    have hm0 : (m:ℝ) ≠ 0 := by positivity
    have h20 : (2:ℝ) ^ (Nat.log 2 (n/m)) ≠ 0 := by positivity
    have hn0 : (n:ℝ) ≠ 0 := by positivity
    field_simp
  rw [← hgoal]
  exact hstep

private lemma log_le_shift (m j : ℕ) (hm : 1 ≤ m) :
    Real.log ((m : ℝ) * 2 ^ (j + 1) + 2)
      ≤ Real.log ((m : ℝ) + 2) + ((j:ℝ) + 1) * Real.log 2 := by
  have h1 : (2:ℝ) ≤ 2 * (2:ℝ)^(j+1) := by
    have := one_le_pow₀ (show (1:ℝ) ≤ 2 by norm_num) (n := j+1)
    nlinarith
  have hle : (m : ℝ) * 2 ^ (j + 1) + 2 ≤ ((m : ℝ) + 2) * 2 ^ (j + 1) := by
    have : ((m:ℝ)+2) * 2^(j+1) = (m:ℝ)*2^(j+1) + 2*2^(j+1) := by ring
    rw [this]; linarith
  have hpos1 : (0:ℝ) < (m:ℝ)*2^(j+1)+2 := by positivity
  have hlog := Real.log_le_log hpos1 hle
  have hmp : (m:ℝ)+2 ≠ 0 := by positivity
  have h2p : (2:ℝ)^(j+1) ≠ 0 := by positivity
  rw [Real.log_mul hmp h2p, Real.log_pow] at hlog
  simpa [Nat.cast_add, Nat.cast_one] using hlog

set_option maxHeartbeats 2000000 in
private lemma tail_bound_aux
    (geom : ∀ a M : ℕ, (∑ j ∈ Finset.range M, (1/2:ℝ)^j * ((j:ℝ)+2)^a)
        ≤ 30 * (2*(a:ℝ)/Real.exp 1)^a)
    (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m N : ℕ, 1 ≤ m →
      (∑ n ∈ (Finset.Icc 1 N).filter (fun n => m < n),
          ((n.divisors.card : ℝ) ^ k) / (n : ℝ) ^ 2)
        ≤ C * (Real.log ((m : ℝ) + 2)) ^ (2^k) / (m : ℝ) := by
  obtain ⟨CB, hCBpos, hCB⟩ := Commons.NumberTheory.Divisors.sum_tau_pow_div_le k
  refine ⟨30 * CB * (2*((2:ℝ)^k)/Real.exp 1)^(2^k), by positivity, ?_⟩
  intro m N hm
  have hmR : (0:ℝ) < (m:ℝ) := Nat.cast_pos.mpr (by omega : 0 < m)
  set α := Real.log ((m:ℝ)+2) with hαdef
  set g : ℕ → ℕ := fun n => Nat.log 2 (n/m) with hgdef
  set s : Finset ℕ := (Finset.Icc 1 N).filter (fun n => m < n) with hsdef
  have hαnn : 0 ≤ α := by
    rw [hαdef]; apply Real.log_nonneg
    have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    linarith
  have hmem : ∀ n ∈ s, g n ∈ Finset.range (N+1) := by
    intro n hn
    rw [Finset.mem_range]
    have hn' : n ∈ (Finset.Icc 1 N).filter (fun n => m < n) := by rwa [hsdef] at hn
    have hnN : n ≤ N := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn').1).2
    have hgn : g n = Nat.log 2 (n/m) := by rw [hgdef]
    have h1 : Nat.log 2 (n/m) ≤ Nat.log 2 n := Nat.log_mono_right (Nat.div_le_self n m)
    have h2 : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
    omega
  -- Step A
  have hA : (∑ n ∈ s, ((n.divisors.card:ℝ)^k)/(n:ℝ)^2)
      ≤ (1/(m:ℝ)) * ∑ n ∈ s, (((n.divisors.card:ℝ)^k)/(n:ℝ))/(2:ℝ)^(g n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hmn : m < n := (Finset.mem_filter.mp (by rwa [hsdef] at hn)).2
    have hg : g n = Nat.log 2 (n/m) := by rw [hgdef]
    rw [hg]
    simpa [mul_div_assoc] using pointwise m n k hm hmn
  -- Step B
  have hB : (∑ n ∈ s, (((n.divisors.card:ℝ)^k)/(n:ℝ))/(2:ℝ)^(g n))
      = ∑ j ∈ Finset.range (N+1),
          ∑ n ∈ (s.filter (fun n => g n = j)), (((n.divisors.card:ℝ)^k)/(n:ℝ))/(2:ℝ)^j := by
    rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.range (N+1)) (g := g) hmem]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro n hn
    rw [(Finset.mem_filter.mp hn).2]
  -- Step C
  have hC : ∀ j ∈ Finset.range (N+1),
      ∑ n ∈ (s.filter (fun n => g n = j)), (((n.divisors.card:ℝ)^k)/(n:ℝ))/(2:ℝ)^j
        ≤ CB * (1/2:ℝ)^j * (Real.log ((m:ℝ)*2^(j+1)+2))^(2^k) := by
    intro j hj
    have hfact : ∑ n ∈ (s.filter (fun n => g n = j)), (((n.divisors.card:ℝ)^k)/(n:ℝ))/(2:ℝ)^j
        = (1/(2:ℝ)^j) * ∑ n ∈ (s.filter (fun n => g n = j)), (((n.divisors.card:ℝ)^k)/(n:ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    rw [hfact]
    have hle : ∑ n ∈ (s.filter (fun n => g n = j)), (((n.divisors.card:ℝ)^k)/(n:ℝ))
        ≤ CB * (Real.log ((m:ℝ)*2^(j+1)+2))^(2^k) := by
      have hsubset : (s.filter (fun n => g n = j)) ⊆ Finset.Icc 1 (m*2^(j+1)) := by
        intro n hn
        rw [Finset.mem_filter] at hn
        obtain ⟨hns, hgj⟩ := hn
        have hn' : n ∈ (Finset.Icc 1 N).filter (fun n => m < n) := by rwa [hsdef] at hns
        have hmn : m < n := (Finset.mem_filter.mp hn').2
        have hnge1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn').1).1
        rw [Finset.mem_Icc]
        refine ⟨hnge1, ?_⟩
        have hlog : Nat.log 2 (n/m) = j := by
          have : g n = Nat.log 2 (n/m) := by rw [hgdef]
          rw [this] at hgj; exact hgj
        have hlt := key_lt m n hm hmn
        rw [hlog] at hlt
        exact le_of_lt hlt
      calc ∑ n ∈ (s.filter (fun n => g n = j)), (((n.divisors.card:ℝ)^k)/(n:ℝ))
          ≤ ∑ n ∈ Finset.Icc 1 (m*2^(j+1)), (((n.divisors.card:ℝ)^k)/(n:ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun n hn hn2 => div_nonneg (by positivity) (Nat.cast_nonneg n))
        _ ≤ CB * (Real.log ((m:ℝ)*2^(j+1)+2))^(2^k) := by
              have h1 : 1 ≤ m * 2^(j+1) :=
                Nat.succ_le_of_lt (Nat.mul_pos (by omega : 0 < m) (pow_pos (by norm_num) (j+1)))
              simpa [Nat.cast_mul, Nat.cast_pow] using hCB (m*2^(j+1)) h1
    have hone : ((1:ℝ)/(2:ℝ)^j) = (1/2:ℝ)^j := by rw [one_div_pow]
    calc (1/(2:ℝ)^j) * ∑ n ∈ (s.filter (fun n => g n = j)), (((n.divisors.card:ℝ)^k)/(n:ℝ))
        ≤ (1/(2:ℝ)^j) * (CB * (Real.log ((m:ℝ)*2^(j+1)+2))^(2^k)) :=
          mul_le_mul_of_nonneg_left hle (by positivity : (0:ℝ) ≤ 1/(2:ℝ)^j)
      _ = CB * (1/2:ℝ)^j * (Real.log ((m:ℝ)*2^(j+1)+2))^(2^k) := by rw [hone]; ring
  -- Final assembly
  have hlogineq : ∀ j ∈ Finset.range (N+1),
      Real.log ((m:ℝ)*2^(j+1)+2) ≤ α + ((j:ℝ)+1) * Real.log 2 := by
    intro j hj; rw [hαdef]; exact log_le_shift m j hm
  have hβle : Real.log 2 ≤ α := by
    rw [hαdef]
    apply Real.log_le_log (by norm_num)
    have : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    linarith
  have hdom : ∀ j ∈ Finset.range (N+1),
      CB * (1/2:ℝ)^j * (Real.log ((m:ℝ)*2^(j+1)+2))^(2^k)
        ≤ CB * (1/2:ℝ)^j * (α * ((j:ℝ)+2))^(2^k) := by
    intro j hj
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (le_of_lt hCBpos) (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) j))
    apply pow_le_pow_left₀ (Real.log_nonneg (by
      have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
      have hp2 : (1:ℝ) ≤ (2:ℝ)^(j+1) := one_le_pow₀ (by norm_num)
      nlinarith [hm1, hp2]))
    have h1 : Real.log ((m:ℝ)*2^(j+1)+2) ≤ α + ((j:ℝ)+1)*Real.log 2 := hlogineq j hj
    have h2 : α + ((j:ℝ)+1)*Real.log 2 ≤ α * ((j:ℝ)+2) := by
      have h3 : Real.log 2 ≤ α := hβle
      nlinarith [hαnn, h3, (Nat.cast_nonneg j : (0:ℝ) ≤ (j:ℝ))]
    linarith
  have hgeom : (∑ j ∈ Finset.range (N+1), (1/2:ℝ)^j * (α * ((j:ℝ)+2))^(2^k))
      ≤ α^(2^k) * (30 * (2*((2:ℝ)^k)/Real.exp 1)^(2^k)) := by
    calc ∑ j ∈ Finset.range (N+1), (1/2:ℝ)^j * (α * ((j:ℝ)+2))^(2^k)
        = α^(2^k) * ∑ j ∈ Finset.range (N+1), ((1/2:ℝ)^j * ((j:ℝ)+2)^(2^k)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [mul_pow]; ring
      _ ≤ α^(2^k) * (30 * (2*((2:ℝ)^k)/Real.exp 1)^(2^k)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ α^(2^k))
          simpa using geom (2^k) (N+1)
  calc (∑ n ∈ (Finset.Icc 1 N).filter (fun n => m < n), ((n.divisors.card:ℝ)^k)/(n:ℝ)^2)
      = ∑ n ∈ s, ((n.divisors.card:ℝ)^k)/(n:ℝ)^2 := by rw [hsdef]
    _ ≤ (1/(m:ℝ)) * ∑ n ∈ s, (((n.divisors.card:ℝ)^k)/(n:ℝ))/(2:ℝ)^(g n) := hA
    _ = (1/(m:ℝ)) * ∑ j ∈ Finset.range (N+1),
          ∑ n ∈ (s.filter (fun n => g n = j)), (((n.divisors.card:ℝ)^k)/(n:ℝ))/(2:ℝ)^j := by rw [hB]
    _ ≤ (1/(m:ℝ)) * ∑ j ∈ Finset.range (N+1),
          CB * (1/2:ℝ)^j * (Real.log ((m:ℝ)*2^(j+1)+2))^(2^k) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 1/(m:ℝ))
          exact Finset.sum_le_sum hC
    _ ≤ (1/(m:ℝ)) * ∑ j ∈ Finset.range (N+1),
          CB * (1/2:ℝ)^j * (α * ((j:ℝ)+2))^(2^k) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 1/(m:ℝ))
          exact Finset.sum_le_sum hdom
    _ = (1/(m:ℝ)) * (CB * ∑ j ∈ Finset.range (N+1),
          (1/2:ℝ)^j * (α * ((j:ℝ)+2))^(2^k)) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j hj; ring
    _ ≤ (1/(m:ℝ)) * (CB * (α^(2^k) * (30 * (2*((2:ℝ)^k)/Real.exp 1)^(2^k)))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 1/(m:ℝ))
          exact mul_le_mul_of_nonneg_left hgeom (le_of_lt hCBpos)
    _ = (30 * CB * (2*((2:ℝ)^k)/Real.exp 1)^(2^k)) * (Real.log ((m:ℝ)+2))^(2^k) / (m:ℝ) := by
          rw [hαdef]; ring


private lemma geom_sum_le_inv (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (M : ℕ) :
    ∑ j ∈ Finset.range M, r^j ≤ (1 - r)⁻¹ := by
  rw [geom_sum_eq (by linarith : r ≠ 1)]
  have heq : (r^M - 1)/(r-1) = (1 - r^M)/(1-r) := by
    rw [div_eq_div_iff (by linarith) (by linarith)]; ring
  rw [heq, ← one_div]
  have h : 1 - r^M ≤ 1 := by
    have hm : (0:ℝ) ≤ r^M := by positivity
    linarith
  exact div_le_div_of_nonneg_right h (by linarith)

private lemma exp_c_le : Real.exp (1/2) ≤ 5/3 := by
  have hsq : (Real.exp (1/2))^2 = Real.exp 1 := by rw [sq, ← Real.exp_add]; norm_num
  have hlt : Real.exp 1 < (5/3:ℝ)^2 := by
    rw [show ((5:ℝ)/3)^2 = 25/9 by norm_num]
    linarith [Real.exp_one_lt_d9]
  rw [← hsq] at hlt
  nlinarith [Real.exp_pos (1/2), hlt]

private lemma geom_pow_add_two_bound (a M : ℕ) :
    (∑ j ∈ Finset.range M, (1/2:ℝ)^j * ((j:ℝ)+2)^a)
      ≤ 30*(2*(a:ℝ)/Real.exp 1)^a := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · rw [ha]
    simp only [pow_zero, mul_one]
    have h2 : (∑ j ∈ Finset.range M, (1/2:ℝ)^j) ≤ (2:ℝ) := by
      calc ∑ j ∈ Finset.range M, (1/2:ℝ)^j ≤ (1 - (1/2:ℝ))⁻¹ :=
            geom_sum_le_inv (r := (1/2:ℝ)) (by norm_num) (by norm_num) M
        _ = 2 := by norm_num
    linarith
  · have hCeq : ((a:ℝ)/((1/2)*Real.exp 1))^a = (2*(a:ℝ)/Real.exp 1)^a := by
      congr 1; field_simp
    set r := Real.exp (1/2)/2 with hrdef
    have hterm : ∀ j : ℕ, (1/2:ℝ)^j * ((j:ℝ)+2)^a
        ≤ (2*(a:ℝ)/Real.exp 1)^a * Real.exp 1 * r^j := by
      intro j
      have hx : (0:ℝ) ≤ (j:ℝ)+2 := by positivity
      have hmax := Commons.Analysis.Real.pow_mul_exp_neg_le a (c := (1/2:ℝ)) (by norm_num) hx
      rw [hCeq] at hmax
      have hx2 : Real.exp (-(1/2*((j:ℝ)+2))) * Real.exp ((1/2)*((j:ℝ)+2)) = 1 := by
        rw [← Real.exp_add, show -(1/2*((j:ℝ)+2)) + (1/2*((j:ℝ)+2)) = 0 by ring, Real.exp_zero]
      have h1 : ((j:ℝ)+2)^a ≤ (2*(a:ℝ)/Real.exp 1)^a * Real.exp ((1/2)*((j:ℝ)+2)) := by
        calc ((j:ℝ)+2)^a = ((j:ℝ)+2)^a * (Real.exp (-(1/2*((j:ℝ)+2))) * Real.exp ((1/2)*((j:ℝ)+2))) := by rw [hx2, mul_one]
          _ = (((j:ℝ)+2)^a * Real.exp (-(1/2*((j:ℝ)+2)))) * Real.exp ((1/2)*((j:ℝ)+2)) := by ring
          _ ≤ (2*(a:ℝ)/Real.exp 1)^a * Real.exp ((1/2)*((j:ℝ)+2)) :=
              mul_le_mul_of_nonneg_right hmax (le_of_lt (Real.exp_pos _))
      have hexp : Real.exp ((1/2)*((j:ℝ)+2)) = Real.exp 1 * (Real.exp (1/2))^j := by
        have hsplit : (1/2)*((j:ℝ)+2) = (j:ℝ)*(1/2) + 1 := by ring
        rw [hsplit, Real.exp_add, Real.exp_nat_mul]; ring
      have hrpow : r^j = (1/2:ℝ)^j * (Real.exp (1/2))^j := by
        rw [hrdef, ← mul_pow]
        congr 1
        ring
      calc (1/2:ℝ)^j * ((j:ℝ)+2)^a
          ≤ (1/2:ℝ)^j * ((2*(a:ℝ)/Real.exp 1)^a * Real.exp ((1/2)*((j:ℝ)+2))) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (2*(a:ℝ)/Real.exp 1)^a * Real.exp 1 * r^j := by
            rw [hexp, hrpow]; ring
    calc (∑ j ∈ Finset.range M, (1/2:ℝ)^j * ((j:ℝ)+2)^a)
        ≤ ∑ j ∈ Finset.range M, (2*(a:ℝ)/Real.exp 1)^a * Real.exp 1 * r^j :=
          Finset.sum_le_sum (fun j hj => hterm j)
      _ = (2*(a:ℝ)/Real.exp 1)^a * Real.exp 1 * ∑ j ∈ Finset.range M, r^j := by
          rw [← Finset.mul_sum]
      _ ≤ (2*(a:ℝ)/Real.exp 1)^a * Real.exp 1 * 6 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hc : r ≤ 5/6 := by rw [hrdef]; linarith [exp_c_le]
          have hr1 : r < 1 := by linarith [hc]
          have hr0 : 0 ≤ r := by positivity
          have hlt := geom_sum_le_inv r hr0 hr1 M
          have hpos : 0 < 1 - r := by linarith
          have h6 : (1 - r)⁻¹ ≤ 6 := by
            have hge : (1/6:ℝ) ≤ 1 - r := by linarith
            have := (inv_le_inv₀ hpos (by norm_num : (0:ℝ) < 1/6)).mpr hge
            simpa using this
          linarith [hlt, h6]
      _ ≤ 30 * (2*(a:ℝ)/Real.exp 1)^a := by
          have he3 : Real.exp 1 * 6 ≤ 30 := by linarith [Real.exp_one_lt_three]
          have hnn : (0:ℝ) ≤ (2*(a:ℝ)/Real.exp 1)^a := by positivity
          nlinarith [he3, hnn]

theorem sum_tau_pow_div_sq_tail_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m N : ℕ, 1 ≤ m →
      (∑ n ∈ (Finset.Icc 1 N).filter (fun n => m < n),
          ((n.divisors.card : ℝ) ^ k) / (n : ℝ) ^ 2)
        ≤ C * (Real.log ((m : ℝ) + 2)) ^ ((2 : ℝ) ^ k) / (m : ℝ) := by
  obtain ⟨C, hCpos, hC⟩ := tail_bound_aux geom_pow_add_two_bound k
  refine ⟨C, hCpos, ?_⟩
  intro m N hm
  have h := hC m N hm
  rw [show ((2:ℝ)^k) = ((2^k:ℕ):ℝ) by push_cast; ring, Real.rpow_natCast]
  exact h

end Commons.NumberTheory.Divisors
