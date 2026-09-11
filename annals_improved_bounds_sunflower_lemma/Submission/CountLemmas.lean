import Mathlib

/-!
# Combinatorial counting lemmas (binomial ratio / sum bounds)

All lemmas are stated over the natural numbers; final real-valued consequences
are derived in other modules.
-/
open Finset
open scoped BigOperators

namespace Submission.CountLemmas

/-- For `0 < v`, `N - v ≤ (v+1) · ⌊N/v⌋`: one step of the binomial ratio bound. -/
private lemma sub_floor_succ_mul (N v : ℕ) (hv : 0 < v) : N - v ≤ (v + 1) * (N / v) := by
  have h1 : N < v * (N / v) + v := by
    have h := Nat.lt_mul_div_succ N hv
    simpa [Nat.mul_succ] using h
  have hle : N ≤ v * (N / v) + v := Nat.le_of_lt h1
  calc
    N - v ≤ v * (N / v) := by
      rw [Nat.sub_le_iff_le_add]
      exact hle
    _ ≤ (v + 1) * (N / v) := by
      exact Nat.mul_le_mul_right (N / v) (Nat.le_succ v)

/-- `C(N, m+1) ≤ C(N, m) · q` whenever `N - m ≤ (m+1) · q`. -/
private lemma choose_step_le (N m q : ℕ) (hm : N - m ≤ (m + 1) * q) :
    N.choose (m + 1) ≤ N.choose m * q := by
  have hmul : N.choose (m + 1) * (m + 1) ≤ (N.choose m * q) * (m + 1) := by
    calc
      N.choose (m + 1) * (m + 1) = N.choose m * (N - m) := Nat.choose_succ_right_eq N m
      _ ≤ N.choose m * ((m + 1) * q) := Nat.mul_le_mul_left (N.choose m) hm
      _ = (N.choose m * q) * (m + 1) := by ring
  exact Nat.le_of_mul_le_mul_right hmul (by omega)

/-- Per-term binomial ratio bound: `C(N, v+j) ≤ C(N, v) · (N/v)^j` for `j ≤ N-v`. -/
lemma choose_ratio_le {N v j : ℕ} (hv : 0 < v) (hj : j ≤ N - v) :
    (N.choose (v + j)) ≤ N.choose v * (N / v) ^ j := by
  induction j with
  | zero =>
      simp
  | succ j ih =>
      have hjs : j ≤ N - v := Nat.le_trans (Nat.le_succ j) hj
      have hib := ih hjs
      have hsub : N - (v + j) ≤ (v + j + 1) * (N / v) := by
        calc
          N - (v + j) ≤ N - v := by omega
          _ ≤ (v + 1) * (N / v) := sub_floor_succ_mul N v hv
          _ ≤ (v + j + 1) * (N / v) := by
            have hvv : v + 1 ≤ v + j + 1 := by omega
            exact Nat.mul_le_mul_right (N / v) hvv
      have hstep := choose_step_le N (v + j) (N / v) hsub
      calc
        N.choose (v + (j + 1)) = N.choose ((v + j) + 1) := by rw [← Nat.add_assoc]
        _ ≤ N.choose (v + j) * (N / v) := hstep
        _ ≤ (N.choose v * (N / v) ^ j) * (N / v) := Nat.mul_le_mul_right (N / v) hib
        _ = N.choose v * (N / v) ^ (j + 1) := by
          rw [pow_succ]
          ring

/-- `C(N, v+j) ≤ C(N, v) · (N/v)^j` for all `j` when `0 < v ≤ N` (terms with `v+j > N` vanish). -/
private lemma choose_ratio_le_any {N v j : ℕ} (hv : 0 < v) (hvN : v ≤ N) :
    N.choose (v + j) ≤ N.choose v * (N / v) ^ j := by
  by_cases h : v + j ≤ N
  · have hj : j ≤ N - v := by omega
    exact choose_ratio_le hv hj
  · have hvj : N < v + j := by omega
    rw [Nat.choose_eq_zero_of_lt hvj]
    exact Nat.zero_le _

/-- Geometric-sum bound: for `q ≥ 2`, `Σ_{j=0}^{s} q^j ≤ 2·q^s`. -/
private lemma geom_sum_le_two_mul {q s : ℕ} (hq : 2 ≤ q) :
    (∑ j ∈ Finset.range (s + 1), q ^ j) ≤ 2 * q ^ s := by
  induction s with
  | zero =>
      simp
  | succ s ih =>
      have h1 : 2 * q ^ s ≤ q ^ (s + 1) := by
        calc
          2 * q ^ s ≤ q * q ^ s := Nat.mul_le_mul_right (q ^ s) hq
          _ = q ^ (s + 1) := by
            rw [pow_succ]
            ring
      calc
        (∑ j ∈ Finset.range (s + 1 + 1), q ^ j)
            = (∑ j ∈ Finset.range (s + 1), q ^ j) + q ^ (s + 1) := by
                rw [Finset.sum_range_succ]
        _ ≤ 2 * q ^ s + q ^ (s + 1) := by
                exact Nat.add_le_add_right ih (q ^ (s + 1))
        _ ≤ 2 * q ^ (s + 1) := by
                calc
                  2 * q ^ s + q ^ (s + 1) ≤ q ^ (s + 1) + q ^ (s + 1) := by
                      exact Nat.add_le_add h1 le_rfl
                  _ = 2 * q ^ (s + 1) := by ring

/-- Sum of the first `s+1` binomial coefficients at `v, v+1, ..., v+s`. -/
lemma sum_choose_le {N v s : ℕ} (hv : 0 < v) (h2v : 2 * v ≤ N) :
    (∑ j ∈ Finset.range (s + 1), (N.choose (v + j) : ℕ)) ≤ 2 * N.choose v * (N / v) ^ s := by
  have hvN : v ≤ N := by omega
  have hq : 2 ≤ N / v := by
    rw [Nat.le_div_iff_mul_le hv]
    exact h2v
  calc
    (∑ j ∈ Finset.range (s + 1), (N.choose (v + j) : ℕ))
        ≤ (∑ j ∈ Finset.range (s + 1), (N.choose v * (N / v) ^ j : ℕ)) := by
            exact Finset.sum_le_sum (fun j _ => choose_ratio_le_any hv hvN)
    _ = N.choose v * (∑ j ∈ Finset.range (s + 1), (N / v) ^ j) := by
            rw [← Finset.mul_sum]
    _ ≤ N.choose v * (2 * (N / v) ^ s) := by
            exact Nat.mul_le_mul_left (N.choose v) (geom_sum_le_two_mul hq)
    _ = 2 * N.choose v * (N / v) ^ s := by ring

/-- A crude upper bound: `C(N, v) ≤ N^v`?  Actually `C(N,v) ≤ 2^N`. -/
lemma choose_le_pow_two {N v : ℕ} : (N.choose v) ≤ 2 ^ N := by
  exact Nat.choose_le_two_pow N v

/-- `C(N,v) ≤ N^v` (trivial: product of v factors each ≤ N). -/
lemma choose_le_pow {N v : ℕ} (hv : v ≤ N) : (N.choose v) ≤ N ^ v := by
  have _ := hv
  exact Nat.choose_le_pow N v

/-- sum of `C(N, v + j)` for j ≤ s is at most the binomial at shifted top. -/
lemma sum_choose_le_choose_shift {N v s : ℕ} :
    (∑ j ∈ Finset.range (s + 1), (N.choose (v + j) : ℕ)) ≤ (N + s).choose (v + s) := by
  induction s with
  | zero =>
      simp
  | succ s ih =>
      have hterm : (N.choose (v + (s + 1)) : ℕ) ≤ (N + s).choose ((v + s) + 1) := by
        rw [Nat.add_assoc]
        exact Nat.choose_le_choose (v + (s + 1)) (show N ≤ N + s by omega)
      have hpascal : (N + (s + 1)).choose (v + (s + 1)) =
          (N + s).choose (v + s) + (N + s).choose ((v + s) + 1) := by
        rw [show N + (s + 1) = (N + s) + 1 by omega]
        rw [show v + (s + 1) = (v + s) + 1 by omega]
        rw [← Nat.succ_eq_add_one, ← Nat.succ_eq_add_one]
        rw [Nat.choose_succ_succ]
      calc
        (∑ j ∈ Finset.range ((s + 1) + 1), (N.choose (v + j) : ℕ))
            = (∑ j ∈ Finset.range (s + 1), (N.choose (v + j) : ℕ)) + (N.choose (v + (s + 1)) : ℕ) := by
                rw [Finset.sum_range_succ]
        _ ≤ (N + s).choose (v + s) + (N.choose (v + (s + 1)) : ℕ) := by
                exact Nat.add_le_add_right ih (N.choose (v + (s + 1)) : ℕ)
        _ ≤ (N + s).choose (v + s) + (N + s).choose ((v + s) + 1) := by
                exact Nat.add_le_add_left hterm ((N + s).choose (v + s))
        _ = (N + (s + 1)).choose (v + (s + 1)) := by
                exact hpascal.symm


/-- `(n+1)·C(n,k) = C(n+1,k+1)·(k+1)` (combinatorial identity). -/
private lemma choose_succ_mul (n k : ℕ) :
    (n + 1).choose (k + 1) * (k + 1) = n.choose k * (n + 1) := by
  simpa [Nat.mul_comm] using (Nat.add_one_mul_choose_eq n k).symm

/-- Real core step: `C(n+1,k+1)·v ≤ C(n,k)·N` (in ℝ) given `v·(n+1) ≤ N·(k+1)`. -/
private lemma core_bound_real {n k N v : ℕ}
    (hcond : (v : ℝ) * ((n + 1 : ℕ) : ℝ) ≤ (N : ℝ) * ((k + 1 : ℕ) : ℝ)) :
    ((((n + 1).choose (k + 1) : ℕ) : ℝ)) * (v : ℝ) ≤ (((n.choose k : ℕ) : ℝ)) * (N : ℝ) := by
  let C' : ℝ := (((n + 1).choose (k + 1) : ℕ) : ℝ)
  let C : ℝ := ((n.choose k : ℕ) : ℝ)
  let a : ℝ := ((n + 1 : ℕ) : ℝ)
  let b : ℝ := ((k + 1 : ℕ) : ℝ)
  have hid : C' * b = C * a := by
    dsimp [C, C', a, b]
    exact_mod_cast (choose_succ_mul n k)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hk1 : (0 : ℝ) < b := by dsimp [b]; exact_mod_cast (Nat.succ_pos k)
  have hcondC : (v * a) * C ≤ (N * b) * C := mul_le_mul_of_nonneg_right hcond hC
  have hE : (v * C') * b ≤ (N * C) * b := by
    nlinarith [hid, hcondC]
  have hres : v * C' ≤ N * C := le_of_mul_le_mul_right hE hk1
  dsimp [C, C'] at hres
  nlinarith

/-- `N + s + 1 ≤ 2·(N/v)·(v+s+1)` whenever `0 < v ≤ N`. -/
private lemma two_mul_floor_ge {N v s : ℕ} (hv : 0 < v) (hvN : v ≤ N) :
    N + s + 1 ≤ 2 * (N / v) * (v + s + 1) := by
  set q : ℕ := N / v with hqdef
  have hq1 : 1 ≤ q := by
    rw [hqdef]
    rw [Nat.le_div_iff_mul_le hv]
    simpa [Nat.mul_comm] using hvN
  have hlt : N < v * (q + 1) := by
    rw [hqdef]
    simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using Nat.lt_mul_div_succ N hv
  have hdiv : N + 1 ≤ (q + 1) * v := by
    nlinarith
  have h1 : N + s + 1 ≤ q * v + v + s := by
    nlinarith
  have h2 : q * v + v + s ≤ 2 * q * (v + s + 1) := by
    nlinarith [hq1]
  nlinarith

/-- Real version: `C(N+s, v+s) ≤ C(N, v) · (N/v)^s` for `0 < v ≤ N`. -/
lemma choose_shift_ratio_le_real {N v s : ℕ} (hv : 0 < v) (hvN : v ≤ N) :
    ((N + s).choose (v + s) : ℝ) ≤ (N.choose v : ℝ) * (((N : ℝ) / (v : ℝ)) ^ s) := by
  have hmain : ((N + s).choose (v + s) : ℝ) * (v : ℝ) ^ s ≤ (N.choose v : ℝ) * (N : ℝ) ^ s := by
    induction s with
    | zero =>
        simp
    | succ s ih =>
        have hn : N + (s + 1) = (N + s) + 1 := by omega
        have hk : v + (s + 1) = (v + s) + 1 := by omega
        rw [hn, hk]
        rw [pow_succ, pow_succ]
        have hcond : (v : ℝ) * ((N + s + 1 : ℕ) : ℝ) ≤ (N : ℝ) * ((v + s + 1 : ℕ) : ℝ) := by
          have hnat : v * (N + s + 1) ≤ N * (v + s + 1) := by
            nlinarith [Nat.mul_le_mul_right (s + 1) hvN]
          exact_mod_cast hnat
        have hcore := core_bound_real (n := N + s) (k := v + s) (N := N) (v := v) hcond
        have hv0 : 0 ≤ (v : ℝ) ^ s := pow_nonneg (by positivity : 0 ≤ (v : ℝ)) s
        have hN0 : 0 ≤ (N : ℝ) := by positivity
        have hc1 : (((N + s) + 1).choose ((v + s) + 1) : ℝ) * (v : ℝ) * (v : ℝ) ^ s
            ≤ ((N + s).choose (v + s) : ℝ) * (N : ℝ) * (v : ℝ) ^ s := by
          have h1 := mul_le_mul_of_nonneg_right hcore hv0
          nlinarith
        have hc2 : ((N + s).choose (v + s) : ℝ) * (N : ℝ) * (v : ℝ) ^ s
            ≤ (N.choose v : ℝ) * (N : ℝ) ^ s * (N : ℝ) := by
          have h2 := mul_le_mul_of_nonneg_right ih hN0
          nlinarith
        nlinarith
  have hvR : (0 : ℝ) < (v : ℕ) := by exact_mod_cast hv
  have hvs_pos : 0 < (v : ℝ) ^ s := pow_pos hvR s
  have hvs_ne : (v : ℝ) ^ s ≠ 0 := ne_of_gt hvs_pos
  have hfield : (((N : ℝ) / (v : ℝ)) ^ s) * (v : ℝ) ^ s = (N : ℝ) ^ s := by
    rw [div_pow]
    field_simp [hvs_ne]
  have hle : ((N + s).choose (v + s) : ℝ) * (v : ℝ) ^ s
      ≤ (N.choose v : ℝ) * (((N : ℝ) / (v : ℝ)) ^ s) * (v : ℝ) ^ s := by
    calc
      ((N + s).choose (v + s) : ℝ) * (v : ℝ) ^ s ≤ (N.choose v : ℝ) * (N : ℝ) ^ s := hmain
      _ = (N.choose v : ℝ) * (((N : ℝ) / (v : ℝ)) ^ s) * (v : ℝ) ^ s := by
          rw [← hfield]
          ring
  exact le_of_mul_le_mul_right hle hvs_pos

/-- integer version with the ceiling-safe form: `C(N+s,v+s) ≤ C(N,v)·(⌈N/v⌉)^s` fails; use 2N/v. -/
lemma choose_shift_ratio_le_two {N v s : ℕ} (hv : 0 < v) (hvN : v ≤ N) :
    (N + s).choose (v + s) ≤ N.choose v * (2 * (N / v)) ^ s := by
  induction s with
  | zero =>
      simp
  | succ s ih =>
      have hn : N + (s + 1) = (N + s) + 1 := by omega
      have hk : v + (s + 1) = (v + s) + 1 := by omega
      rw [hn, hk]
      rw [pow_succ]
      have hstep : N + s + 1 ≤ 2 * (N / v) * ((v + s) + 1) := by
        simpa using two_mul_floor_ge (N := N) (v := v) (s := s) hv hvN
      have hle1 : ((N + s) + 1).choose ((v + s) + 1) ≤ ((N + s).choose (v + s)) * (2 * (N / v)) := by
        have hidn : ((N + s) + 1).choose ((v + s) + 1) * ((v + s) + 1)
            = ((N + s).choose (v + s)) * ((N + s) + 1) := by
          simpa using choose_succ_mul (N + s) (v + s)
        have h1 : ((N + s) + 1).choose ((v + s) + 1) * ((v + s) + 1)
            ≤ (((N + s).choose (v + s)) * (2 * (N / v))) * ((v + s) + 1) := by
          calc
            ((N + s) + 1).choose ((v + s) + 1) * ((v + s) + 1)
                = ((N + s).choose (v + s)) * ((N + s) + 1) := hidn
            _ ≤ ((N + s).choose (v + s)) * (2 * (N / v) * ((v + s) + 1)) := by
                exact Nat.mul_le_mul_left ((N + s).choose (v + s)) hstep
            _ = (((N + s).choose (v + s)) * (2 * (N / v))) * ((v + s) + 1) := by ring
        exact Nat.le_of_mul_le_mul_right h1 (by omega)
      calc
        ((N + s) + 1).choose ((v + s) + 1)
            ≤ ((N + s).choose (v + s)) * (2 * (N / v)) := hle1
        _ ≤ (N.choose v * (2 * (N / v)) ^ s) * (2 * (N / v)) := by
            exact Nat.mul_le_mul_right (2 * (N / v)) ih
        _ = N.choose v * (2 * (N / v)) ^ (s + 1) := by
            rw [pow_succ]
            ring

/-- `(N/v)^s ≤ (N/v)^s'` when `s ≤ s'` (integer powers, `1 ≤ N/v`). -/
lemma pow_ratio_mono {N v s s' : ℕ} (hv : 0 < v) (hvN : v ≤ N) (hss : s ≤ s') :
    (N / v) ^ s ≤ (N / v) ^ s' := by
  have hq1 : 1 ≤ N / v := by
    rw [Nat.le_div_iff_mul_le hv]
    simpa [mul_comm] using hvN
  exact Nat.pow_le_pow_right (by omega : 0 < N / v) hss

/-- if `v ≤ N` and `N ≥ 2` then `N - v + 1 ≥ 1`, etc. -/
lemma exists_mem_range_choose {N v : ℕ} (hv : v ≤ N) : 0 < N.choose v ↔ v ≤ N := by
  constructor
  · intro _; exact hv
  · intro _; exact Nat.choose_pos hv

end Submission.CountLemmas
