import Mathlib
import Submission.CDTPlan.InterfacesA

/-!
# Zagier's `c_n`: the explicit formula, harmonic numbers and the certificate polynomial

This module sets up the objects used to prove the integrality
`8·[1..n]²·c_n ∈ ℤ` of Zagier's sporadic sequence `c_n`
(`Submission.CDT.HC_coeff`) — the statement `Work.ZagC.zagier_c_integrality`.

The mathematical content is the explicit formula

  `c_n = Σ_{m ≤ n} C(n,m) g_m`,
  `g_m = Σ_{k ≤ m} C(m,k)³ ( (H2_k + H2_{m-k})/8 + (3/8)(H_k - H_{m-k})² )`,

whose key ingredient is the fact that `g` is the second solution of Franel's
recurrence `(m+1)²g_{m+1} = (7m²+7m+2)g_m + 8m²g_{m-1}` (Franel's recurrence is
satisfied by the Franel numbers `Σ_k C(m,k)³`).  We prove the recurrence for the
*explicit* `g` by creative telescoping, exploiting that `g_m` is (a multiple of)
the `ε²`-coefficient of the `ε`-deformed Franel sum `Σ_k C(m,k+ε)³`.

Concretely, writing `t2(M,K)` for the `ε²`-coefficient of `C(M,K+ε)³` up to the
irrelevant `ζ(2)` multiple, the certificate polynomial `Ncert` of Franel gives the
termwise telescoping identity

  `LFop (fun j => t2 j k) m = Y2 m (k+1) - Y2 m k`

where `Y2` is the `ε²`-coefficient of the deformed carrier
`C(m+1,k+ε)³·Ncert(m,k+ε)/(m(m+1)³)`.  Summing over `k` gives Franel's
recurrence for `Y = Σ_k t2(m,k) = 12 g_m`.
-/

namespace Work.ZagC

open Finset
open scoped BigOperators

noncomputable section

/-! ### Harmonic numbers -/

/-- The harmonic numbers `H_m = Σ_{j=1}^m 1/j`, as rationals. -/
def Hh (m : ℕ) : ℚ := ∑ j ∈ Finset.Icc 1 m, ((j : ℚ))⁻¹

/-- The second-order harmonic numbers `H2_m = Σ_{j=1}^m 1/j²`. -/
def H2h (m : ℕ) : ℚ := ∑ j ∈ Finset.Icc 1 m, (((j : ℚ))⁻¹) ^ 2

@[simp] lemma Hh_zero : Hh 0 = 0 := by simp [Hh]
@[simp] lemma H2h_zero : H2h 0 = 0 := by simp [H2h]
@[simp] lemma Hh_one : Hh 1 = 1 := by norm_num [Hh]
@[simp] lemma H2h_one : H2h 1 = 1 := by norm_num [H2h]

lemma Hh_succ (n : ℕ) : Hh (n + 1) = Hh n + (((n + 1 : ℕ)) : ℚ)⁻¹ := by
  unfold Hh
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]

lemma H2h_succ (n : ℕ) : H2h (n + 1) = H2h n + ((((n + 1 : ℕ)) : ℚ)⁻¹) ^ 2 := by
  unfold H2h
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]

lemma Hh_pred (n : ℕ) : Hh (n - 1) = Hh n - (((n : ℕ)) : ℚ)⁻¹ := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [Nat.succ_sub_one, Hh_succ]
    ring

lemma H2h_pred (n : ℕ) : H2h (n - 1) = H2h n - ((((n : ℕ)) : ℚ)⁻¹) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [Nat.succ_sub_one, H2h_succ]
    ring

/-! ### The Zeilberger certificate of Franel's recurrence -/

/-- The certificate polynomial `Ñ(m,k) = k³(4k³ − 18k²m − 12k² + 27km² + 39km + 12k − 14m³ − 32m² − 22m − 4)`
satisfying `Π(m,k)·m(k+1)³(m+1−k)³ = Ñ(k+1)(m+1−k)³ − Ñ(k)(k+1)³`
with `Π(m,k) = (m+1)²((m+1)/(m+1−k))³ − (7m²+7m+2) − 8m²((m−k)/m)³`. -/
def Ncert (m k : ℕ) : ℚ :=
  ((k : ℚ)) ^ 3 * (4 * ((k : ℚ)) ^ 3 - 18 * ((k : ℚ)) ^ 2 * (m : ℚ) - 12 * ((k : ℚ)) ^ 2
    + 27 * (k : ℚ) * (m : ℚ) ^ 2 + 39 * (k : ℚ) * (m : ℚ) + 12 * (k : ℚ)
    - 14 * (m : ℚ) ^ 3 - 32 * (m : ℚ) ^ 2 - 22 * (m : ℚ) - 4)

/-- The `k`-derivative of the certificate polynomial `Ncert`. -/
def dNcert (m k : ℕ) : ℚ :=
  3 * ((k : ℚ)) ^ 2 * (4 * ((k : ℚ)) ^ 3 - 18 * ((k : ℚ)) ^ 2 * (m : ℚ) - 12 * ((k : ℚ)) ^ 2
    + 27 * (k : ℚ) * (m : ℚ) ^ 2 + 39 * (k : ℚ) * (m : ℚ) + 12 * (k : ℚ)
    - 14 * (m : ℚ) ^ 3 - 32 * (m : ℚ) ^ 2 - 22 * (m : ℚ) - 4)
  + ((k : ℚ)) ^ 3 * (12 * ((k : ℚ)) ^ 2 - 36 * (k : ℚ) * (m : ℚ) - 24 * (k : ℚ)
    + 27 * (m : ℚ) ^ 2 + 39 * (m : ℚ) + 12)

/-- The second `k`-derivative of the certificate polynomial `Ncert`. -/
def ddNcert (m k : ℕ) : ℚ :=
  6 * (k : ℚ) * (4 * ((k : ℚ)) ^ 3 - 18 * ((k : ℚ)) ^ 2 * (m : ℚ) - 12 * ((k : ℚ)) ^ 2
    + 27 * (k : ℚ) * (m : ℚ) ^ 2 + 39 * (k : ℚ) * (m : ℚ) + 12 * (k : ℚ)
    - 14 * (m : ℚ) ^ 3 - 32 * (m : ℚ) ^ 2 - 22 * (m : ℚ) - 4)
  + 6 * ((k : ℚ)) ^ 2 * (12 * ((k : ℚ)) ^ 2 - 36 * (k : ℚ) * (m : ℚ) - 24 * (k : ℚ)
    + 27 * (m : ℚ) ^ 2 + 39 * (m : ℚ) + 12)
  + ((k : ℚ)) ^ 3 * (24 * (k : ℚ) - 36 * (m : ℚ) - 24)

/-! ### The deformation data -/

/-- The `ε²`-coefficient of the deformed binomial cube `C(M,K+ε)³`
(the `ζ(2)`-multiple is dropped: it is annihilated by Franel's recurrence). -/
def t2 (M K : ℕ) : ℚ :=
  ((M.choose K : ℚ)) ^ 3 *
    ((9 / 2) * (Hh K - Hh (M - K)) ^ 2 + (3 / 2) * (H2h K + H2h (M - K)))

/-- The summand of the explicit formula for `g_m`; `t2 = 12 · sm`. -/
def sm (M K : ℕ) : ℚ :=
  ((M.choose K : ℚ)) ^ 3 *
    ((3 / 8) * (Hh K - Hh (M - K)) ^ 2 + (1 / 8) * (H2h K + H2h (M - K)))

lemma t2_eq_sm (M K : ℕ) : t2 M K = 12 * sm M K := by
  unfold t2 sm; ring

/-- The `ε²`-coefficient of the deformed telescoping carrier
`C(m+1,k+ε)³ · Ñ(m,k+ε) / (m(m+1)³)`. -/
def Y2 (m K : ℕ) : ℚ :=
  ((((m + 1).choose K : ℚ)) ^ 3
      * ((9 / 2) * (Hh K - Hh (m + 1 - K)) ^ 2 + (3 / 2) * (H2h K + H2h (m + 1 - K)))
      * Ncert m K
    + (-3 * (((m + 1).choose K : ℚ)) ^ 3 * (Hh K - Hh (m + 1 - K))) * dNcert m K
    + (((m + 1).choose K : ℚ)) ^ 3 * ddNcert m K / 2)
  / ((m : ℚ) * (((m + 1 : ℕ)) : ℚ) ^ 3)

@[simp] lemma t2_eq_zero_of_lt {M K : ℕ} (h : M < K) : t2 M K = 0 := by
  unfold t2
  rw [Nat.choose_eq_zero_of_lt h]
  norm_num

@[simp] lemma sm_eq_zero_of_lt {M K : ℕ} (h : M < K) : sm M K = 0 := by
  unfold sm
  rw [Nat.choose_eq_zero_of_lt h]
  norm_num

lemma Y2_eq_zero_of_lt {m K : ℕ} (h : m + 1 < K) : Y2 m K = 0 := by
  unfold Y2
  rw [Nat.choose_eq_zero_of_lt h]
  norm_num

@[simp] lemma Y2_zero (m : ℕ) : Y2 m 0 = 0 := by
  unfold Y2 Ncert dNcert ddNcert
  norm_num

/-! ### The two recurrences -/

/-- Franel's recurrence operator `L_F`: `(m+1)²u_{m+1} − (7m²+7m+2)u_m − 8m²u_{m−1}`. -/
def LFop (u : ℕ → ℚ) (m : ℕ) : ℚ :=
  (((m + 1 : ℕ)) : ℚ) ^ 2 * u (m + 1)
    - (7 * (m : ℚ) ^ 2 + 7 * (m : ℚ) + 2) * u m
    - 8 * (m : ℚ) ^ 2 * u (m - 1)

/-- The (inhomogeneous) Zagier recurrence operator `L_C`:
`(m+1)²u_{m+1} − (10m²+10m+3)u_m + 9m²u_{m−1}`. -/
def LCop (u : ℕ → ℚ) (m : ℕ) : ℚ :=
  (((m + 1 : ℕ)) : ℚ) ^ 2 * u (m + 1)
    - (10 * (m : ℚ) ^ 2 + 10 * (m : ℚ) + 3) * u m
    + 9 * (m : ℚ) ^ 2 * u (m - 1)

/-- The explicit second solution of Franel's recurrence. -/
def g (m : ℕ) : ℚ := ∑ k ∈ Finset.range (m + 1), sm m k

/-- `t2`-sum: `12 · g_m`. -/
def YY (m : ℕ) : ℚ := ∑ k ∈ Finset.range (m + 1), t2 m k

/-- The binomial transform `n ↦ Σ_{m ≤ n} C(n,m) u_m`. -/
def Cfun (u : ℕ → ℚ) (n : ℕ) : ℚ := ∑ m ∈ Finset.range (n + 1), (n.choose m : ℚ) * u m

lemma YY_eq_twelve_g (m : ℕ) : YY m = 12 * g m := by
  unfold YY g
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [t2_eq_sm]

end

end Work.ZagC
