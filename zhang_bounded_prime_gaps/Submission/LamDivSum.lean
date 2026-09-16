import Mathlib
import Submission.SieveExpansion

open scoped BigOperators Topology
open Finset Filter

set_option maxHeartbeats 2000000

/-!
# The one-dimensional divisor sum `λ_F`

Polymath8a (16) defines, for a smooth compactly supported `F`,
`λ_F(n) := Σ_{d | n} μ(d)·F(log_x d)`.  In this workspace the sum is truncated
at `D`, giving the formal object

    `lamDivSum F x D m = Σ_{d ≤ D, d | m} μ(d)·F(log m / log x)`

(`lamDivWeight F x d = μ(d)·F(log d / log x)`, `Submission/SieveExpansion.lean`).

The key algebraic fact used in the sieve is Polymath8a (20):

    `λ_F(m) = F(0)` whenever `m` is prime and `m ≥ x`,

provided `F` vanishes on `[1, ∞)` (in the paper `F` is supported on `[0,1]`).
-/

namespace Commons.NumberTheory.MaynardSieve

attribute [local instance] Classical.propDecidable

/-- The (truncated) one-dimensional divisor sum `λ_F(m) = Σ_{d ≤ D, d | m} μ(d)F(log_x d)`. -/
noncomputable def lamDivSum (F : ℝ → ℝ) (R D : ℕ) (m : ℕ) : ℝ :=
  ∑ d : Fin (D + 1), lamDivWeight F R (d : ℕ) * (if (d : ℕ) ∣ m then (1 : ℝ) else 0)

/-- `lamDivSum` as a sum over `Finset.Icc 1 D` (the `d = 0` term vanishes for `m > 0`). -/
lemma lamDivSum_eq_sum_Icc {F : ℝ → ℝ} {R D m : ℕ} (hm : 0 < m) :
    lamDivSum F R D m =
      ∑ d ∈ Finset.Icc 1 D, lamDivWeight F R d * (if d ∣ m then (1 : ℝ) else 0) := by
  rw [lamDivSum, Fin.sum_univ_eq_sum_range
    (fun d => lamDivWeight F R d * (if d ∣ m then (1 : ℝ) else 0)) (D + 1)]
  have hrange : Finset.range (D + 1) = insert 0 (Finset.Icc 1 D) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hrange, Finset.sum_insert (by simp)]
  have h0 : lamDivWeight F R 0 * (if (0 : ℕ) ∣ m then (1 : ℝ) else 0) = 0 := by
    have hz : ¬ ((0 : ℕ) ∣ m) := by
      rw [Nat.zero_dvd]
      omega
    rw [if_neg hz, mul_zero]
  rw [h0, zero_add]

/-- The `d = 1` term of the divisor sum is `F 0`. -/
lemma lamDivWeight_one (F : ℝ → ℝ) (R : ℕ) :
    lamDivWeight F R 1 = F 0 := by
  rw [lamDivWeight]
  have hlog1 : Real.log ((1 : ℕ) : ℝ) = 0 := by simp
  rw [hlog1, zero_div]
  norm_num [moebiusReal]

/-- The `d = m` term of the divisor sum for a prime `m ≥ x`. -/
lemma lamDivWeight_prime_eq_zero {F : ℝ → ℝ} {R m : ℕ} (hm : m.Prime) (hRm : R ≤ m)
    (hR1 : 1 < R) (hF : ∀ t : ℝ, 1 ≤ t → F t = 0) :
    lamDivWeight F R m = 0 := by
  rw [lamDivWeight]
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hlogpos : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR1)
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm.pos
  have hlogm : Real.log (R : ℝ) ≤ Real.log (m : ℝ) := Real.log_le_log hRpos (by exact_mod_cast hRm)
  have h1 : 1 ≤ Real.log (m : ℝ) / Real.log (R : ℝ) := by
    rw [le_div_iff₀ hlogpos]; linarith
  rw [hF _ h1, mul_zero]

/-- **Polymath8a (20)**: for a prime `m ≥ x`, `λ_F(m) = F(0)` when `F` vanishes on
`[1,∞)`. -/
theorem lamDivSum_prime {F : ℝ → ℝ} {R D m : ℕ} (hm : m.Prime) (hRm : R ≤ m) (hR1 : 1 < R)
    (hD : 1 ≤ D) (hF : ∀ t : ℝ, 1 ≤ t → F t = 0) :
    lamDivSum F R D m = F 0 := by
  have hmpos : 0 < m := hm.pos
  rw [lamDivSum_eq_sum_Icc hmpos]
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 D := Finset.mem_Icc.mpr ⟨le_rfl, hD⟩
  rw [Finset.sum_eq_single 1]
  · rw [if_pos (one_dvd m), mul_one, lamDivWeight_one F R]
  · intro d hd hd1
    obtain ⟨hd1', hdD⟩ := Finset.mem_Icc.mp hd
    by_cases hdiv : d ∣ m
    · rw [if_pos hdiv]
      have hdm : d = m := by
        rcases hm.eq_one_or_self_of_dvd d hdiv with h | h
        · exact absurd h hd1
        · exact h
      rw [hdm, mul_one]
      exact lamDivWeight_prime_eq_zero hm hRm hR1 hF
    · rw [if_neg hdiv, mul_zero]
  · intro h
    exact absurd h1mem h

end Commons.NumberTheory.MaynardSieve
