import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Bounds

namespace Commons.Algebra.Binomial

/-- Pascal's rule applied twice: `C(a+b+3, b+2)` splits as the sum of the "subtracted"
term `C(a+b+1, b)` and the two remaining binomial coefficients. -/
private lemma pascal_twice (a b : ℕ) :
    (a+b+3).choose (b+2) =
      (a+b+1).choose b + ((a+b+2).choose (b+2) + (a+b+1).choose (b+1)) := by
  have h1 : (a+b+3).choose (b+2) = (a+b+2).choose (b+1) + (a+b+2).choose (b+2) :=
    Nat.choose_succ_succ' (a+b+2) (b+1)
  have h2 : (a+b+2).choose (b+1) = (a+b+1).choose b + (a+b+1).choose (b+1) :=
    Nat.choose_succ_succ' (a+b+1) b
  rw [h1, h2]
  ring

/-- Consecutive binomial coefficients are monotone along the Pascal diagonal. -/
private lemma choose_diag_mono (a b : ℕ) :
    (a+b+1).choose (b+1) ≤ (a+b+2).choose (b+2) := by
  have h := Nat.choose_succ_succ' (a+b+1) (b+1)
  rw [h]
  exact Nat.le_add_right _ _

/-- A crude but sufficient growth bound: `C(a+b+2, b+2) ≤ (a+2)^a (b+3)^a`. -/
private lemma choose_growth (a b : ℕ) :
    (a+b+2).choose (b+2) ≤ (a+2)^a * (b+3)^a := by
  have hsym : (a+b+2).choose (b+2) = (a+b+2).choose a := by
    have h := Nat.choose_symm (n := a+b+2) (k := b+2) (by omega)
    rw [show a+b+2 - (b+2) = a by omega] at h
    exact h.symm
  rw [hsym]
  calc (a+b+2).choose a ≤ (a+b+2)^a := Nat.choose_le_pow _ _
    _ ≤ ((a+2)*(b+3))^a := Nat.pow_le_pow_left (by nlinarith [Nat.zero_le a, Nat.zero_le b]) a
    _ = (a+2)^a * (b+3)^a := by rw [mul_pow]

/-- The core arithmetic estimate, in the shifted parameters `n = a+2`, `k = b+2`. -/
private lemma harmonic_dim_arith_shifted (a b : ℕ) :
    ((a+b+3).choose (b+2) - (a+b+1).choose b) ≤ 2 * (a+2)^a * (b+3)^a := by
  have h1 := pascal_twice a b
  have h2 := choose_diag_mono a b
  have h3 := choose_growth a b
  have hCD : (a+b+2).choose (b+2) + (a+b+1).choose (b+1) ≤
      2 * ((a+2)^a * (b+3)^a) := by
    linarith
  have hA : (a+b+3).choose (b+2) ≤ (a+b+1).choose b + 2 * ((a+2)^a * (b+3)^a) := by
    rw [h1]; exact Nat.add_le_add_left hCD _
  have hEq : (a+b+1).choose b + 2 * ((a+2)^a * (b+3)^a) =
      2 * (a+2)^a * (b+3)^a + (a+b+1).choose b := by
    ring
  rw [Nat.sub_le_iff_le_add, ← hEq]
  exact hA

/-- Hadwiger's bound: the dimension of the space of harmonic polynomials of degree `k`
in `n` variables, `C(n+k-1,k) - C(n+k-3,k-2)`, is at most `2 n^(n-2) (k+1)^(n-2)`. -/
theorem harmonic_dim_arith (n k : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k) :
    (((n + k - 1).choose k - (n + k - 3).choose (k - 2) : ℕ) : ℝ)
      ≤ 2 * (n : ℝ) ^ (n - 2) * ((k : ℝ) + 1) ^ (n - 2) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hnat : ((2+a)+(2+b)-1).choose (2+b) - ((2+a)+(2+b)-3).choose ((2+b)-2)
      ≤ 2 * (2+a)^a * ((2+b)+1)^a := by
    have e1 : (2+a)+(2+b)-1 = a+b+3 := by omega
    have e2 : (2+a)+(2+b)-3 = a+b+1 := by omega
    have e3 : (2+b)-2 = b := by omega
    have e4 : 2+a = a+2 := by omega
    have e5 : (2+b)+1 = b+3 := by omega
    have e6 : 2+b = b+2 := by omega
    rw [e1, e2, e3, e5, e6, e4]
    exact harmonic_dim_arith_shifted a b
  have hcast : ((2 * (2+a)^a * ((2+b)+1)^a : ℕ) : ℝ)
      = 2 * ((2+a : ℕ) : ℝ)^a * (((2+b : ℕ) : ℝ) + 1)^a := by push_cast; ring
  have hsub : (2+a) - 2 = a := by omega
  rw [hsub]
  calc ((((2+a)+(2+b)-1).choose (2+b) - ((2+a)+(2+b)-3).choose ((2+b)-2) : ℕ) : ℝ)
      ≤ ((2 * (2+a)^a * ((2+b)+1)^a : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = 2 * ((2+a : ℕ) : ℝ)^a * (((2+b : ℕ) : ℝ) + 1)^a := hcast

end Commons.Algebra.Binomial