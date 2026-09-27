import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Matrix.Reflection
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

/-!
# Extending a primitive integral vector to a unimodular matrix

For a primitive vector `m : Fin 3 → ℤ` (one whose entries have gcd `1`) we show that
`m` occurs as the first column of a matrix `A : Matrix (Fin 3) (Fin 3) ℤ` of
determinant `1`.  Equivalently, `SL₃(ℤ)` acts transitively on primitive vectors.

## Construction

Write `m = (a,b,c)`.

* If `b = 0`, set `g = gcd a c = 1` and use Bézout `a x + c y = 1` to build the
  explicit matrix `!![a,0,-y; 0,1,0; c,0,x]` of determinant `1`.
* If `a = 0`, use Bézout `b α + c β = 1` to build `!![0,1,0; b,0,β; c,0,-α]`.
* In the remaining case `a ≠ 0 ≠ b`, let `g = gcd a b > 0`, `a' = a/g`, `b' = b/g`
  and `x = gcdA a b`, `y = gcdB a b`, so that `a x + b y = g`.  With Bézout data
  `g x' + c y' = 1` for the (primitive) pair `(g,c)`, the product
  `R⁻¹ · B = !![a',-y,0; b',x,0; 0,0,1] * !![g,0,-y'; 0,1,0; c,0,x']`
  has determinant `1` and first column `(a',g, b'g, c) = (a,b,c)`.
-/

namespace Work.EKLComp

open Matrix

theorem exists_unimodular_first_column (m : Fin 3 → ℤ) (hm : m ≠ 0)
    (hprim : ∀ k : ℤ, (∀ i, k ∣ m i) → k = 1 ∨ k = -1) :
    ∃ A : Matrix (Fin 3) (Fin 3) ℤ, A.det = 1 ∧ ∀ i : Fin 3, A i 0 = m i := by
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, m = ![a, b, c] :=
    ⟨m 0, m 1, m 2, by funext i; fin_cases i <;> rfl⟩
  -- Rephrase primitivity as a statement about the three entries.
  have hdiv : ∀ k : ℤ, k ∣ a → k ∣ b → k ∣ c → k = 1 ∨ k = -1 := by
    intro k ha hb hc
    refine hprim k (fun i => ?_)
    fin_cases i <;> simp_all
  by_cases hb : b = 0
  · -- Case `b = 0`: use Bézout on `(a,c)`.
    subst hb
    have hgcd : ((Int.gcd a c : ℕ) : ℤ) = 1 := by
      have h := hdiv _ (Int.gcd_dvd_left a c) (dvd_zero _) (Int.gcd_dvd_right a c)
      rcases h with h | h
      · exact h
      · have := Int.gcd_nonneg a c
        omega
    have hbez : a * Int.gcdA a c + c * Int.gcdB a c = 1 := by
      have h := Int.gcd_eq_gcd_ab a c
      rw [hgcd] at h
      exact h.symm
    refine ⟨!![a, 0, -(Int.gcdB a c); 0, 1, 0; c, 0, Int.gcdA a c], ?_, ?_⟩
    · simp [Matrix.det_fin_three]; linarith
    · intro i; fin_cases i <;> simp
  · by_cases ha : a = 0
    · -- Case `a = 0 ≠ b`: use Bézout on `(b,c)`.
      subst ha
      have hgcd : ((Int.gcd b c : ℕ) : ℤ) = 1 := by
        have h := hdiv _ (dvd_zero _) (Int.gcd_dvd_left b c) (Int.gcd_dvd_right b c)
        rcases h with h | h
        · exact h
        · have := Int.gcd_nonneg b c; linarith
      have hbez : b * Int.gcdA b c + c * Int.gcdB b c = 1 := by
        have h := Int.gcd_eq_gcd_ab b c
        rw [hgcd] at h
        exact h.symm
      refine ⟨!![0, 1, 0; b, 0, Int.gcdB b c; c, 0, -(Int.gcdA b c)], ?_, ?_⟩
      · simp [Matrix.det_fin_three]; linarith
      · intro i; fin_cases i <;> simp
    · -- Case `a ≠ 0 ≠ b`: reduce the pair `(a,b)` to `(g,0)` and then use Case `b = 0`.
      set g : ℤ := ((Int.gcd a b : ℕ) : ℤ) with hg_def
      have hgpos : 0 < g := by
        rw [hg_def]
        exact_mod_cast Int.gcd_pos_of_ne_zero_left b ha
      have hgne : g ≠ 0 := ne_of_gt hgpos
      have hgdvd_a : g ∣ a := by rw [hg_def]; exact Int.gcd_dvd_left a b
      have hgdvd_b : g ∣ b := by rw [hg_def]; exact Int.gcd_dvd_right a b
      have hbez1 : a * Int.gcdA a b + b * Int.gcdB a b = g := by
        have h := Int.gcd_eq_gcd_ab a b
        rw [← hg_def] at h
        exact h.symm
      set a' : ℤ := a / g with ha'_def
      set b' : ℤ := b / g with hb'_def
      have h3 : a' * g = a := by rw [ha'_def]; exact Int.ediv_mul_cancel hgdvd_a
      have h4 : b' * g = b := by rw [hb'_def]; exact Int.ediv_mul_cancel hgdvd_b
      -- `(g,c)` is primitive, so Bézout data exists.
      have hgcd_gc : ((Int.gcd g c : ℕ) : ℤ) = 1 := by
        have h := hdiv _ (dvd_trans (Int.gcd_dvd_left g c) hgdvd_a)
          (dvd_trans (Int.gcd_dvd_left g c) hgdvd_b) (Int.gcd_dvd_right g c)
        rcases h with h | h
        · exact h
        · have := Int.gcd_nonneg g c; linarith
      have hbez2 : g * Int.gcdA g c + c * Int.gcdB g c = 1 := by
        have h := Int.gcd_eq_gcd_ab g c
        rw [hgcd_gc] at h
        exact h.symm
      -- The determinant of the reduction matrix.
      have hdetR : (!![a', -Int.gcdB a b, 0; b', Int.gcdA a b, 0; 0, 0, 1] :
          Matrix (Fin 3) (Fin 3) ℤ).det = 1 := by
        simp only [Matrix.det_fin_three]
        have key : a' * Int.gcdA a b + Int.gcdB a b * b' = 1 := by
          have k2 : (a' * Int.gcdA a b + Int.gcdB a b * b') * g = 1 * g := by
            linear_combination (Int.gcdA a b) * h3 + (Int.gcdB a b) * h4 + hbez1
          exact mul_right_cancel₀ hgne k2
        simp [key]
      refine ⟨!![a', -Int.gcdB a b, 0; b', Int.gcdA a b, 0; 0, 0, 1] *
        !![g, 0, -(Int.gcdB g c); 0, 1, 0; c, 0, Int.gcdA g c], ?_, ?_⟩
      · rw [Matrix.det_mul, hdetR]
        simp [Matrix.det_fin_three]
        linarith
      · intro i
        fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h3, h4]

end Work.EKLComp
