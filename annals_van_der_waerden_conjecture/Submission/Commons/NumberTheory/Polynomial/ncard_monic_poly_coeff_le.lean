import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Star
import Mathlib.Data.Set.Card

open Finset

namespace Commons.NumberTheory.Polynomial

/-- A polynomial of degree `n` (in the sense `natDegree`) is determined by its coefficients
`0, …, n`. -/
private lemma ext_of_coeff_eq {P Q : Polynomial ℤ} {n : ℕ} (hP : P.natDegree = n)
    (hQ : Q.natDegree = n) (h : ∀ i ≤ n, P.coeff i = Q.coeff i) : P = Q := by
  ext k
  by_cases hk : k ≤ n
  · exact h k hk
  · push Not at hk
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-- The number of monic integer polynomials of degree `n` whose `i`-th coefficient is bounded
by `B i` is at most `∏_{i = 0}^{n} (2 * B i + 1)`. -/
theorem ncard_monic_poly_coeff_le {n : ℕ} (B : ℕ → ℝ) (hB : ∀ i, 0 ≤ B i) :
    ((Set.ncard {P : Polynomial ℤ | P.Monic ∧ P.natDegree = n ∧
      ∀ i ≤ n, |((P.coeff i : ℤ) : ℝ)| ≤ B i} : ℕ) : ℝ) ≤
      ∏ i ∈ Finset.range (n + 1), (2 * B i + 1) := by
  classical
  set S : Set (Polynomial ℤ) := {P | P.Monic ∧ P.natDegree = n ∧
      ∀ i ≤ n, |((P.coeff i : ℤ) : ℝ)| ≤ B i} with hS
  change ((S.ncard : ℕ) : ℝ) ≤ ∏ i ∈ Finset.range (n + 1), (2 * B i + 1)
  -- The coefficients of any `P ∈ S` lie in `[-⌊B i⌋, ⌊B i⌋]`.
  set C : Fin (n + 1) → Finset ℤ := fun i => Finset.Icc (-(⌊B (i : ℕ)⌋)) (⌊B (i : ℕ)⌋) with hC
  -- The coefficient map is injective on `S` and lands in the box `∏ i, C i`.
  have hsub : ∀ P ∈ S, (fun i : Fin (n + 1) => P.coeff (i : ℕ)) ∈
      (Fintype.piFinset C : Set (Fin (n + 1) → ℤ)) := by
    intro P hP
    rw [hS] at hP
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [hC]
    simp only [Finset.mem_Icc]
    have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
    obtain ⟨h1, h2⟩ := abs_le.mp (hP.2.2 (i : ℕ) hi)
    refine ⟨?_, Int.le_floor.mpr h2⟩
    have hthis : ((-(P.coeff (i : ℕ)) : ℤ) : ℝ) ≤ B (i : ℕ) := by
      have : -(P.coeff (i : ℕ) : ℝ) ≤ B (i : ℕ) := by linarith
      simpa using this
    have h3 := Int.le_floor.mpr hthis
    linarith
  have hinj : Set.InjOn (fun P : Polynomial ℤ => fun i : Fin (n + 1) => P.coeff (i : ℕ)) S := by
    intro P hP Q hQ heq
    rw [hS] at hP hQ
    apply ext_of_coeff_eq hP.2.1 hQ.2.1
    intro k hk
    have := congrFun heq ⟨k, Nat.lt_succ_of_le hk⟩
    simpa using this
  have hle : S.ncard ≤ (Fintype.piFinset C).card := by
    have := Set.ncard_le_ncard_of_injOn (s := S)
      (fun P : Polynomial ℤ => fun i : Fin (n + 1) => P.coeff (i : ℕ)) hsub hinj
    rwa [Set.ncard_coe_finset] at this
  -- Each box factor has at most `2 * B i + 1` elements.
  have hcardC : ∀ i : Fin (n + 1), ((C i).card : ℝ) ≤ 2 * B (i : ℕ) + 1 := by
    intro i
    have hK1 : -(⌊B (i : ℕ)⌋) ≤ ⌊B (i : ℕ)⌋ + 1 := by
      have := Int.floor_nonneg.mpr (hB (i : ℕ)); omega
    have h1 : ((C i).card : ℤ) = 2 * ⌊B (i : ℕ)⌋ + 1 := by
      rw [hC, Int.card_Icc_of_le (-(⌊B (i : ℕ)⌋)) (⌊B (i : ℕ)⌋) hK1]; ring
    have h2 : ((C i).card : ℝ) = 2 * (⌊B (i : ℕ)⌋ : ℝ) + 1 := by
      exact_mod_cast h1
    rw [h2]
    have hf : (⌊B (i : ℕ)⌋ : ℝ) ≤ B (i : ℕ) := Int.floor_le _
    linarith
  calc ((S.ncard : ℕ) : ℝ)
      ≤ ((Fintype.piFinset C).card : ℝ) := by exact_mod_cast hle
    _ = ∏ i : Fin (n + 1), ((C i).card : ℝ) := by
          rw [Fintype.card_piFinset]; push_cast; rfl
    _ ≤ ∏ i : Fin (n + 1), (2 * B (i : ℕ) + 1) :=
          Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hcardC i)
    _ = ∏ i ∈ Finset.range (n + 1), (2 * B i + 1) := by
          rw [Fin.prod_univ_eq_prod_range (fun i => 2 * B i + 1) (n + 1)]

end Commons.NumberTheory.Polynomial