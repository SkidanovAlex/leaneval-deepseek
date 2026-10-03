import Mathlib
import Submission.Work.A3.Weil.Defs
import Submission.Commons.Algebra.Polynomial.signed_sum_pow_lower
import Submission.Commons.Analysis.ExponentialSums.hua_bound

set_option autoImplicit false

namespace Work.A3.Weil

open Polynomial Finset
open scoped BigOperators

/-- `Work.A3.Weil.iterDiff` agrees with the `Commons` finite-difference operator. -/
lemma iterDiff_eq_commons : ∀ (k : ℕ) (l : Fin k → ℤ) (φ : ℤ → ℝ) (n : ℤ),
    iterDiff k l φ n = Commons.Analysis.ExponentialSums.iterDiff φ k l n := by
  intro k
  induction k with
  | zero => intro l φ n; rfl
  | succ k ih =>
      intro l φ n
      simp only [iterDiff, Commons.Analysis.ExponentialSums.iterDiff]
      rw [ih (fun i => l i.castSucc) φ (n + l (Fin.last k)), ih (fun i => l i.castSucc) φ n]

/-- The `k`-fold difference as an alternating sum over subsets of the shifts. -/
lemma iterDiff_eq_sum (k : ℕ) (l : Fin k → ℤ) (φ : ℤ → ℝ) (n : ℤ) :
    iterDiff k l φ n
      = ∑ S : Finset (Fin k), (-1 : ℝ) ^ (k - S.card) * φ (n + ∑ i ∈ S, l i) := by
  rw [iterDiff_eq_commons, Commons.Analysis.ExponentialSums.iterDiff_eq_sum]

/-- Casting the signed alternating sum from `ℤ` to `ℝ`. -/
lemma cast_signed_sum (k : ℕ) (G : Finset (Fin k) → ℤ) :
    (∑ S : Finset (Fin k), (-1 : ℝ) ^ (k - S.card) * ((G S : ℤ) : ℝ))
      = ((∑ S : Finset (Fin k), (-1 : ℤ) ^ (k - S.card) * G S : ℤ) : ℝ) := by
  push_cast
  apply Finset.sum_congr rfl
  intro S _
  ring

/-- The top-degree signed identity: the `k`-fold difference of `x ↦ x ^{k+1}` is affine with
slope `(k+1)! · ∏ h`. -/
lemma signed_sum_pow_step (k : ℕ) (hk : 1 ≤ k) (l : Fin k → ℤ) :
    ∃ c : ℤ, ∀ z : ℤ,
      (∑ S : Finset (Fin k), (-1 : ℤ) ^ (k - S.card) * (z + ∑ i ∈ S, l i) ^ (k + 1))
        = (((k + 1).factorial : ℤ) * (∏ i, l i)) * z + c := by
  simpa using Commons.Algebra.Polynomial.signed_sum_pow_linear (k + 1) (by omega) l

/-- The signed alternating sum of a degree-`(k+1)` polynomial sampled at the shifted points
`z + ∑_{i ∈ S} h i` is affine in `z` with slope `(k+1)! · lc · ∏ h`. -/
lemma signed_eval_affine (Q : ℤ[X]) (k : ℕ) (hk : k + 1 = Q.natDegree) (hk1 : 1 ≤ k)
    (l : Fin k → ℤ) :
    ∃ c : ℤ, ∀ z : ℤ,
      (∑ S : Finset (Fin k), (-1 : ℤ) ^ (k - S.card) * Q.eval (z + ∑ i ∈ S, l i))
        = (((k + 1).factorial : ℤ) * Q.coeff (k + 1) * (∏ i, l i)) * z + c := by
  classical
  obtain ⟨c₀, hc₀⟩ := signed_sum_pow_step k hk1 l
  refine ⟨(k.factorial : ℤ) * Q.coeff k * (∏ i, l i) + Q.coeff (k + 1) * c₀, fun z => ?_⟩
  have hQ : ∀ w : ℤ, Q.eval w = ∑ i ∈ Finset.range (k + 2), Q.coeff i * w ^ i := by
    intro w
    rw [Polynomial.eval_eq_sum_range, ← hk]
  have key : (∑ S : Finset (Fin k), (-1 : ℤ) ^ (k - S.card) * Q.eval (z + ∑ i ∈ S, l i))
      = ∑ i ∈ Finset.range (k + 2), Q.coeff i *
          (∑ S : Finset (Fin k), (-1 : ℤ) ^ (k - S.card) * (z + ∑ i' ∈ S, l i') ^ i) := by
    calc ∑ S : Finset (Fin k), (-1 : ℤ) ^ (k - S.card) * Q.eval (z + ∑ i ∈ S, l i)
        = ∑ S : Finset (Fin k), (-1 : ℤ) ^ (k - S.card) *
            (∑ i ∈ Finset.range (k + 2), Q.coeff i * (z + ∑ i' ∈ S, l i') ^ i) := by
          apply Finset.sum_congr rfl; intro S _; rw [hQ]
      _ = ∑ i ∈ Finset.range (k + 2), ∑ S : Finset (Fin k),
            (-1 : ℤ) ^ (k - S.card) * (Q.coeff i * (z + ∑ i' ∈ S, l i') ^ i) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro S _; rw [Finset.mul_sum]
      _ = ∑ i ∈ Finset.range (k + 2), Q.coeff i *
            (∑ S : Finset (Fin k), (-1 : ℤ) ^ (k - S.card) * (z + ∑ i' ∈ S, l i') ^ i) := by
          apply Finset.sum_congr rfl; intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro S _; ring
  have hlow : (∑ i ∈ Finset.range (k + 1), Q.coeff i *
        (∑ S : Finset (Fin k), (-1 : ℤ) ^ (k - S.card) * (z + ∑ i' ∈ S, l i') ^ i))
      = (k.factorial : ℤ) * Q.coeff k * (∏ i, l i) := by
    have hif : ∀ i ∈ Finset.range (k + 1),
        (∑ S : Finset (Fin k), (-1 : ℤ) ^ (k - S.card) * (z + ∑ i' ∈ S, l i') ^ i)
          = if i = k then (k.factorial : ℤ) * (∏ i, l i) else 0 := by
      intro i hi
      exact Commons.Algebra.Polynomial.signed_sum_pow_lower (r := k) (m := i)
        (by have := Finset.mem_range.mp hi; omega) l z
    rw [Finset.sum_congr rfl (fun i hi => by rw [hif i hi])]
    rw [Finset.sum_eq_single k]
    · rw [if_pos rfl]; ring
    · intro b _ hbne; rw [if_neg hbne, mul_zero]
    · intro hknot; exact absurd (Finset.mem_range.mpr (by omega)) hknot
  have hval : (∑ i ∈ Finset.range (k + 2), Q.coeff i *
        (∑ S : Finset (Fin k), (-1 : ℤ) ^ (k - S.card) * (z + ∑ i' ∈ S, l i') ^ i))
      = (((k + 1).factorial : ℤ) * Q.coeff (k + 1) * (∏ i, l i)) * z
        + ((k.factorial : ℤ) * Q.coeff k * (∏ i, l i) + Q.coeff (k + 1) * c₀) := by
    rw [show k + 2 = (k + 1) + 1 from rfl, Finset.sum_range_succ, hlow, hc₀ z]
    ring
  rw [key, hval]

/-- The signed sum of the Weyl phase over the subsets of the shifts. -/
lemma weylPhase_sum_eq (Q : ℤ[X]) (θ : ℝ) (k : ℕ) (l : Fin k → ℤ) (n : ℤ) :
    (∑ S : Finset (Fin k), (-1 : ℝ) ^ (k - S.card) * weylPhase Q θ (n + ∑ i ∈ S, l i))
      = -θ * ((∑ S : Finset (Fin k), (-1 : ℤ) ^ (k - S.card) *
          Q.eval ((n + 1) + ∑ i ∈ S, l i) : ℤ) : ℝ) := by
  rw [show (∑ S : Finset (Fin k), (-1 : ℝ) ^ (k - S.card) * weylPhase Q θ (n + ∑ i ∈ S, l i))
      = ∑ S : Finset (Fin k), (-1 : ℝ) ^ (k - S.card) *
          (-θ * ((Q.eval ((n + 1) + ∑ i ∈ S, l i) : ℤ) : ℝ)) from by
    apply Finset.sum_congr rfl
    intro S _
    rw [weylPhase]
    congr 1
    have : n + ∑ i ∈ S, l i + 1 = (n + 1) + ∑ i ∈ S, l i := by ring
    rw [this]]
  rw [← cast_signed_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem iterDiff_weylPhase_affine (Q : Polynomial ℤ) (θ : ℝ) (k : ℕ) (hk : k + 1 = Q.natDegree)
    (l : Fin k → ℤ) :
    ∃ c : ℝ, ∀ n : ℤ,
      Work.A3.Weil.iterDiff k l (Work.A3.Weil.weylPhase Q θ) n = Work.A3.Weil.weylSlope Q θ k l * (n : ℝ) + c := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have hQ1 : Q.natDegree = 1 := by omega
    refine ⟨-θ * (((Q.coeff 0 : ℤ) : ℝ) + ((Q.coeff 1 : ℤ) : ℝ)), fun n => ?_⟩
    have hev : Q.eval (n + 1) = Q.coeff 0 + Q.coeff 1 * (n + 1) := by
      rw [Polynomial.eval_eq_sum_range, hQ1, Finset.sum_range_succ, Finset.sum_range_one]
      ring
    have hsl : weylSlope Q θ 0 l = -θ * ((Q.coeff 1 : ℤ) : ℝ) := by
      simp only [weylSlope, hQ1, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
      norm_num
    rw [show iterDiff 0 l (weylPhase Q θ) n = weylPhase Q θ n from rfl, weylPhase, hev, hsl]
    push_cast
    ring
  · obtain ⟨cint, hcint⟩ := signed_eval_affine Q k hk (by omega) l
    refine ⟨-θ * ((((k + 1).factorial : ℤ) * Q.coeff (k + 1) * (∏ i, l i) : ℤ) : ℝ)
      - θ * (cint : ℝ), fun n => ?_⟩
    rw [iterDiff_eq_sum k l (weylPhase Q θ) n, weylPhase_sum_eq Q θ k l n, hcint (n + 1)]
    have hsl : weylSlope Q θ k l
        = -θ * ((((k + 1).factorial : ℤ) * Q.coeff (k + 1) * (∏ i, l i) : ℤ) : ℝ) := by
      simp only [weylSlope]
      rw [← hk]
      push_cast
      ring
    rw [hsl]
    push_cast
    ring

end Work.A3.Weil
