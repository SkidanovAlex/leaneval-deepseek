import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.weil_bound_poly
import Submission.Commons.NumberTheory.DirichletCharacter.charSum_product_poly_weil

/-!
# A local Weil bound for a product of linear factors

`Commons.NumberTheory.DirichletCharacter.weil_local_bound` bounds the "correlation"

`∑ x, (∏ i, χ (x + a i)) * (∏ i, conj (χ (x + b i)))`

of two products of `r` linear factors of a non-trivial Dirichlet character `χ` modulo a
prime `p` by `2 * r * √p`, under the non-degeneracy hypothesis that
`(∏ (X + C (a i))) * (∏ (X + C (b i))) ^ (orderOf χ - 1)` is not a constant multiple of an
`orderOf χ`-th power.

The proof rewrites the summand pointwise: since `χ u ^ orderOf χ = 1` for every unit `u`,
one has `conj (χ (g x)) = χ (g x) ^ (orderOf χ - 1)`, so the correlation equals the single
polynomial character sum `∑ x, χ ((f * g ^ (orderOf χ - 1)) x)`.  Weil's bound for one-variable
multiplicative character sums (`weil_bound_poly`, the Bombieri--Stepanov theorem in the commons)
bounds this by the number of *distinct* roots of `f * g ^ (orderOf χ - 1)`, and those roots are
the union of the roots of `f` and of `g`, at most `deg f + deg g = 2r` of them.
-/

open Polynomial
open scoped BigOperators

namespace Commons.NumberTheory.DirichletCharacter

/-- For any element `b`, the complex conjugate of `χ b` is its inverse (both are `0` or a root
of unity). -/
private lemma wlb_star_char_eq_inv {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p)
    (b : ZMod p) : (starRingEnd ℂ) (χ b) = (χ b)⁻¹ := by
  rcases eq_or_ne b 0 with rfl | hb
  · rw [MulChar.map_zero]; simp
  · obtain ⟨u, rfl⟩ := isUnit_iff_ne_zero.mpr hb
    have hmul : χ ((u : ZMod p)) * (starRingEnd ℂ) (χ ((u : ZMod p))) = 1 := by
      rw [star_apply_char, ← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply_coe]
    exact eq_inv_of_mul_eq_one_right hmul

/-- Pointwise reduction of the two-product correlation to a single polynomial character sum:
`χ (f x) * conj (χ (g x)) = χ ((f * g ^ (orderOf χ - 1)) x)`. -/
private lemma wlb_term {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (f g : Polynomial (ZMod p)) (x : ZMod p) :
    χ (f.eval x) * (starRingEnd ℂ) (χ (g.eval x))
      = χ ((f * g ^ (orderOf χ - 1)).eval x) := by
  have hm2 : 2 ≤ orderOf χ := by
    have h1 : orderOf χ ≠ 1 := fun h => hχ (orderOf_eq_one_iff.mp h)
    have h2 : 1 ≤ orderOf χ := orderOf_pos χ
    omega
  rw [eval_mul, eval_pow]
  rcases eq_or_ne (g.eval x) 0 with hg0 | hg0
  · rw [hg0]
    simp [MulChar.map_zero, zero_pow (by omega : orderOf χ - 1 ≠ 0)]
  · have hunit : IsUnit (g.eval x) := isUnit_iff_ne_zero.mpr hg0
    rw [map_mul χ (f.eval x) ((g.eval x) ^ (orderOf χ - 1)), map_pow]
    have hpow : (χ (g.eval x)) ^ (orderOf χ - 1) = (χ (g.eval x))⁻¹ := by
      have h1 : (χ (g.eval x)) ^ orderOf χ = 1 := by
        have hp : (χ ^ orderOf χ) = (1 : DirichletCharacter ℂ p) := pow_orderOf_eq_one χ
        have h2 : (χ ^ orderOf χ) (g.eval x) = 1 := by rw [hp, MulChar.one_apply hunit]
        rwa [MulChar.pow_apply' χ (by omega : orderOf χ ≠ 0) (g.eval x)] at h2
      have h2 : (χ (g.eval x)) ^ orderOf χ
          = (χ (g.eval x)) ^ (orderOf χ - 1) * χ (g.eval x) := by
        conv_lhs => rw [show orderOf χ = (orderOf χ - 1) + 1 by omega]
        rw [pow_succ]
      rw [h2] at h1
      exact eq_inv_of_mul_eq_one_left h1
    rw [wlb_star_char_eq_inv χ (g.eval x), ← hpow]

theorem weil_local_bound {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (r : ℕ) (hr : 1 ≤ r) (a b : Fin r → ZMod p)
    (hgood : ∀ (c : ZMod p) (Q : Polynomial (ZMod p)),
      (∏ i, (Polynomial.X + Polynomial.C (a i) : Polynomial (ZMod p))) *
        (∏ i, (Polynomial.X + Polynomial.C (b i) : Polynomial (ZMod p)))^(orderOf χ - 1)
        ≠ Polynomial.C c * Q^(orderOf χ)) :
    ‖∑ x : ZMod p, (∏ i, χ (x + a i)) * (∏ i, (starRingEnd ℂ) (χ (x + b i)))‖
      ≤ (2*r:ℝ)*Real.sqrt (p : ℝ) := by
  classical
  have hm2 : 2 ≤ orderOf χ := by
    have h1 : orderOf χ ≠ 1 := fun h => hχ (orderOf_eq_one_iff.mp h)
    have h2 : 1 ≤ orderOf χ := orderOf_pos χ
    omega
  set f : Polynomial (ZMod p) := ∏ i, (Polynomial.X + Polynomial.C (a i) : Polynomial (ZMod p))
    with hf
  set g : Polynomial (ZMod p) := ∏ i, (Polynomial.X + Polynomial.C (b i) : Polynomial (ZMod p))
    with hg
  set P : Polynomial (ZMod p) := f * g ^ (orderOf χ - 1) with hP
  have hfdeg : f.natDegree = r := by
    rw [hf, Polynomial.natDegree_prod]
    · simp
    · intro i _
      exact Polynomial.X_add_C_ne_zero (a i)
  have hgdeg : g.natDegree = r := by
    rw [hg, Polynomial.natDegree_prod]
    · simp
    · intro i _
      exact Polynomial.X_add_C_ne_zero (b i)
  have hf0 : f ≠ 0 := by
    intro h
    have : r = 0 := by rw [← hfdeg, h]; simp
    omega
  have hg0 : g ≠ 0 := by
    intro h
    have : r = 0 := by rw [← hgdeg, h]; simp
    omega
  have hgpow0 : g ^ (orderOf χ - 1) ≠ 0 := pow_ne_zero _ hg0
  have hP0 : P ≠ 0 := by rw [hP]; exact mul_ne_zero hf0 hgpow0
  have hPdeg : 1 ≤ P.natDegree := by
    rw [hP, Polynomial.natDegree_mul hf0 hgpow0, Polynomial.natDegree_pow, hfdeg, hgdeg]
    exact le_trans hr (Nat.le_add_right r ((orderOf χ - 1) * r))
  have hnd : ∀ (c : ZMod p) (Q : Polynomial (ZMod p)), P ≠ Polynomial.C c * Q ^ orderOf χ := by
    intro c Q
    rw [hP, hf, hg]
    exact hgood c Q
  have hwb := weil_bound_poly p χ hχ P hP0 hPdeg hnd
  have hterm : ∀ x : ZMod p,
      (∏ i, χ (x + a i)) * (∏ i, (starRingEnd ℂ) (χ (x + b i))) = χ (P.eval x) := by
    intro x
    have hA : (∏ i, χ (x + a i)) = χ (f.eval x) := by
      rw [hf, Polynomial.eval_prod]
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      exact (map_prod χ (fun i => x + a i) Finset.univ).symm
    have hBg : (∏ i, χ (x + b i)) = χ (g.eval x) := by
      rw [hg, Polynomial.eval_prod]
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      exact (map_prod χ (fun i => x + b i) Finset.univ).symm
    have hB : (∏ i, (starRingEnd ℂ) (χ (x + b i))) = (starRingEnd ℂ) (χ (g.eval x)) := by
      rw [← map_prod (starRingEnd ℂ) (fun i => χ (x + b i)) Finset.univ, hBg]
    rw [hA, hB]
    exact wlb_term χ hχ f g x
  have hsum_eq : (∑ x : ZMod p, (∏ i, χ (x + a i)) * (∏ i, (starRingEnd ℂ) (χ (x + b i))))
      = ∑ x : ZMod p, χ (P.eval x) :=
    Finset.sum_congr rfl (fun x _ => hterm x)
  rw [hsum_eq]
  calc ‖∑ x : ZMod p, χ (P.eval x)‖
      ≤ ((P.rootSet (AlgebraicClosure (ZMod p))).ncard : ℝ) * Real.sqrt (p : ℝ) := hwb
    _ ≤ (2*r:ℝ) * Real.sqrt (p : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        have h := ncard_rootSet_mul_pow_le p f g (orderOf χ - 1) (by omega)
        rw [← hP] at h
        rw [hfdeg, hgdeg] at h
        have h2 : (P.rootSet (AlgebraicClosure (ZMod p))).ncard ≤ 2 * r := by omega
        have h3 : ((P.rootSet (AlgebraicClosure (ZMod p))).ncard : ℝ) ≤ (2 : ℝ) * (r : ℝ) := by
          exact_mod_cast h2
        simpa using h3

end Commons.NumberTheory.DirichletCharacter
