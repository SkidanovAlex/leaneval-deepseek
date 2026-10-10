import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Rat.Star
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Ring.Star
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Cauchy's root bound: an algebraic element of a linearly ordered field is dominated by a natural

Let `K` be a linearly ordered field (more precisely a field with `LinearOrder` and
`IsStrictOrderedRing`, which is Mathlib's way of writing "linearly ordered field").  If
`x : K` is a root of a non-zero polynomial `p ∈ ℚ[X]`, i.e. `(aeval x) p = 0`, then `x` is
algebraic over `ℚ` and Cauchy's root bound provides an integral domination of `x`:

  `|x| ≤ max 1 ((∑_{i < deg p} |p_i|) / |p_{deg p}|)`,

a rational constant.  Since `ℚ` is Archimedean, this constant is below some natural number,
which gives the statement `∃ n : ℕ, x ≤ (n : K)`.

This is the only ingredient missing from `Mathlib` for the fact that the order of the fixed
field of an involution of `ℚ̄` is Archimedean (see `InvAux/exists_orderEmbedding.lean`).
-/

namespace Work.SSGRoute.InvAux

open Finset

/-- Cauchy's root bound in a linearly ordered field, with the rational constant made explicit:
a root `x` of a non-zero `p : ℚ[X]` satisfies `|x| ≤ max 1 (S / |leadingCoeff|)` where
`S = ∑_{i < deg p} |p.coeff i|`. -/
lemma abs_le_of_aeval_eq_zero {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {p : Polynomial ℚ} (hp : p ≠ 0) {x : K} (hx : (Polynomial.aeval x) p = 0) :
    |x| ≤
      ((max 1 ((∑ i ∈ Finset.range p.natDegree, |p.coeff i|) / |p.coeff p.natDegree|) : ℚ) :
        K) := by
  set d := p.natDegree with hd
  -- `p` is not a non-zero constant, so `d ≥ 1`.
  have hd1 : 1 ≤ d := by
    rw [hd]
    by_contra h
    rw [not_le, Nat.lt_one_iff] at h
    have hpC : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h
    have hzero : (algebraMap ℚ K) (p.coeff 0) = 0 := by
      have h' := hx
      rw [hpC, Polynomial.aeval_C] at h'
      exact h'
    have hc0 : p.coeff 0 ≠ 0 := by
      have heq : p.coeff 0 = p.leadingCoeff := by rw [← h]; exact Polynomial.coeff_natDegree
      rw [heq]; exact Polynomial.leadingCoeff_ne_zero.mpr hp
    exact hc0 (Rat.cast_eq_zero.mp hzero)
  -- the leading coefficient is non-zero
  have hc : p.coeff d ≠ 0 := by
    rw [hd, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  -- write `p(x) = 0` as a sum over coefficients
  have hsum : ∑ i ∈ Finset.range (d + 1), ((p.coeff i : ℚ) : K) * x ^ i = 0 := by
    have h' := hx
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range] at h'
    simpa [hd] using h'
  -- isolate the leading term
  have hsplit : ((p.coeff d : ℚ) : K) * x ^ d
      = -∑ i ∈ Finset.range d, ((p.coeff i : ℚ) : K) * x ^ i := by
    have h := hsum
    rw [Finset.sum_range_succ] at h
    linarith
  -- take absolute values
  have habs : |((p.coeff d : ℚ) : K)| * |x| ^ d
      ≤ ∑ i ∈ Finset.range d, |((p.coeff i : ℚ) : K)| * |x| ^ i := by
    calc |((p.coeff d : ℚ) : K)| * |x| ^ d
        = |((p.coeff d : ℚ) : K) * x ^ d| := by rw [abs_mul, abs_pow]
      _ = |∑ i ∈ Finset.range d, ((p.coeff i : ℚ) : K) * x ^ i| := by rw [hsplit, abs_neg]
      _ ≤ ∑ i ∈ Finset.range d, |((p.coeff i : ℚ) : K) * x ^ i| :=
            Finset.abs_sum_le_sum_abs (fun i => ((p.coeff i : ℚ) : K) * x ^ i) (Finset.range d)
      _ = ∑ i ∈ Finset.range d, |((p.coeff i : ℚ) : K)| * |x| ^ i := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [abs_mul, abs_pow]
  -- the estimate, in the regime `1 ≤ |x|`
  have key : (1 : K) ≤ |x| →
      |x| ≤ (((∑ i ∈ Finset.range d, |p.coeff i|) / |p.coeff d| : ℚ) : K) := by
    intro hx1
    have hterm : ∑ i ∈ Finset.range d, |((p.coeff i : ℚ) : K)| * |x| ^ i
        ≤ (∑ i ∈ Finset.range d, |((p.coeff i : ℚ) : K)|) * |x| ^ (d - 1) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum ?_
      intro i hi
      have hi' : i ≤ d - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.mp hi)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx1 hi') (abs_nonneg _)
    have hcomb : |((p.coeff d : ℚ) : K)| * |x| ^ d
        ≤ (∑ i ∈ Finset.range d, |((p.coeff i : ℚ) : K)|) * |x| ^ (d - 1) :=
      le_trans habs hterm
    have hxd : |x| ^ d = |x| * |x| ^ (d - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hd1]
      rw [pow_succ']
    have hcancel : |((p.coeff d : ℚ) : K)| * |x|
        ≤ ∑ i ∈ Finset.range d, |((p.coeff i : ℚ) : K)| := by
      have hpos : 0 < |x| ^ (d - 1) := pow_pos (lt_of_lt_of_le zero_lt_one hx1) _
      have h := hcomb
      rw [hxd, ← mul_assoc] at h
      exact (mul_le_mul_iff_of_pos_right hpos).mp h
    have hck_pos : 0 < |((p.coeff d : ℚ) : K)| := by
      rw [abs_pos]
      exact Rat.cast_ne_zero.mpr hc
    have hbd : |x| ≤
        (∑ i ∈ Finset.range d, |((p.coeff i : ℚ) : K)|) / |((p.coeff d : ℚ) : K)| := by
      rw [le_div_iff₀ hck_pos, mul_comm]
      exact hcancel
    have hSU : (∑ i ∈ Finset.range d, |((p.coeff i : ℚ) : K)|)
        = ((∑ i ∈ Finset.range d, |p.coeff i| : ℚ) : K) := by
      rw [Rat.cast_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Rat.cast_abs]
    have hcd : |((p.coeff d : ℚ) : K)| = ((|p.coeff d| : ℚ) : K) := by rw [Rat.cast_abs]
    rw [Rat.cast_div, ← hSU, ← hcd]
    exact hbd
  have hfin : |x| ≤ max (1 : K)
      (((∑ i ∈ Finset.range d, |p.coeff i|) / |p.coeff d| : ℚ) : K) := by
    by_cases hxx : |x| ≤ 1
    · exact le_trans hxx (le_max_left _ _)
    · exact le_trans (key (le_of_lt (not_le.mp hxx))) (le_max_right _ _)
  have hmaxcast : ((max 1 ((∑ i ∈ Finset.range d, |p.coeff i|) / |p.coeff d|) : ℚ) : K)
      = max (1 : K) (((∑ i ∈ Finset.range d, |p.coeff i|) / |p.coeff d| : ℚ) : K) := by
    rw [Rat.cast_max, Rat.cast_one]
  rw [hmaxcast]
  exact hfin

theorem exists_nat_ge_of_aeval_eq_zero {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {p : Polynomial ℚ} (hp : p ≠ 0) {x : K} (hx : (Polynomial.aeval x) p = 0) :
    ∃ n : ℕ, x ≤ (n : K) := by
  obtain ⟨n, hn⟩ :=
    exists_nat_ge (max 1 ((∑ i ∈ Finset.range p.natDegree, |p.coeff i|) / |p.coeff p.natDegree|))
  refine ⟨n, ?_⟩
  have hb := abs_le_of_aeval_eq_zero hp hx
  have hcast : ((max 1
      ((∑ i ∈ Finset.range p.natDegree, |p.coeff i|) / |p.coeff p.natDegree|) : ℚ) : K)
      ≤ (n : K) := by
    rw [← Rat.cast_natCast]
    exact Rat.cast_le.mpr hn
  exact le_trans (le_abs_self x) (le_trans hb hcast)

end Work.SSGRoute.InvAux
