import Mathlib
import Submission.Work.Diff.STE.fill.matInv_entry_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

/-- **Explicit entrywise bound on the inverse.**

If the quadratic form of a square matrix `A` dominates `lam · ∑ ξᵢ²` (with `lam > 0`), then each
entry of `A⁻¹` is bounded by `1 / lam` in absolute value; the bound is attained by `A = lam • 1`.

The proof does not use symmetry of `A`: only the *symmetric part* of `A` is seen by the quadratic
form, and the bound is nevertheless valid for the entries of the (possibly non-symmetric) inverse
`A⁻¹`.  Indeed, if `A x = e_b` then `lam · ∑ xᵢ² ≤ ∑ᵢ xᵢ (A x)ᵢ = x_b`, while `x_b² ≤ ∑ xᵢ²`; so
`lam · (∑ xᵢ²) ≤ √(∑ xᵢ²)`, whence `√(∑ xᵢ²) ≤ 1/lam` and finally `|A⁻¹ a b| = |x_a| ≤ 1/lam`. -/
theorem matInv_entry_bound_explicit {n : ℕ} (hn : 1 ≤ n) {lam : ℝ} (hlam : 0 < lam) :
    ∀ A : Matrix (Fin n) (Fin n) ℝ,
      (∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, A i j * ξ i * ξ j) →
      ∀ a b : Fin n, |A⁻¹ a b| ≤ 1 / lam := by
  have _ : 1 ≤ n := hn
  intro A hA a b
  -- `A` is injective, hence invertible: if `A x = 0` the quadratic form bound forces `x = 0`.
  have hker : ∀ x : Fin n → ℝ, Matrix.mulVec A x = 0 → x = 0 := by
    intro x hx
    have hq : ∑ i, ∑ j, A i j * x i * x j = 0 := by
      have h1 : ∑ i, Matrix.mulVec A x i * x i = 0 := by rw [hx]; simp
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mulVec_apply_eq_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    have h := hA x
    rw [hq] at h
    have hS : ∑ i, (x i) ^ 2 = 0 := by
      have hnn : 0 ≤ ∑ i, (x i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      nlinarith
    funext i
    have hi : (x i) ^ 2 ≤ ∑ k, (x k) ^ 2 := by
      have h2 := Finset.single_le_sum (f := fun k => (x k) ^ 2) (fun k _ => sq_nonneg _)
        (Finset.mem_univ i)
      simpa using h2
    rw [hS] at hi
    exact sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg _))
  have hinj : Function.Injective (Matrix.mulVec A) := by
    intro x y hxy
    have h : x - y = 0 := hker (x - y) (by rw [Matrix.mulVec_sub, hxy, sub_self])
    exact sub_eq_zero.mp h
  have hunit : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hunit
  have hmul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdet
  -- the `b`-th column of `A⁻¹` solves `A x = e_b`
  set x : Fin n → ℝ := fun i => A⁻¹ i b with hxdef
  have hcol : Matrix.mulVec A x = ((Pi.single b (1 : ℝ)) : Fin n → ℝ) := by
    funext i
    rw [hxdef, Matrix.mulVec_apply_eq_sum,
      show (∑ j, A i j * A⁻¹ j b) = (A * A⁻¹) i b from by rw [Matrix.mul_apply],
      hmul, Matrix.one_apply, Pi.single_apply]
  have hquad := hA x
  have hinner : ∑ i, ∑ j, A i j * x i * x j = x b := by
    have h1 : ∑ i, ∑ j, A i j * x i * x j = ∑ i, Matrix.mulVec A x i * x i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mulVec_apply_eq_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h1, hcol]
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
  rw [hinner] at hquad
  -- it remains to use `lam * S ≤ x b`, where `S = ∑ i, x i ^ 2`
  set S : ℝ := ∑ i, (x i) ^ 2 with hSdef
  have hSnn : 0 ≤ S := by rw [hSdef]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hxb_nn : 0 ≤ x b := le_trans (mul_nonneg hlam.le hSnn) hquad
  have hb_sq : (x b) ^ 2 ≤ S := by
    rw [hSdef]
    have h2 := Finset.single_le_sum (f := fun k => (x k) ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_univ b)
    simpa using h2
  have ha_sq : (x a) ^ 2 ≤ S := by
    rw [hSdef]
    have h2 := Finset.single_le_sum (f := fun k => (x k) ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_univ a)
    simpa using h2
  -- `(lam * S) ^ 2 ≤ (x b) ^ 2 ≤ S`
  have hSq : lam ^ 2 * S ^ 2 ≤ S := by
    have h1 : (lam * S) ^ 2 ≤ (x b) ^ 2 := pow_le_pow_left₀ (mul_nonneg hlam.le hSnn) hquad 2
    calc lam ^ 2 * S ^ 2 = (lam * S) ^ 2 := by ring
      _ ≤ (x b) ^ 2 := h1
      _ ≤ S := hb_sq
  have hSle : S ≤ (1 / lam) ^ 2 := by
    rcases lt_or_eq_of_le hSnn with hSpos | hS0
    · have h2 : S * (lam ^ 2 * S) ≤ S * 1 := by nlinarith [hSq]
      have h3 : lam ^ 2 * S ≤ 1 := le_of_mul_le_mul_left h2 hSpos
      rw [div_pow, one_pow, le_div_iff₀ (by positivity : (0 : ℝ) < lam ^ 2)]
      linarith
    · rw [← hS0]
      exact sq_nonneg _
  have hfinal : (x a) ^ 2 ≤ (1 / lam) ^ 2 := le_trans ha_sq hSle
  have hlast := Real.sqrt_le_sqrt hfinal
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs] at hlast
  rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / lam)] at hlast
  simpa [hxdef] using hlast

end Work.Diff.STE.Lead
