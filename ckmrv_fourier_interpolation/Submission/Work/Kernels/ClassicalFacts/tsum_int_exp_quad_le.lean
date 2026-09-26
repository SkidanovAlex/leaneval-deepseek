import Mathlib

/-!
# A geometric bound for the `ℤ`-sum of `exp (-y * (n^2 + n))`

For `y > 0` we bound
`∑' n : ℤ, exp (-(y * (n^2 + n)))` by `2 / (1 - exp (-y))`.

The key observations are

* `n^2 + n = n * (n + 1) ≥ 0` for every integer `n`, and `g n = exp (-(y * (n^2 + n)))`
  is invariant under the fixed-point free involution `n ↦ -n - 1`;
* hence the sum over `ℤ`, split via `ℤ ≃ ℕ ⊕ ℕ`, is twice the sum over `ℕ`, namely
  `2 * ∑' n : ℕ, exp (-(y * (n^2 + n)))` (the two fibres `n ↦ n` and `n ↦ -(n+1)`
  are both equal to the same `ℕ`-indexed function);
* `n^2 + n ≥ n` for `n : ℕ`, so each term is at most `(exp (-y))^n`, and the geometric
  series sums to `(1 - exp (-y))⁻¹`.
-/

namespace Work.Kernels.ClassicalFacts

/-- Termwise comparison of `exp (-(y * (n^2 + n)))` with the geometric term `(exp (-y))^n`
for natural `n`. -/
private lemma exp_quad_le_geom (y : ℝ) (hy : 0 < y) (n : ℕ) :
    Real.exp (-(y * ((n : ℝ) ^ 2 + (n : ℝ)))) ≤ (Real.exp (-y)) ^ n := by
  rw [← Real.exp_nat_mul, Real.exp_le_exp]
  have h : (0 : ℝ) ≤ y * (n : ℝ) ^ 2 := mul_nonneg hy.le (sq_nonneg _)
  nlinarith [h]

/-- The `ℕ`-indexed summand `exp (-(y * (n^2 + n)))` is summable for `y > 0`. -/
private lemma summable_quad_exp (y : ℝ) (hy : 0 < y) :
    Summable (fun n : ℕ => Real.exp (-(y * ((n : ℝ) ^ 2 + (n : ℝ))))) := by
  have hgeom : Summable (fun n : ℕ => (Real.exp (-y)) ^ n) := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  exact Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le)
    (fun n => exp_quad_le_geom y hy n) hgeom

/-- Splitting the `ℤ`-sum along the fixed-point free involution `n ↦ -n - 1`: the sum equals
twice the corresponding `ℕ`-sum. -/
private lemma tsum_int_eq_two_mul (y : ℝ) (hy : 0 < y) :
    (∑' n : ℤ, Real.exp (-(y * ((n : ℝ) ^ 2 + (n : ℝ)))))
      = 2 * ∑' n : ℕ, Real.exp (-(y * ((n : ℝ) ^ 2 + (n : ℝ)))) := by
  let g : ℤ → ℝ := fun n => Real.exp (-(y * ((n : ℝ) ^ 2 + (n : ℝ))))
  let s : ℕ → ℝ := fun n => Real.exp (-(y * ((n : ℝ) ^ 2 + (n : ℝ))))
  let e : ℤ ≃ ℕ ⊕ ℕ := Equiv.intEquivNatSumNat
  let F : ℕ ⊕ ℕ → ℝ := fun x => g (e.symm x)
  have hsum_s : Summable s := summable_quad_exp y hy
  have hF1 : ∀ n : ℕ, F (Sum.inl n) = s n := by
    intro n; simp [F, g, s, e, Equiv.intEquivNatSumNat]
  have hF2 : ∀ n : ℕ, F (Sum.inr n) = s n := by
    intro n
    simp only [F, g, s, e]
    rw [show Equiv.intEquivNatSumNat.symm (Sum.inr n) = Int.negSucc n by
      simp [Equiv.intEquivNatSumNat]]
    congr 1
    rw [Int.cast_negSucc]; push_cast; ring
  have hs1 : Summable (F ∘ Sum.inl) := hsum_s.congr (fun n => (hF1 n).symm)
  have hs2 : Summable (F ∘ Sum.inr) := hsum_s.congr (fun n => (hF2 n).symm)
  have hL : (∑' x : ℕ ⊕ ℕ, F x) = ∑' m : ℤ, g m := Equiv.tsum_eq e.symm g
  have hmain : (∑' m : ℤ, g m) = 2 * ∑' n : ℕ, s n := by
    rw [← hL, Summable.tsum_sum hs1 hs2]
    rw [tsum_congr hF1, tsum_congr hF2]
    ring
  exact hmain

lemma tsum_int_exp_quad_le (y : ℝ) (hy : 0 < y) :
    ∑' n : ℤ, Real.exp (-(y * ((n : ℝ) ^ 2 + (n : ℝ)))) ≤ 2 / (1 - Real.exp (-y)) := by
  have hgeom : Summable (fun n : ℕ => (Real.exp (-y)) ^ n) := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hsum_s : Summable (fun n : ℕ => Real.exp (-(y * ((n : ℝ) ^ 2 + (n : ℝ))))) :=
    summable_quad_exp y hy
  rw [tsum_int_eq_two_mul y hy]
  have hbound : (∑' n : ℕ, Real.exp (-(y * ((n : ℝ) ^ 2 + (n : ℝ)))))
      ≤ (1 - Real.exp (-y))⁻¹ := by
    have h := Summable.tsum_le_tsum (fun n => exp_quad_le_geom y hy n) hsum_s hgeom
    rwa [tsum_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_lt_one_iff.mpr (by linarith))] at h
  calc 2 * (∑' n : ℕ, Real.exp (-(y * ((n : ℝ) ^ 2 + (n : ℝ)))))
        ≤ 2 * (1 - Real.exp (-y))⁻¹ := by linarith
    _ = 2 / (1 - Real.exp (-y)) := by ring

end Work.Kernels.ClassicalFacts
