import Mathlib

namespace Work.WilE4.Poly

open MvPolynomial

/-- The `i`-degree of the partial derivative `∂P/∂Xᵢ` drops by at least one
(truncated subtraction).  The degenerate case `degreeOf i P = 0` is covered by
the truncation: then `P` is constant in `Xᵢ`, hence `pderiv i P = 0` and both
sides read `0`. -/
lemma pderiv_degreeOf_le_pred {m : ℕ} (P : MvPolynomial (Fin m) ℝ) (i : Fin m) :
    (MvPolynomial.pderiv i P).degreeOf i ≤ P.degreeOf i - 1 := by
  rw [MvPolynomial.degreeOf_le_iff]
  intro s hs
  rw [MvPolynomial.mem_support_iff] at hs
  rw [MvPolynomial.coeff_pderiv] at hs
  have hs2 : P.coeff (s + Finsupp.single i 1) ≠ 0 := by
    rintro h; rw [h] at hs; exact hs (zero_mul _)
  have hmem : s + Finsupp.single i 1 ∈ P.support := by
    rwa [MvPolynomial.mem_support_iff]
  have hle := MvPolynomial.le_degreeOf_of_mem_support (p := P) i hmem
  simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hle
  omega

/-- If the `i`-degree of `P` is at most `n`, then differentiating `n + 1` times
with respect to `Xᵢ` kills `P`. -/
lemma iterate_pderiv_succ_zero {m : ℕ} (i : Fin m) :
    ∀ (n : ℕ) (P : MvPolynomial (Fin m) ℝ),
      P.degreeOf i ≤ n → ((MvPolynomial.pderiv i)^[n + 1]) P = 0 := by
  intro n
  induction n with
  | zero =>
    intro P hP
    have hd : P.degreeOf i = 0 := Nat.le_zero.mp hP
    ext s
    change (MvPolynomial.pderiv i P).coeff s = 0
    rw [MvPolynomial.coeff_pderiv]
    have hnot : s + Finsupp.single i 1 ∉ P.support := by
      apply MvPolynomial.notMem_support_of_degreeOf_lt (p := P) i
      rw [hd]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      omega
    rw [MvPolynomial.notMem_support_iff] at hnot
    rw [hnot, zero_mul]
  | succ n ih =>
    intro P hP
    rw [show n + 1 + 1 = (n + 1).succ from rfl, Function.iterate_succ_apply]
    apply ih
    have h := pderiv_degreeOf_le_pred P i
    omega

theorem iterate_pderiv_zero {m : ℕ} (P : MvPolynomial (Fin m) ℝ) (i : Fin m)
    {k : ℕ} (hk : P.degreeOf i < k) : ((MvPolynomial.pderiv i)^[k]) P = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  subst hj
  exact iterate_pderiv_succ_zero i j P (by omega)

end Work.WilE4.Poly
