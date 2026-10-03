import Mathlib
import Submission.Work.A3.Circle

/-!
# Dirichlet approximation outside the major arcs (Area A3)

For every `θ` outside the major arcs `majorArcSet Q N η` of the circle method there is a *reduced*
rational approximation `a/q` with

* `N^η < q ≤ N^{deg Q / 2}` and
* `|θ - a/q| ≤ 1/q²`,

i.e. the Dirichlet approximation theorem at level `N^{deg Q/2}`, combined with the observation
that the approximation cannot land inside the major arcs.  This is the input which feeds Weyl's
inequality on the minor arcs (`Work.A3.norm_expSum_le_of_not_mem_majorArcSet`).

The proof is the standard one: `Real.exists_rat_abs_sub_le_and_den_le` (Dirichlet's approximation
theorem, with the sharp denominator `n + 1` in the numerator) applied with `n = ⌊N^{deg Q/2}⌋`
produces `q` with `q.den ≤ n ≤ N^{deg Q/2}` and `|θ - q| ≤ 1/((n+1) q.den) ≤ 1/(q.den N^{deg Q/2})`.
Since `q.den ≤ N^{deg Q/2}` the last bound is `≤ 1/q.den²`; and if `q.den ≤ N^η` this very
inequality exhibits `θ` as an element of `majorArcSet Q N η`, contradicting the hypothesis.  So
`N^η < q.den`, as required.
-/

set_option autoImplicit false

namespace Work.A3

open Polynomial

/-- **Dirichlet approximation off the major arcs.**  If `θ` is not in the major arcs
`majorArcSet Q N η` (the union of the arcs of radius `1/(q N^{d/2})`, `d = deg Q`, around the
reduced fractions of denominator `q ≤ N^η`), then `θ` has a reduced rational approximation
`a/q` with `q.den > N^η`, `q.den ≤ N^{d/2}` and error `≤ 1/q.den²`. -/
theorem dirichlet_approx_of_not_mem_majorArcSet (Q : Polynomial ℤ) {N : ℕ} (hN : 1 ≤ N) {η : ℝ} {θ : ℝ}
    (hθ : θ ∉ Work.A3.majorArcSet Q N η) :
    ∃ q : ℚ, 1 ≤ q.den ∧
      (q.den : ℝ) ≤ (N : ℝ) ^ ((Polynomial.natDegree Q : ℝ) / 2) ∧
      (N : ℝ) ^ η < (q.den : ℝ) ∧
      |θ - (q.num : ℝ) / (q.den : ℝ)| ≤ 1 / ((q.den : ℝ) ^ 2) ∧
      IsCoprime q.num (q.den : ℤ) := by
  set X : ℝ := (N : ℝ) ^ ((Polynomial.natDegree Q : ℝ) / 2) with hXdef
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hX1 : 1 ≤ X := by
    rw [hXdef]; exact Real.one_le_rpow hN1 (by positivity)
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le zero_lt_one hX1
  -- Dirichlet's approximation theorem at the (real) level `X`, truncated to `n = ⌊X⌋`.
  set n : ℕ := ⌊X⌋₊ with hndef
  have hnle : (n : ℝ) ≤ X := by rw [hndef]; exact Nat.floor_le hXpos.le
  have hnlt : X ≤ (n : ℝ) + 1 := by
    rw [hndef]; exact le_of_lt (Nat.lt_floor_add_one X)
  have hnpos : 0 < n := by
    rw [hndef]; exact Nat.floor_pos.mpr hX1
  obtain ⟨q, hqapprox, hqden⟩ := Real.exists_rat_abs_sub_le_and_den_le θ hnpos
  have hden1 : 1 ≤ q.den := q.pos
  have hdenpos : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast hden1
  have hdenleX : (q.den : ℝ) ≤ X := le_trans (by exact_mod_cast hqden) hnle
  have hcop : IsCoprime q.num (q.den : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using q.reduced
  -- the sharpened error bound, with the exact Dirichlet radius `1/(q.den * X)`
  have happrox : |θ - (q.num : ℝ) / (q.den : ℝ)| ≤ 1 / ((q.den : ℝ) * X) := by
    have h1 : |θ - (q.num : ℝ) / (q.den : ℝ)| ≤ 1 / (((n : ℝ) + 1) * (q.den : ℝ)) := by
      simpa [Rat.cast_def] using hqapprox
    refine h1.trans ?_
    apply one_div_le_one_div_of_le (mul_pos hdenpos hXpos)
    nlinarith [hnlt, hdenpos]
  refine ⟨q, hden1, hdenleX, ?_, ?_, hcop⟩
  · -- `q.den ≤ N^η` would put `θ` in the major arcs
    by_contra hc
    refine hθ ⟨q.den, q.num, hden1, hcop, not_lt.mp hc, ?_⟩
    simpa [hXdef] using happrox
  · have hsq : (q.den : ℝ) ^ 2 ≤ (q.den : ℝ) * X := by
      rw [pow_two]; exact mul_le_mul_of_nonneg_left hdenleX hdenpos.le
    exact happrox.trans (one_div_le_one_div_of_le (by positivity) hsq)

end Work.A3
