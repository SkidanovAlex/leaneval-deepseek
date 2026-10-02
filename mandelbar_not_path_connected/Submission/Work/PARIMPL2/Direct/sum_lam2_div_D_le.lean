import Mathlib
import Submission.Work.PARIMPL2.Direct.sum_lam2_div_sin_sq_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-!
# Sum of `λ² / (sin²(λ x_j) + sinh²(λ y_j))` along a decreasing real-part sequence

This is the `sinh`-denominator version of `sum_lam2_div_sin_sq_le`: since
`sinh² ≥ 0`, each term is dominated by the corresponding term without the
hyperbolic factor, and the latter sum is already bounded by `24/R`.

## Main result

`sum_lam2_div_D_le`: if `λ R² ≤ 1`, `R ≥ 128` and the real parts `Re u_j` stay in
`[R/4+2, π/λ - R/4]` and decrease by at least `1/3` at each step, then
`∑_{j<n} λ²/(sin²(λ Re u_j) + sinh²(λ Im u_j)) ≤ 24/R`.
-/

/-- Termwise domination of the `sinh`-denominator term by the pure `sin²` term:
for `λ x ∈ (0, π)` one has `λ²/(sin²(λx) + sinh²(λy)) ≤ λ²/sin²(λx)`. -/
private lemma term_le_sin (lam R x y : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hx1 : R / 4 + 2 ≤ x) (hx2 : x ≤ Real.pi / lam - R / 4) :
    lam ^ 2 / (Real.sin (lam * x) ^ 2 + Real.sinh (lam * y) ^ 2)
      ≤ lam ^ 2 / (Real.sin (lam * x)) ^ 2 := by
  have hxpos : 0 < x := by linarith
  have ht0 : 0 < lam * x := mul_pos hlam hxpos
  have htpi : lam * x < Real.pi := by
    have h1 : lam * x ≤ lam * (Real.pi / lam - R / 4) :=
      mul_le_mul_of_nonneg_left hx2 hlam.le
    have h1' : lam * (Real.pi / lam - R / 4) = Real.pi - lam * (R / 4) := by field_simp
    rw [h1'] at h1
    have h2 : 0 < lam * (R / 4) := by positivity
    linarith
  have hsinpos : 0 < Real.sin (lam * x) := Real.sin_pos_of_pos_of_lt_pi ht0 htpi
  have hden : Real.sin (lam * x) ^ 2
      ≤ Real.sin (lam * x) ^ 2 + Real.sinh (lam * y) ^ 2 := by
    have := sq_nonneg (Real.sinh (lam * y)); linarith
  exact div_le_div_of_nonneg_left (by positivity) (pow_pos hsinpos 2) hden

theorem sum_lam2_div_D_le (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (n : ℕ) (u : ℕ → ℂ)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ (u j).re)
    (hx2 : ∀ j ≤ n, (u j).re ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, (u (j + 1)).re ≤ (u j).re - 1 / 3) :
    ∑ j ∈ Finset.range n,
        lam ^ 2 / (Real.sin (lam * (u j).re) ^ 2 + Real.sinh (lam * (u j).im) ^ 2) ≤ 24 / R := by
  refine le_trans ?_ (sum_lam2_div_sin_sq_le lam R u n hlam hR hlamR hx1 hx2 hdec)
  apply Finset.sum_le_sum
  intro j hj
  have hjlt : j < n := Finset.mem_range.mp hj
  exact term_le_sin lam R ((u j).re) ((u j).im) hlam hR
    (hx1 j (le_of_lt hjlt)) (hx2 j (le_of_lt hjlt))

end Work.PARIMPL2.Direct
