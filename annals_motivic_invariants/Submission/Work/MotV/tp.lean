import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotV.TpAux
import Submission.Work.MotV.tp_ident
import Submission.Work.MotV.tp_max
import Submission.Work.MotV.tp_cmp
import Submission.Work.MotV.tp_final

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

/-- Node TP: the twisted-point valuation lemma (the arithmetic engine of route V).  `y` is a
nonzero point of the T-twisted Klein curve `kleinTw a b h y = 0` over an arbitrary valued field
with `v a = v b = 1`; then `v h` is a fifth power.  Pure valuation theory: no smoothness, no
characteristic hypothesis, `Γ₀` an arbitrary linearly ordered commutative group with zero.

Route.  Put `M i := v h ^ i * (v (y i)) ^ 5` for `i : Fin 5` and let `I` be the set of `argmax M`.
Each twisted quadric `k` has three monomials — the square `y_{2k}^2`, the consecutive pair
`(2k+2, 2k+3)` and the distance-two pair `(2k+1, 2k+4)` — and for a monomial `(i,l)` of the `k`-th
equation the fifth power of the term's value is `M i * M l / (v h) ^ (4*k)`: this is the identity
`5 * [i + l ≥ 5] = i + l - (4*k)` for the three index pairs.  Use `Valuation.map_add_eq_of_lt_left`
and `pow_lt_pow_left` to compare fifth powers.  If `I` contains no two cyclically consecutive
indices, pick `j ∈ I` and `k` with `2k = j`: the square term is then strictly dominant (the other
two monomials involve an index outside `I`, and `j+2, j+3` cannot both lie in `I`), so by the
strict ultrametric inequality the sum is nonzero — contradiction with `heq k`.  Hence
`M i = M (i+1)` for some `i`.  For `i ≤ 3` this gives `v h = (v (y i) / v (y (i+1))) ^ 5`; for
`i = 4` it gives `(v h)^4 = (v (y 0) / v (y 4))^5`, so `v h = (v h * v (y 4) / v (y 0)) ^ 5`.
`hh` gives `v h ≠ 0` and `hy` gives `max M ≠ 0`, so the divisions are legitimate. -/
theorem tp {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
    {a b h : F} (ha : v a = 1) (hb : v b = 1) (hh : h ≠ 0) {y : Fin 5 → F} (hy : y ≠ 0)
    (heq : ∀ k, kleinTw a b h y k = 0) : ∃ u : F, v h = v u ^ 5 := by
  have hΛ : v h ≠ 0 := by rwa [Valuation.ne_zero_iff]
  obtain ⟨j, hjmax, hm⟩ := tp_max v hh hy
  -- `j` maximises the weight; if no two cyclically consecutive indices are maximal, the square
  -- monomial of the quadric with `2 * k = j` is strictly dominant, contradicting `heq k`
  have hkey : ∃ i : Fin 5, wt v h y i = wt v h y j ∧ wt v h y (i + 1) = wt v h y j := by
    by_contra hcon
    have hstep : ∀ i, wt v h y i = wt v h y j → wt v h y (i + 1) ≠ wt v h y j :=
      fun i hi hi' => hcon ⟨i, hi, hi'⟩
    obtain ⟨hc2, hc3⟩ := tp_cmp v hΛ y hm hjmax hstep
    -- the quadric of index `3 * j` is the one whose square monomial is `y_j ^ 2`
    have hk : (2 * (3 * j) : Fin 5) = j := two_mul_three_mul j
    have heqj : -a * b * twMon h y j j + a ^ 2 * twMon h y (j + 2) (j + 3)
        - b ^ 2 * twMon h y (j + 1) (j + 4) = 0 := by
      have h := heq (3 * j)
      unfold kleinTw at h
      rw [hk] at h
      exact h
    have hsum : (-a * b * twMon h y j j) + (a ^ 2 * twMon h y (j + 2) (j + 3))
        + (-(b ^ 2 * twMon h y (j + 1) (j + 4))) = 0 := by
      simpa [sub_eq_add_neg] using heqj
    -- the three coefficient valuations are `1`
    have hv1 : v (-a * b * twMon h y j j) = v (twMon h y j j) := by
      simp [map_mul, map_neg, map_pow, ha, hb]
    have hv2 : v (a ^ 2 * twMon h y (j + 2) (j + 3)) = v (twMon h y (j + 2) (j + 3)) := by
      simp [map_mul, map_pow, ha]
    have hv3 : v (-(b ^ 2 * twMon h y (j + 1) (j + 4))) = v (twMon h y (j + 1) (j + 4)) := by
      simp [map_mul, map_neg, map_pow, hb]
    exact sum_ne_zero_of_dominant v hsum (by rw [hv2, hv1]; exact hc2)
      (by rw [hv3, hv1]; exact hc3)
  obtain ⟨i, hi1, hi2⟩ := hkey
  exact tp_final v hh (by rw [hi1, hi2]) (by rw [hi1]; exact ne_of_gt hm)

end Work.MotV
