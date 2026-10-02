import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

/-- The derivative of the Taylor expansion of `P` at `a` is the Taylor expansion
of the derivative of `P` at `a`. -/
lemma derivative_taylor (a : ℂ) (P : Polynomial ℂ) :
    (Polynomial.taylor a P).derivative = Polynomial.taylor a P.derivative := by
  rw [Polynomial.taylor_apply, Polynomial.taylor_apply, Polynomial.derivative_comp,
    Polynomial.derivative_X_add_C, one_mul]

/-- The `2`-nd coefficient of the Taylor expansion of `P` at `a` is `P''(a)/2`. -/
lemma taylor_coeff_two (a : ℂ) (P : Polynomial ℂ) :
    (Polynomial.taylor a P).coeff 2
      = Polynomial.eval a (Polynomial.derivative (Polynomial.derivative P)) / 2 := by
  have hb : (Polynomial.taylor a P).derivative.derivative.eval 0
      = 2 * (Polynomial.taylor a P).coeff 2 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative,
      Polynomial.coeff_derivative]
    ring
  have ha : (Polynomial.taylor a P).derivative.derivative.eval 0
      = Polynomial.eval a (Polynomial.derivative (Polynomial.derivative P)) := by
    rw [derivative_taylor, derivative_taylor, Polynomial.taylor_eval, zero_add]
  have key : 2 * (Polynomial.taylor a P).coeff 2
      = Polynomial.eval a (Polynomial.derivative (Polynomial.derivative P)) := hb.symm.trans ha
  rw [eq_div_iff (by norm_num : (2 : ℂ) ≠ 0), mul_comm]
  exact key

/-- **Second-order Taylor expansion of a complex polynomial, uniform on a disc.**

For every polynomial `P` over `ℂ`, every centre `a : ℂ` and every radius `d >= 0` there is a
constant `C >= 0` such that for all `v : ℂ` with `‖v‖ ≤ d`,
`‖P(a + v) - P(a) - P'(a) * v - (P''(a) / 2) * v ^ 2‖ ≤ C * ‖v‖ ^ 3`.

Suggested route.  First obtain the cubic-remainder form: there is a polynomial `W` over `ℂ`
with `P(a + v) - P(a) - P'(a) * v - (P''(a) / 2) * v ^ 2 = v ^ 3 * W(v)` for all `v` (via
`Polynomial.taylor a P = P.comp (X + C a)` and `Polynomial.eval_eq_sum_range` together with
`Finset.sum_range_add`; the coefficient identifications are `T.eval 0 = T.coeff 0`,
`T.derivative.eval 0 = T.coeff 1`, `T.derivative.derivative.eval 0 = 2 * T.coeff 2` for
`T := Polynomial.taylor a P`, via `Polynomial.coeff_derivative`).  Then let `C` be any bound for
`‖W.eval t‖` over `Metric.closedBall 0 d`: that disc is compact in `ℂ` (`isCompact_closedBall`)
and `fun t => W.eval t` is continuous (`Polynomial.continuous`), so
`IsCompact.exists_bound_of_continuousOn` supplies such a `C`; deduce
`‖v ^ 3 * W(v)‖ = ‖v‖ ^ 3 * ‖W(v)‖ ≤ C * ‖v‖ ^ 3`. -/
theorem poly_taylor_two_bound (P : Polynomial ℂ) (a : ℂ) (d : ℝ) (hd : 0 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℂ, ‖v‖ ≤ d →
      ‖Polynomial.eval (a + v) P - Polynomial.eval a P
        - Polynomial.eval a (Polynomial.derivative P) * v
        - (Polynomial.eval a (Polynomial.derivative (Polynomial.derivative P)) / 2) * v ^ 2‖
        ≤ C * ‖v‖ ^ 3 := by
  -- Write the remainder as `v ^ 3 * W v` for an explicit polynomial `W`.
  set T : Polynomial ℂ := Polynomial.taylor a P with hT
  set Q : Polynomial ℂ := T - Polynomial.C (T.coeff 0) - Polynomial.C (T.coeff 1) * Polynomial.X
      - Polynomial.C (T.coeff 2) * Polynomial.X ^ 2 with hQ
  have hcoeff : ∀ k < 3, Q.coeff k = 0 := by
    intro k hk
    rw [hQ]
    interval_cases k <;> simp [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  obtain ⟨W, hW⟩ := Polynomial.X_pow_dvd_iff.mpr hcoeff
  have hident : ∀ v : ℂ, Polynomial.eval (a + v) P - Polynomial.eval a P
        - Polynomial.eval a (Polynomial.derivative P) * v
        - (Polynomial.eval a (Polynomial.derivative (Polynomial.derivative P)) / 2) * v ^ 2
      = v ^ 3 * Polynomial.eval v W := by
    intro v
    have h1 : Polynomial.eval v Q = v ^ 3 * Polynomial.eval v W := by
      rw [hW]
      simp [Polynomial.eval_mul, Polynomial.eval_pow]
    have h2 : Polynomial.eval v Q = Polynomial.eval (a + v) P - Polynomial.eval a P
        - Polynomial.eval a (Polynomial.derivative P) * v
        - (Polynomial.eval a (Polynomial.derivative (Polynomial.derivative P)) / 2) * v ^ 2 := by
      rw [hQ]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_pow, hT]
      rw [Polynomial.taylor_eval, Polynomial.taylor_coeff_zero, Polynomial.taylor_coeff_one,
        taylor_coeff_two, add_comm v a]
    exact h2 ▸ h1
  -- Bound `W` on the compact disc `closedBall 0 d`.
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) d).exists_bound_of_continuousOn
    (W.continuous.continuousOn)
  refine ⟨C, ?_, ?_⟩
  · have h0 : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) d := by
      rw [Metric.mem_closedBall, dist_self]; exact hd
    exact le_trans (norm_nonneg _) (hC 0 h0)
  · intro v hv
    have hmem : v ∈ Metric.closedBall (0 : ℂ) d := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hv
    have hWv : ‖Polynomial.eval v W‖ ≤ C := hC v hmem
    rw [hident v, norm_mul, norm_pow]
    calc ‖v‖ ^ 3 * ‖Polynomial.eval v W‖ ≤ ‖v‖ ^ 3 * C :=
          mul_le_mul_of_nonneg_left hWv (by positivity)
      _ = C * ‖v‖ ^ 3 := by ring

end Work.FBif
