import Mathlib
import Submission.Work.MotV.TpAux

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Route V, node TP: the final step of the twisted-point valuation lemma

`Work.MotV.tp_final` is the last step of the proof of `Work.MotV.tp`
(`Submission/Work/MotV/tp.lean`): once the strict-ultrametric argument has produced a *pair of
consecutive* indices `i`, `i + 1` (cyclically in `Fin 5`) with equal nonzero weights
`wt v h y i = wt v h y (i+1)`, the value `v h` is a fifth power of a value of `v`.

This is pure valuation theory, with no hypothesis at all on the characteristic or on the
residue field, and `Γ₀` an arbitrary linearly ordered commutative group with zero.

## The mathematics

Write `a = v h`, `W i = v (y i)`, so that `wt v h y i = a ^ i * (W i) ^ 5`.

* If `i ≠ 4` then `(i + 1 : Fin 5)` has value `i + 1`, and cancelling the nonzero factor `a ^ i`
  in `a ^ i (W i)^5 = a ^ (i+1) (W (i+1))^5` gives `(W i)^5 = a * (W (i+1))^5`.  Since `W i ≠ 0`
  (as `wt v h y i ≠ 0` and `a ≠ 0`) this says `a = (W i / W (i+1))^5`, and `W i / W (i+1)` is the
  value of the *field element* `y i / y (i+1)`:

  `v h = (v (y i / y (i+1)))^5`.

* If `i = 4` then `(i + 1 : Fin 5) = 0`, and the same identity reads `a ^ 4 * (W 4)^5 = (W 0)^5`.
  Multiplying it by `a` and dividing by `(W 0)^5` gives `a = (a * W 4 / W 0)^5`, and again
  `a * W 4 / W 0` is the value of the field element `h * y 4 / y 0`:

  `v h = (v (h * y 4 / y 0))^5`.

Both divisions are legitimate: `a ≠ 0` because `h ≠ 0`, and `W i ≠ 0` because `wt v h y i ≠ 0`
at a nonzero `a`; the remaining denominators are covered by the two group-theoretic helper
lemmas below, which derive their non-vanishing from the displayed identities.
-/

open scoped WithZero

namespace Work.MotV

/-- In a commutative group with zero: `b ^ 5 = a * c ^ 5` with `b ≠ 0` forces `a = (b / c) ^ 5`
(the case `c = 0` is impossible, since it would give `b ^ 5 = 0`). -/
private lemma pow5_div_eq {G : Type*} [CommGroupWithZero G] {a b c : G}
    (hb : b ≠ 0) (h : b ^ 5 = a * c ^ 5) : (b / c) ^ 5 = a := by
  rcases eq_or_ne c 0 with rfl | hc
  · exact absurd (by simpa using h) (pow_ne_zero 5 hb)
  · rw [div_pow, h, mul_div_cancel_right₀ a (pow_ne_zero 5 hc)]

/-- In a commutative group with zero: `a ^ 4 * b ^ 5 = c ^ 5` with `a ≠ 0`, `b ≠ 0` forces
`a = (a * b / c) ^ 5`. -/
private lemma pow5_div_eq_four {G : Type*} [CommGroupWithZero G] {a b c : G}
    (ha : a ≠ 0) (hb : b ≠ 0) (h : a ^ 4 * b ^ 5 = c ^ 5) : (a * b / c) ^ 5 = a := by
  rcases eq_or_ne c 0 with rfl | hc
  · exact absurd (by simpa using h)
      (mul_ne_zero (pow_ne_zero 4 ha) (pow_ne_zero 5 hb))
  · rw [div_pow, mul_pow, ← h, mul_div_mul_right (a ^ 5) (a ^ 4) (pow_ne_zero 5 hb)]
    have h5 : a ^ 5 = a * a ^ 4 := by
      rw [show (5 : ℕ) = 1 + 4 from rfl, pow_add, pow_one]
    rw [h5, mul_div_cancel_right₀ a (pow_ne_zero 4 ha)]

theorem tp_final {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation F Γ₀) {h : F} (hh : h ≠ 0) {y : Fin 5 → F} {i : Fin 5}
    (hi : wt v h y i = wt v h y (i + 1)) (hne : wt v h y i ≠ 0) : ∃ u : F, v h = v u ^ 5 := by
  have hv : v h ≠ 0 := by rwa [Valuation.ne_zero_iff]
  have hWi : v (y i) ≠ 0 := by
    intro hc
    exact hne (by simp [wt, hc])
  rcases eq_or_ne i 4 with rfl | hne4
  · -- the wrapping case: `h * y 4 / y 0` is the fifth root
    refine ⟨h * y 4 / y 0, ?_⟩
    have h4 : (v h) ^ 4 * (v (y 4)) ^ 5 = (v (y 0)) ^ 5 := by
      simpa [wt] using hi
    have hgoal : (v h * v (y 4) / v (y 0)) ^ 5 = v h := pow5_div_eq_four hv hWi h4
    rw [Valuation.map_div, Valuation.map_mul]
    exact hgoal.symm
  · -- the non-wrapping case: `y i / y (i + 1)` is the fifth root
    have hlt : (i : ℕ) < 4 := by
      have h1 : (i : ℕ) ≠ 4 := fun hc => hne4 (Fin.ext hc)
      have h2 := i.isLt
      omega
    refine ⟨y i / y (i + 1), ?_⟩
    have hidx : ((i + 1 : Fin 5) : ℕ) = (i : ℕ) + 1 := by
      refine Fin.val_add_one_of_lt (n := 4) ?_
      rw [Fin.lt_def]
      exact hlt
    have hstep : (v (y i)) ^ 5 = v h * (v (y (i + 1))) ^ 5 := by
      have h2 : (v h) ^ (i : ℕ) * (v (y i)) ^ 5
          = (v h) ^ ((i : ℕ) + 1) * (v (y (i + 1))) ^ 5 := by
        simpa [wt, hidx] using hi
      have h3 : (v h) ^ ((i : ℕ) + 1) = (v h) ^ (i : ℕ) * v h := pow_succ _ _
      rw [h3] at h2
      refine mul_left_cancel₀ (pow_ne_zero (i : ℕ) hv) ?_
      simpa only [mul_assoc] using h2
    rw [Valuation.map_div]
    exact (pow5_div_eq hWi hstep).symm

end Work.MotV
