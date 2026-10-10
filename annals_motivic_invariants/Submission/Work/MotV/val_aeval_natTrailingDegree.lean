import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

/-- Let `v` be a valuation of a ring `B` which is trivial on the constants `A` (so that every
`algebraMap A B c` has value `1`), and let `w : B` have value `< 1` (i.e. `w` lies in the
"maximal ideal").  Then evaluating a nonzero polynomial `p` at `w` scales the value by the order
of vanishing of `p` at `0`:

`v (p.aeval w) = (v w) ^ p.natTrailingDegree`.

This is the nonarchimedean triangle inequality in its sharp form: the lowest-degree term
`p.coeff t · w ^ t` (where `t = p.natTrailingDegree`) strictly dominates all the higher-degree
terms, which have value `(v w) ^ i < (v w) ^ t` for `i > t`, and all lower-degree terms vanish. -/
theorem val_aeval_natTrailingDegree {A B Γ₀ : Type*} [CommSemiring A] [Ring B] [Algebra A B]
    [LinearOrderedCommMonoidWithZero Γ₀] {v : Valuation B Γ₀} [v.IsTrivialOn A] {w : B}
    (hw : v w < 1) {p : Polynomial A} (hp : p ≠ 0) :
    v (p.aeval w) = (v w) ^ p.natTrailingDegree := by
  -- (1) A general bound: every value of `q.aeval w` is `≤ 1`, because it is a sum of terms
  -- `algebraMap (q.coeff i) * w ^ i` of value `(v w) ^ i ≤ 1`.
  have Hbound : ∀ q : Polynomial A, v (q.aeval w) ≤ 1 := by
    intro q
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
    refine Valuation.map_sum_le v ?_
    intro i hi
    by_cases hc : q.coeff i = 0
    · rw [hc]; simp
    · rw [map_mul, map_pow, Valuation.IsTrivialOn.eq_one (q.coeff i) hc, one_mul]
      exact pow_le_one₀ zero_le hw.le
  -- (2) The splitting of `q` into its constant term and the rest: `q = C (q.coeff 0) + X * q.divX`.
  have HdivX : ∀ q : Polynomial A,
      q.aeval w = w * q.divX.aeval w + algebraMap A B (q.coeff 0) := by
    intro q
    conv_lhs => rw [← Polynomial.X_mul_divX_add q]
    rw [Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_X, Polynomial.aeval_C]
  -- (3) If the constant term is a unit (nonzero), it dominates and the value is `1`.
  have Hone : ∀ q : Polynomial A, q.coeff 0 ≠ 0 → v (q.aeval w) = 1 := by
    intro q hq
    have hb : v (q.divX.aeval w) ≤ 1 := Hbound q.divX
    have h2 : v (w * q.divX.aeval w) < 1 := by
      rw [map_mul]
      calc v w * v (q.divX.aeval w) ≤ v w * 1 := mul_le_mul_of_nonneg_left hb zero_le
        _ = v w := mul_one _
        _ < 1 := hw
    have h1 : v (algebraMap A B (q.coeff 0)) = 1 := Valuation.IsTrivialOn.eq_one (q.coeff 0) hq
    have hlt : v (w * q.divX.aeval w) < v (algebraMap A B (q.coeff 0)) := by
      rw [h1]; exact h2
    rw [HdivX q, Valuation.map_add_eq_of_lt_right v hlt, h1]
  -- (4) Factoring out `X ^ t`, `t = p.natTrailingDegree`: `X ^ t ∣ p` since the coefficients
  -- below `t` all vanish.
  have hdvd : Polynomial.X ^ p.natTrailingDegree ∣ p := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    by_contra hne
    exact absurd (Polynomial.natTrailingDegree_le_of_ne_zero hne) (not_le.mpr hd)
  obtain ⟨q, hq⟩ := hdvd
  -- the quotient has nonzero constant term, because it is `p.coeff t`.
  have hcoeff : q.coeff 0 ≠ 0 := by
    have h1 : (Polynomial.X ^ p.natTrailingDegree * q).coeff (0 + p.natTrailingDegree)
        = q.coeff 0 :=
      Polynomial.coeff_X_pow_mul q p.natTrailingDegree 0
    rw [zero_add] at h1
    rw [← h1, ← hq]
    exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hp
  have hae : p.aeval w = w ^ p.natTrailingDegree * q.aeval w := by
    conv_lhs => rw [hq]
    rw [map_mul, Polynomial.aeval_X_pow]
  rw [hae, map_mul, map_pow, Hone q hcoeff, mul_one]

end Work.MotV
