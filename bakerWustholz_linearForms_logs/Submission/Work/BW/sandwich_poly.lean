import Mathlib
import Submission.Work.BW.poly_natDegree_eventually_le
import Submission.Work.BW.leadingCoeff_le_of_eventually_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Evaluating the shift `p(X + c)` at `x` gives `p(x + c)`. -/
private lemma eval_comp_X_add_C (p : Polynomial ℚ) (c x : ℚ) :
    (p.comp (Polynomial.X + Polynomial.C c)).eval x = p.eval (x + c) := by
  rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

/-- The shift `X ↦ X + c` (with `c` a constant) does not change the `natDegree`. -/
private lemma natDegree_comp_X_add_C (p : Polynomial ℚ) (c : ℚ) :
    (p.comp (Polynomial.X + Polynomial.C c)).natDegree = p.natDegree := by
  rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]

/-- The shift `X ↦ X + c` (with `c` a constant) does not change the leading coefficient, because
`X + C c` is monic of degree `1`. -/
private lemma leadingCoeff_comp_X_add_C (p : Polynomial ℚ) (c : ℚ) :
    (p.comp (Polynomial.X + Polynomial.C c)).leadingCoeff = p.leadingCoeff := by
  rw [Polynomial.leadingCoeff_comp (by rw [Polynomial.natDegree_X_add_C]; norm_num),
      Polynomial.leadingCoeff_X_add_C, one_pow, mul_one]

/-- Squeeze bound for polynomials: if a nonnegative function of `t` is eventually the polynomial `p`,
and the polynomial `q` is squeezed between `p` and the `k`-shift of `p`, then `p` and `q` have the
same degree and the same leading coefficient. (Used with `p` and `q` the eventual polynomials of a
ray Hilbert function and of its shift.)

Suggested route: the sign of a nonzero polynomial at `+∞` is the sign of its leading coefficient
(`Polynomial.tendsto_atTop_iff_leadingCoeff_nonneg`, `Polynomial.tendsto_atBot_iff_leadingCoeff_nonpos`,
composed with `tendsto_natCast_atTop_atTop`), so a polynomial that is eventually `≥ 0` on `ℕ` has
nonnegative leading coefficient. Writing `r` for `q - p` and `s` for `p(·+k) - q`, both are
eventually nonnegative, so both have nonnegative leading coefficients. If `natDegree p < natDegree q`
then the coefficient of `X ^ natDegree q` in `r` is `q.leadingCoeff` and in `s` is `-q.leadingCoeff`,
whence `q.leadingCoeff = 0`, contradicting `q ≠ 0`; the case `natDegree q < natDegree p` is similar
(using `hp0`, i.e. `p ≥ 0` eventually, to rule out a negative leading coefficient for `p`). Hence the
degrees agree, and comparing the coefficients of `X ^ natDegree p` in `r` and `s` gives
`q.leadingCoeff = p.leadingCoeff`. -/
theorem sandwich_poly {p q : Polynomial ℚ} {k : ℕ}
    (hp0 : ∀ᶠ t : ℕ in Filter.atTop, 0 ≤ p.eval (t : ℚ))
    (h1 : ∀ᶠ t : ℕ in Filter.atTop, p.eval (t : ℚ) ≤ q.eval (t : ℚ))
    (h2 : ∀ᶠ t : ℕ in Filter.atTop, q.eval (t : ℚ) ≤ p.eval ((t + k : ℕ) : ℚ)) :
    p.natDegree = q.natDegree ∧ p.leadingCoeff = q.leadingCoeff := by
  -- `P` is the shifted polynomial `p(X + k)`.
  set P : Polynomial ℚ := p.comp (Polynomial.X + Polynomial.C (k : ℚ)) with hPdef
  have hPeval : ∀ t : ℕ, P.eval (t : ℚ) = p.eval ((t + k : ℕ) : ℚ) := by
    intro t
    rw [hPdef, eval_comp_X_add_C, Nat.cast_add]
  have hPdeg : P.natDegree = p.natDegree := by rw [hPdef, natDegree_comp_X_add_C]
  have hPlead : P.leadingCoeff = p.leadingCoeff := by rw [hPdef, leadingCoeff_comp_X_add_C]
  -- `q` is eventually nonnegative, being squeezed above `p ≥ 0`.
  have hq0 : ∀ᶠ t : ℕ in Filter.atTop, 0 ≤ q.eval (t : ℚ) := by
    filter_upwards [hp0, h1] with t ht0 ht1
    linarith
  -- `q` is eventually at most the shift `P`.
  have hqP : ∀ᶠ t : ℕ in Filter.atTop, q.eval (t : ℚ) ≤ P.eval (t : ℚ) := by
    filter_upwards [h2] with t ht
    rw [hPeval t]
    exact ht
  -- Degrees: `p ≤ q` and `q ≤ p(X+k)`, both bounded below by `0`, force equal `natDegree`.
  have hpq_deg : p.natDegree ≤ q.natDegree := poly_natDegree_eventually_le h1 hp0
  have hqp_deg : q.natDegree ≤ p.natDegree := by
    have h := poly_natDegree_eventually_le hqP hq0
    rwa [hPdeg] at h
  have hdeg_eq : p.natDegree = q.natDegree := le_antisymm hpq_deg hqp_deg
  -- Leading coefficients: comparing with `q` from below gives `p.lc ≤ q.lc`, and comparing `q`
  -- with the shift `P` (same leading coefficient as `p`) gives `q.lc ≤ p.lc`.
  have hlc1 : p.leadingCoeff ≤ q.leadingCoeff := leadingCoeff_le_of_eventually_le hdeg_eq h1
  have hlc2 : q.leadingCoeff ≤ p.leadingCoeff := by
    have h := leadingCoeff_le_of_eventually_le (p := q) (q := P) ?_ hqP
    · rwa [hPlead] at h
    · rw [hPdeg, hdeg_eq]
  exact ⟨hdeg_eq, le_antisymm hlc1 hlc2⟩

end Work.BW
