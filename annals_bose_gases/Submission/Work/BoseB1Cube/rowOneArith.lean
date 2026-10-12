import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

/-- **The row-1 arithmetic at the diluteness gate `12 ≤ X`.**

Pure real arithmetic for the flat-arm ledger of `Work.BoseB1Cube.flatArm37RowOneGood`.  With
`X = μ|B(u)|` (the box's chemical-potential volume), `n = n'` the particle number on the window
`4X ≤ n < 5X`, `s = S/J` the *normalised* flat count (`S` the flat count, `J = ∫Φ²`, so that
`n − c₀ ≤ s ≤ n` whenever the excited count is `< c₀·J`), `c₀` the free small threshold of the
target and `ρ` the (arbitrarily small) loss factor of the Young step:

* the bracket `(10/37)(s−1) − Xρ` of the pair row is **nonnegative**, and
* it pays the row-1 demand `X·n/18`.

The extremal configuration is `(X, n, s, c₀, ρ) = (12, 48, 47.999999, 10⁻⁶, 1.0001)`, where the
second inequality reads `32 ≤ 33.67`; both conjuncts are monotone increasing in `s`, so
`s = n − c₀` is the only case that has to be checked, and
`f(n) = (n−c₀)((10/37)(n−c₀−1) − Xρ) − Xn/18` is a convex quadratic in `n` whose vertex
`(37/20)X(ρ+1/18) + ½ + c₀ ≈ 1.96X` lies below `4X`, so `n = 4X` is the extreme case; `f(4X)` is
in turn a convex quadratic in `X` with vertex `≈ 5.3`, so `X = 12` is extreme. -/
theorem rowOneArith {X n s c₀ ρ : ℝ}
    (hX : 12 ≤ X) (hn4 : 4 * X ≤ n) (hs : n - c₀ ≤ s)
    (hc₀0 : 0 < c₀) (hc₀ : c₀ ≤ 1 / 10 ^ 6) (hρ1 : 1 ≤ ρ) (hρ : ρ ≤ 1.0001) :
    0 ≤ (10 / 37) * (s - 1) - X * ρ ∧ X * n / 18 ≤ s * ((10 / 37) * (s - 1) - X * ρ) := by
  constructor
  · -- The bracket is nonnegative: `s ≥ 4X − c₀` and `ρ ≤ 1.0001`.
    nlinarith
  · -- The bracket pays the demand.  Write `u = n − c₀ ≥ u₀ = 4X − c₀` and
    -- `P(v) = (10/37)v² − A·v − X·c₀/18` with `A = 10/37 + Xρ + X/18`.  Since `s ≥ u` and
    -- `B₀ := (10/37)(u−1) − Xρ ≥ 0`, it suffices that `P(u) ≥ 0`; `P` is increasing for
    -- `v ≥ u₀` (the bracket `(10/37)(u+u₀) − A` is nonnegative), so it suffices that
    -- `P(u₀) ≥ 0`, which is the convex quadratic in `X` evaluated at its lower end `X = 12`.
    have hA : (0:ℝ) ≤ 10/37*((n-c₀) + (4*X-c₀)) - (10/37 + X*ρ + X/18) := by nlinarith
    have hP : (0:ℝ) ≤ (10/37)*(4*X-c₀)^2 - (10/37 + X*ρ + X/18)*(4*X-c₀) - X*c₀/18 := by
      have hX2 : (0:ℝ) ≤ X^2 := sq_nonneg X
      have h1 : (1/10:ℝ) ≤ 160/37 - 4*ρ - 2/9 := by linarith
      have hb1 : (1/10:ℝ)*X^2 ≤ X^2*(160/37 - 4*ρ - 2/9) := by
        calc (1/10:ℝ)*X^2 = X^2*(1/10) := by ring
          _ ≤ X^2*(160/37 - 4*ρ - 2/9) := mul_le_mul_of_nonneg_left h1 hX2
      have hX0 : (0:ℝ) ≤ X := by linarith
      have hXc : (0:ℝ) ≤ X*c₀ := by positivity
      have h2 : X*c₀*(1 - 80/37) ≤ X*c₀*(ρ - 80/37) := by
        apply mul_le_mul_of_nonneg_left _ hXc; linarith
      have h3 : (-(43/37)*X*(1/10^6) : ℝ) ≤ X*c₀*(1 - 80/37) := by nlinarith
      have h4 : (0:ℝ) ≤ (10/37)*c₀ + (10/37)*c₀^2 := by positivity
      have h5 : (0:ℝ) ≤ (1/10)*X - 40/37 - (43/37)*(1/10^6) := by linarith
      have h6 : (0:ℝ) ≤ X*((1/10)*X - 40/37 - (43/37)*(1/10^6)) := mul_nonneg hX0 h5
      have hexp : (10/37)*(4*X-c₀)^2 - (10/37 + X*ρ + X/18)*(4*X-c₀) - X*c₀/18
          = X^2*(160/37 - 4*ρ - 2/9) + X*c₀*(ρ - 80/37) - (40/37)*X + (10/37)*c₀
              + (10/37)*c₀^2 := by
        ring
      rw [hexp]
      linarith
    nlinarith [hA, hP]

end Work.BoseB1Cube
