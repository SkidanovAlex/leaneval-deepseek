/-
# OffAxis/G72Defs — the normalized HB Lemma 7.2 weight

HB Lemma 7.2's test function with parameter `lam` is
`f(t) = (lam/30)(2 - lam t)^3 (4 + 6 lam t + lam^2 t^2)` on `[0, 2/lam]`, i.e.
`f(t) = lam * g(lam t)` with `g(y) = (1/30)(2-y)^3(4+6y+y^2)` on `[0,2]`.
Its Laplace transform therefore factors as `F(z) = G(z/lam)` with
`G(w) = ∫_0^2 e^{-wy} g(y) dy`.

The whole §10 numerical bookkeeping of Heath-Brown is `lam`-free once written in
terms of `G`: the identities `F 0 = 8/9`, `F(-lam) = 8/5`, `lam^{-1} f 0 = 16/15`
become `G 0 = 8/9`, `G (-1) = 8/5`, and the conditions (10.8), (10.12) become the
scale-free inequalities `G72Cancel` / `G72TenSeven` of the companion modules.
-/
import Mathlib

noncomputable section
namespace Work.ZeroFreeTables

/-- HB Lemma 7.2's weight `g(y) = (1/30)(2-y)^3(4+6y+y^2)` on `[0,2]`. -/
def g72 (y : ℝ) : ℝ := (1/30) * (2 - y)^3 * (4 + 6*y + y^2)

/-- The Laplace transform `G(w) = ∫_0^2 e^{-wy} g(y) dy` of `g72`.  The HB Lemma 7.2
test function of parameter `lam` has Laplace transform `z ↦ G (z / lam)`. -/
noncomputable def G72 (w : ℂ) : ℂ :=
  ∫ y in (0:ℝ)..2, Complex.exp (-(w * (y : ℂ))) * ((g72 y : ℝ) : ℂ)

end Work.ZeroFreeTables
