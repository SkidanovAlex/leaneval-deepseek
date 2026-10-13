/-
  WilC4/ratio_sign_halfB : the doubling ratio of the fibre has constant sign on an interval which
  is free of `HalfB B₀`.

  ## The mathematics

  `HalfB B₀ = B₀ ∪ B₀/2`, where the halving acts on the *argument* coordinate.  So for a parameter
  `c`,

      `∀ x ∈ (a,b), Fin.cons x c ∉ HalfB B₀`

  says exactly: for every `x ∈ (a,b)`, *both* `x` and `2x` are `B₀`-free.  Consequently

  * `(a,b)` is `B₀`-free, and
  * `(2a,2b) = {2x : x ∈ (a,b)}` is `B₀`-free too (it is an interval: `t ∈ (2a,2b)` has
    `t = 2(t/2)` with `t/2 ∈ (a,b)`).

  By `GoodFibre`, on each `B₀`-free interval the fibre is a continuous non-vanishing function, so
  it has *constant sign* there (`free_sign`).  Hence, for `x, x' ∈ (a,b)` and values `y = f(x)`,
  `y' = f(2x)`, `y₁ = f(x')`, `y₁' = f(2x')`:

      `y * y₁ > 0`   (both from the interval `(a,b)`) and
      `y' * y₁' > 0` (both from the interval `(2a,2b)`).

  Since `w = y'/y` and `w' = y₁'/y₁` (with `y, y₁ ≠ 0`, which `RatW` provides), the two ratios
  have the same sign and their product is `(y'y₁')/(y y₁) > 0`.

  This is the "same sign" input for the ratio on a `HalfB`-free window; it is what lets one treat
  the doubling ratio of the inverted family `InvY Y` as a *positive* function there.
-/
import Mathlib
import Submission.Work.WilC4.InvFamDefs
import Submission.Work.WilC4.rexp_deep_window_value_ratio_aux

set_option linter.unusedVariables false

namespace Work.WilC4

/-- **The doubling ratio has constant sign on a `HalfB B₀`-free interval.**  If `(a,b)` is free of
`HalfB B₀` and the fibre is good (`GoodFibre Y B₀`), then the ratio `f_c(2x)/f_c(x)` at any two
points `x, x' ∈ (a,b)` has positive product: `x` and `x'` lie in the `B₀`-free interval `(a,b)`,
while `2x` and `2x'` lie in the `B₀`-free interval `(2a,2b)`, and on each such interval the fibre
is a non-vanishing continuous function, hence of constant sign. -/
theorem ratio_sign_halfB {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Work.WilC4.Route.Gr Y c x y →
      Work.WilC4.Route.Gr Y c x y' → y = y')
    (hgf : Work.WilC4.GoodFibre Y B₀) {c : Fin k → ℝ} {a b : ℝ} (hab : a < b)
    (hfree : ∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ Work.WilC4.HalfB B₀)
    {x x' w w' : ℝ} (hx : x ∈ Set.Ioo a b) (hx' : x' ∈ Set.Ioo a b)
    (hw : Work.WilC4.RatW Y c x w) (hw' : Work.WilC4.RatW Y c x' w') :
    0 < w * w' := by
  -- `HalfB`-freeness of `(a,b)` gives `B₀`-freeness of both `(a,b)` and `(2a,2b)`.
  have hfree1 : ∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B₀ := by
    intro x hx
    exact fun h => hfree x hx ((mem_halfB_iff B₀ x c).mpr (Or.inl h))
  have hfree2 : ∀ x ∈ Set.Ioo a b, Fin.cons (2 * x) c ∉ B₀ := by
    intro x hx
    exact fun h => hfree x hx ((mem_halfB_iff B₀ x c).mpr (Or.inr h))
  have hfree2ab : ∀ t ∈ Set.Ioo (2 * a) (2 * b), Fin.cons t c ∉ B₀ := by
    intro t ht
    have ht' : t / 2 ∈ Set.Ioo a b :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h := hfree2 (t / 2) ht'
    rwa [show 2 * (t / 2) = t by ring] at h
  -- the values of the two ratios
  obtain ⟨y, y', hy, hy', hy0, hwy⟩ := hw
  obtain ⟨y₁, y₁', hy₁, hy₁', hy₁0, hwy₁⟩ := hw'
  -- constant sign of the fibre on `(a,b)`: the values at `x` and at `x'`.
  have hxx : 0 < y * y₁ := free_sign hgf hab hfree1 hx hx' hy hy₁
  -- constant sign of the fibre on `(2a,2b)`: the values at `2x` and at `2x'`.
  have h2a : 2 * a < 2 * b := by linarith
  have h2x : 2 * x ∈ Set.Ioo (2 * a) (2 * b) :=
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h2x' : 2 * x' ∈ Set.Ioo (2 * a) (2 * b) :=
    ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  have h2xx : 0 < y' * y₁' := free_sign hgf h2a hfree2ab h2x h2x' hy' hy₁'
  -- `w = y'/y`, `w' = y₁'/y₁`, so the product is positive.
  have hw_eq : w = y' / y := (eq_div_iff hy0).mpr hwy
  have hw'_eq : w' = y₁' / y₁ := (eq_div_iff hy₁0).mpr hwy₁
  rw [hw_eq, hw'_eq, div_mul_div_comm]
  exact div_pos h2xx hxx

end Work.WilC4
