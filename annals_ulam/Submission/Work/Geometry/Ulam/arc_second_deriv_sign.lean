import Mathlib

namespace Commons.Geometry.Ulam

open MeasureTheory Filter
open scoped Interval Topology

set_option autoImplicit false

private lemma arc_ident_arith (R0 R1 R2 s c : ℝ) (hs : s ^ 2 + c ^ 2 = 1) :
    (R2 * s + 2 * R1 * c - R0 * s) * (R1 * c - R0 * s) -
      (R1 * s + R0 * c) * (R2 * c - 2 * R1 * s - R0 * c)
    = R0 ^ 2 + 2 * R1 ^ 2 - R0 * R2 := by
  have hs' : s ^ 2 = 1 - c ^ 2 := by linarith [hs]
  ring_nf
  rw [hs']
  ring

/-- **Arc identity.**  For the right arc `x = R * cos`, `y = R * sin` (pointwise products), the
combination governing the second derivative of the profile in `x` is
`y'' * x' - y' * x'' = R ^ 2 + 2 * (R') ^ 2 - R * R''`. -/
lemma rightArc_second_deriv_identity (R : ℝ → ℝ)
    (hR : Differentiable ℝ R) (hR' : Differentiable ℝ (deriv R)) (α : ℝ) :
    deriv (deriv (R * Real.sin)) α * deriv (R * Real.cos) α -
      deriv (R * Real.sin) α * deriv (deriv (R * Real.cos)) α
    = R α ^ 2 + 2 * deriv R α ^ 2 - R α * deriv (deriv R) α := by
  have hcos : ∀ β, deriv (R * Real.cos) β = deriv R β * Real.cos β - R β * Real.sin β := by
    intro β
    rw [deriv_mul (hR β) (Real.differentiableAt_cos), Real.deriv_cos]
    ring
  have hsin : ∀ β, deriv (R * Real.sin) β = deriv R β * Real.sin β + R β * Real.cos β := by
    intro β
    rw [deriv_mul (hR β) (Real.differentiableAt_sin), Real.deriv_sin]
  have h2cos : deriv (deriv (R * Real.cos)) α =
      deriv (deriv R) α * Real.cos α - 2 * deriv R α * Real.sin α - R α * Real.cos α := by
    have hfun : deriv (R * Real.cos) = deriv R * Real.cos - R * Real.sin := by
      funext β; exact hcos β
    rw [hfun, deriv_sub ((hR'.mul Real.differentiable_cos).differentiableAt)
        ((hR.mul Real.differentiable_sin).differentiableAt),
      deriv_mul (hR' α) Real.differentiableAt_cos, deriv_mul (hR α) Real.differentiableAt_sin,
      Real.deriv_cos, Real.deriv_sin]
    ring
  have h2sin : deriv (deriv (R * Real.sin)) α =
      deriv (deriv R) α * Real.sin α + 2 * deriv R α * Real.cos α - R α * Real.sin α := by
    have hfun : deriv (R * Real.sin) = deriv R * Real.sin + R * Real.cos := by
      funext β; exact hsin β
    rw [hfun, deriv_add ((hR'.mul Real.differentiable_sin).differentiableAt)
        ((hR.mul Real.differentiable_cos).differentiableAt),
      deriv_mul (hR' α) Real.differentiableAt_sin, deriv_mul (hR α) Real.differentiableAt_cos,
      Real.deriv_sin, Real.deriv_cos]
    ring
  rw [h2sin, h2cos, hcos α, hsin α]
  exact arc_ident_arith (R α) (deriv R α) (deriv (deriv R) α) (Real.sin α) (Real.cos α)
    (Real.sin_sq_add_cos_sq α)

/-- **Arc sign.**  Under the `C²`-closeness data (`1 - η ≤ R`, `|R''| < η`, `η < 1/8`) the
combination `y'' x' - y' x''` is *nonnegative*; since `x' = R' cos - R sin < 0` on `(0, π/2)`,
this is exactly `f'' ≤ 0`, i.e. concavity of the arc's graph. -/
lemma rightArc_second_deriv_nonneg (R : ℝ → ℝ)
    (hR : Differentiable ℝ R) (hR' : Differentiable ℝ (deriv R)) {η : ℝ} (hη0 : 0 < η)
    (hηsmall : η < 1 / 8) {α : ℝ} (hRpos : 0 < R α) (hRlow : 1 - η ≤ R α)
    (hR2 : |deriv (deriv R) α| < η) :
    0 ≤ deriv (deriv (R * Real.sin)) α * deriv (R * Real.cos) α -
        deriv (R * Real.sin) α * deriv (deriv (R * Real.cos)) α := by
  rw [rightArc_second_deriv_identity R hR hR' α]
  have hle : R α * deriv (deriv R) α ≤ R α * η :=
    mul_le_mul_of_nonneg_left (le_of_lt (abs_lt.mp hR2).2) (le_of_lt hRpos)
  have h1 : (0 : ℝ) < R α * (R α - η) := by nlinarith [hRlow, hηsmall, hRpos]
  nlinarith [hle, h1, sq_nonneg (deriv R α)]


/-
### Left arc: how it follows from the right one (and a trap worth recording)

The left arc has **height** `Y = r * sin` and **abscissa** `X = -(r * cos)`, i.e. it is the right
arc `x̃ = r * cos`, `ỹ = r * sin` reflected in the `y`-axis (`X = -x̃`, `Y = ỹ`).  Reflection
negates `X'` and `X''` and leaves `Y`, `Y'`, `Y''`, so

`Y'' X' - Y' X'' = -(ỹ'' x̃' - ỹ' x̃'') = -(r^2 + 2 (r')^2 - r r'')`

by `rightArc_second_deriv_identity` applied to `r`.  Since for the left arc `X' = r sin - r' cos > 0`
on `(0, π/2)`, concavity of the graph is `Y'' X' - Y' X'' ≤ 0`, i.e. again the *same* bound
`r^2 + 2 (r')^2 - r r'' ≥ 0` supplied by `1 - η ≤ r`, `|r''| < η`, `η < 1/8`.  So the left twin
needs no new mathematics — only the derivative plumbing `X' = -x̃'`, `X'' = -x̃''`, which is
`deriv_const_mul` (write `X = (-1) * (r * cos)`) applied twice; `deriv_neg` does *not* fire on the
goal shape `deriv (-(r * Real.cos)) = -deriv (r * Real.cos)` in this Mathlib version.

**The trap, twice in one sitting:** the combination is `Y'' X' - Y' X''` — the *height's* second
derivative times the *abscissa's* first derivative, minus the height's first times the abscissa's
second.  I first stated the right-arc request with `x''` in the first slot (making it identically
`0`), and then wrote the left-arc statement with the roles of `X` and `Y` interchanged.  Whoever
writes the twins should ask which branch carries the *height* before transcribing.
-/


/-
**Left twin: DONE.**  `leftArc_second_deriv_identity` and `leftArc_second_deriv_nonpos` below are
the left arc `X = -(r * cos)`, `Y = r * sin` — the right arc reflected in the `y`-axis.  The proof
follows the recommended route (repeat the right-arc computation on the negated branch, via
`deriv_mul ((hr β).neg) (Real.differentiableAt_cos)` and `hr'`), *not* `deriv_const_mul`: that lemma
is stated with the pattern `deriv (fun y => c * d y) x`, which the beta-expanded goals do not match.
The three Lean gotchas met on the way, all recorded so the twins of the twins cost nothing:
* convert function-level products to pointwise ones with `simp only [Pi.neg_apply, Pi.mul_apply]`
  (and `Pi.sub_apply` for differences) before `ring`;
* `deriv_neg` does not rewrite the goal shape `deriv (-(r * Real.cos)) = -deriv (r * Real.cos)`;
  use `HasDerivAt.neg` (`.deriv`) instead;
* to feed `(hA.sub hB).deriv`, the function whose derivative is being taken must first be put in the
  literal form `(fun β => ...) - fun β => ...`; a `funext` proof deriving it from the pointwise
  identity does the job.

With that, the **arc half of `profileGlue_concaveOn` is complete in Lean**: both arcs have their
`Y'' X' - Y' X''` identity and the correct sign (`≥ 0` on the right arc, `≤ 0` on the left, both
from the same bound `R (R - η) + 2 (R')² > 0`).
-/

lemma leftArc_second_deriv_identity (r : ℝ → ℝ)
    (hr : Differentiable ℝ r) (hr' : Differentiable ℝ (deriv r)) (α : ℝ) :
    deriv (deriv (r * Real.sin)) α * deriv (fun β => -(r β) * Real.cos β) α -
      deriv (r * Real.sin) α * deriv (deriv (fun β => -(r β) * Real.cos β)) α
    = -(r α ^ 2 + 2 * deriv r α ^ 2 - r α * deriv (deriv r) α) := by
  have hX1 : ∀ β, deriv (fun γ => -(r γ) * Real.cos γ) β =
      -(deriv r β * Real.cos β) + r β * Real.sin β := by
    intro β
    have hfun : (-r * Real.cos) = fun γ => -(r γ) * Real.cos γ := by
      funext γ; simp only [Pi.neg_apply, Pi.mul_apply]
    have h := ((hr.differentiableAt.hasDerivAt.neg).mul (Real.hasDerivAt_cos β)).deriv
    rw [hfun] at h
    rw [h]
    simp only [Pi.neg_apply, Pi.mul_apply]
    ring
  have hX2 : deriv (deriv (fun γ => -(r γ) * Real.cos γ)) α =
      -(deriv (deriv r) α * Real.cos α - 2 * deriv r α * Real.sin α - r α * Real.cos α) := by
    have hfun : deriv (fun γ => -(r γ) * Real.cos γ) =
        (fun β => r β * Real.sin β) - fun β => deriv r β * Real.cos β := by
      funext β
      rw [hX1 β]
      simp only [Pi.sub_apply]
      ring
    rw [hfun]
    have hA : HasDerivAt (fun β => r β * Real.sin β)
        (deriv r α * Real.sin α + r α * Real.cos α) α :=
      hr.differentiableAt.hasDerivAt.mul (Real.hasDerivAt_sin α)
    have hB : HasDerivAt (fun β => deriv r β * Real.cos β)
        (deriv (deriv r) α * Real.cos α + deriv r α * (-Real.sin α)) α :=
      hr'.differentiableAt.hasDerivAt.mul (Real.hasDerivAt_cos α)
    rw [(hA.sub hB).deriv]
    ring
  have hY1 : ∀ β, deriv (r * Real.sin) β = deriv r β * Real.sin β + r β * Real.cos β := by
    intro β
    rw [deriv_mul (hr β) (Real.differentiableAt_sin), Real.deriv_sin]
  have hY2 : deriv (deriv (r * Real.sin)) α =
      deriv (deriv r) α * Real.sin α + 2 * deriv r α * Real.cos α - r α * Real.sin α := by
    have hfun : deriv (r * Real.sin) = deriv r * Real.sin + r * Real.cos := funext hY1
    rw [hfun, deriv_add ((hr'.mul Real.differentiable_sin).differentiableAt)
        ((hr.mul Real.differentiable_cos).differentiableAt),
      deriv_mul (hr' α) Real.differentiableAt_sin, deriv_mul (hr α) Real.differentiableAt_cos,
      Real.deriv_sin, Real.deriv_cos]
    ring
  have harith := arc_ident_arith (r α) (deriv r α) (deriv (deriv r) α) (Real.sin α) (Real.cos α)
    (Real.sin_sq_add_cos_sq α)
  rw [hY2, hX2, hY1 α, hX1 α]
  nlinarith [harith]

lemma leftArc_second_deriv_nonpos (r : ℝ → ℝ)
    (hr : Differentiable ℝ r) (hr' : Differentiable ℝ (deriv r)) {η : ℝ} (hη0 : 0 < η)
    (hηsmall : η < 1 / 8) {α : ℝ} (hrpos : 0 < r α) (hrlow : 1 - η ≤ r α)
    (hr2 : |deriv (deriv r) α| < η) :
    deriv (deriv (r * Real.sin)) α * deriv (fun β => -(r β) * Real.cos β) α -
      deriv (r * Real.sin) α * deriv (deriv (fun β => -(r β) * Real.cos β)) α ≤ 0 := by
  rw [leftArc_second_deriv_identity r hr hr' α]
  have hle : r α * deriv (deriv r) α ≤ r α * η :=
    mul_le_mul_of_nonneg_left (le_of_lt (abs_lt.mp hr2).2) (le_of_lt hrpos)
  have h1 : (0 : ℝ) < r α * (r α - η) := by nlinarith [hrlow, hηsmall, hrpos]
  nlinarith [hle, h1, sq_nonneg (deriv r α)]

end Commons.Geometry.Ulam
