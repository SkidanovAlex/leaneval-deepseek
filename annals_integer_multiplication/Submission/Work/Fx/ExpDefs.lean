import Mathlib
import Submission.Work.Fx.FxCommon

/-!
# Definitions for the fixed-point complex exponential (`Work.Fx.expCplx`)

* `wprec p = p + 3·size p + 70`: working precision (guard bits).
* `d0 p = 3·size p + 70`, `wcnt p = 8(p+1)`: number of Horner steps.
* `hval z d i = Σ_{k≤i} z^k d!/(d+k)!`: the Horner partial sum (at stage `i`, next divisor `d`);
  `hval z 0 M = Σ_{k≤M} z^k/k!`.
* `pot Z d i = Σ_{k<i} Z^k d!/(d+k)!`: the matching error potential (`pot Z 0 M = Σ_{k<M} Z^k/k!`).
* `stepQre/stepQim`: one fixed-point stage of the recurrence
  `Q ← 1 + (z/dd)·Q`, real/imaginary parts.

State layout (on the value stack, top first) during the fold:
`Qre, Qim, dd, Zs, Zt, Pow, d0` with the dummy list element `1` on top.
-/

set_option autoImplicit false

namespace Work.Fx
open HvdH

/-- Working precision: `p` plus `3·size p + 70` guard bits. -/
def wprec (p : ℕ) : ℕ := p + 3 * p.size + 70

/-- Number of guard bits. -/
def d0 (p : ℕ) : ℕ := 3 * p.size + 70

/-- Number of Horner stages. -/
def wcnt (p : ℕ) : ℕ := 8 * (p + 1)

/-- Size bound carried by the loop invariant. -/
def bsz (p : ℕ) : ℕ := 3 * wprec p + 200

theorem wprec_eq (p : ℕ) : wprec p = p + d0 p := by simp [wprec, d0, Nat.add_assoc]

theorem le_wprec (p : ℕ) : p ≤ wprec p := by simp only [wprec]; omega

theorem one_le_wcnt (p : ℕ) : 1 ≤ wcnt p := by simp only [wcnt]; omega

/-- The complex number encoded by the input `(X, Y)` at precision `p`. -/
noncomputable def zval (p : ℕ) (X Y : ℤ) : ℂ := ((X : ℂ) + (Y : ℂ) * Complex.I) / 2 ^ p

/-- Horner partial sum: `Σ_{k≤i} z^k · d!/(d+k)!` (stage `i`, next divisor `d`). -/
noncomputable def hval (z : ℂ) (d i : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (i + 1), z ^ k * ((d.factorial : ℂ) / ((d + k).factorial : ℂ))

/-- Error potential: `Σ_{k<i} Z^k · d!/(d+k)!`. -/
noncomputable def pot (Z : ℝ) (d i : ℕ) : ℝ :=
  ∑ k ∈ Finset.range i, Z ^ k * ((d.factorial : ℝ) / ((d + k).factorial : ℝ))

/-- Real part of one fixed-point Horner stage. -/
def stepQre (Zs Zt Pow Qre Qim dd : ℤ) : ℤ :=
  Pow + Int.tdiv (Int.tdiv (Zs * Qre - Zt * Qim) Pow) dd

/-- Imaginary part of one fixed-point Horner stage. -/
def stepQim (Zs Zt Pow Qre Qim dd : ℤ) : ℤ :=
  Int.tdiv (Int.tdiv (Zs * Qim + Zt * Qre) Pow) dd

end Work.Fx
