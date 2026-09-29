import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.NrmSpec

/-!
# `Work.CNum.SerUpDefs` — the state invariant behind the `serUp` certificate

`Work.CNum.serUp x y e` is the fixed-point (mantissa, scale `SC = 2^30`) upper bound for
`log ‖h w‖`, where `h = Submission.CDTPlan.hauptH` is the hauptmodul and `w` is any point of the
closed ball of centre `c = (x + iy)/SC` and radius `ρ = e/SC`.  The certificate evaluates the
logarithmic series

  `log ‖h w‖ ≤ log 256 + log R + 24 Σ_{n < SERM} log (‖1 + c^{n+1}‖ + (n+1) R^n ρ)
      + 24 R^(SERM+1)/(1-R)`,   `R = ‖c‖ + ρ`,

term by term, carrying an integer mantissa `(px, py)` for `c^(k+1)`, an integer mantissa `pe` for
the accumulated error, and an integer mantissa `sg` for `σ^k`.

This file only *defines* the auxiliary objects so that the lemmas about them can be stated and
proved in parallel.  The invariant `SerInv x y e σ k px py pe sg` says that at step `k`

* `pe ≥ 0` and `m2r pe ≤ 3`;
* `R^k ≤ m2r sg ≤ 2`;
* `‖c^(k+1) - (px + i py)/SC‖ ≤ m2r pe`;
* `|SC + px| ≤ 2^34` and `|py| ≤ 2^34`, so that `NrmUpSpec` applies to the mantissa pair
  `(SC + px, py)`.
-/

namespace Work.CNum

open Work.ANum

/-- The complex point `(x + i y)/SC` attached to the mantissa pair `(x, y)`. -/
noncomputable def spt (x y : ℤ) : ℂ := ((x : ℝ) + (y : ℝ) * Complex.I) / (SC : ℝ)

/-- The radius `R = ‖c‖ + ρ` of the disc on which the series is evaluated
(`ρ = m2r e` is the radius of the input ball). -/
noncomputable def srad (x y e : ℤ) : ℝ := ‖spt x y‖ + m2r e

/-- The `k`-th term of the logarithmic series to be bounded. -/
noncomputable def sT (x y e : ℤ) (k : ℕ) : ℝ :=
  Real.log (‖(1 : ℂ) + spt x y ^ (k + 1)‖ + ((k : ℝ) + 1) * srad x y e ^ k * m2r e)

/-- Real part of `SC · (c · p)` rounded up, `p = (px + i py)/SC`. -/
def snx (x y px py : ℤ) : ℤ := -Int.ediv (-(px * x - py * y)) SC

/-- Imaginary part of `SC · (c · p)` rounded up, `p = (px + i py)/SC`. -/
def sny (x y px py : ℤ) : ℤ := -Int.ediv (-(px * y + py * x)) SC

/-- Accumulated mantissa error after one multiplication by `c` (upward rounded, plus `2/SC`). -/
def snpe (σ pe : ℤ) : ℤ := mulU σ pe + 2

/-- Bound for `σ ^ (k+1)` after one step. -/
def snsg (σ sg : ℤ) : ℤ := mulU sg σ

/-- The upper-bound mantissa for the `k`-th series term. -/
def shi (x y σ e : ℤ) (k : ℕ) (px py pe sg : ℤ) : ℤ :=
  nrmUp (SC + px) py + pe + ((k : ℤ) + 1) * mulU e sg + 4

/-- The state invariant of the `serAuxB` recursion at step `k`. -/
def SerInv (x y e σ : ℤ) (k : ℕ) (px py pe sg : ℤ) : Prop :=
  0 ≤ pe ∧ m2r pe ≤ 3 ∧ srad x y e ^ k ≤ m2r sg ∧ m2r sg ≤ 2 ∧
  ‖spt x y ^ (k + 1) - spt px py‖ ≤ m2r pe ∧
  Int.natAbs (SC + px) ≤ 2 ^ 34 ∧ Int.natAbs py ≤ 2 ^ 34

/-! ## The certificate-shaped terms

`serAuxB` accumulates, after `k` multiplications (`p ≈ SC·c^{k+1}`, `sg ≈ σ^k`), the bound
`24 · logUpM (shi x y σ e k px py pe sg)`: the coefficient multiplying `ρ = m2r e` there is
`k+1` **at the level whose countdown is `k+1`**, i.e. the exponent of `c` is `k+1` while the
coefficient is `SERM-k`.  These two auxiliary quantities record that state of affairs. -/

/-- The coefficient `(SERM - k) · R^k · ρ` carried by the term of exponent `k+1`, where
`R = srad x y e` and `ρ = m2r e`.  (`serAuxB`'s own coefficient is `(SERM-k) · m2r sg · e`, and
its `sg` dominates `R^k`, so this is the right comparison shape.) -/
noncomputable def scoef (x y e : ℤ) (k : ℕ) : ℝ :=
  ((SERM - k : ℕ) : ℝ) * srad x y e ^ k * m2r e

/-- The `k`-th term of the series bound in the shape produced by `serAuxB` (exponent `k+1`,
coefficient `SERM - k`). -/
noncomputable def sTc (x y e : ℤ) (k : ℕ) : ℝ :=
  Real.log (‖(1 : ℂ) + spt x y ^ (k + 1)‖ + scoef x y e k)

/-- The perturbation coefficient at exponent `J`: `(SERM + 1 - J) · σ^{J-1} · ρ`. -/
noncomputable def spcoef (σ e : ℤ) (J : ℕ) : ℝ := ((SERM + 1 - J : ℕ) : ℝ) * (m2r σ) ^ (J - 1) * m2r e

/-- The exact telescoping perturbation at exponent `J`: `R^J - c^J`. -/
noncomputable def sdelta (x y e : ℤ) (J : ℕ) : ℝ := srad x y e ^ J - ‖spt x y‖ ^ J

end Work.CNum
