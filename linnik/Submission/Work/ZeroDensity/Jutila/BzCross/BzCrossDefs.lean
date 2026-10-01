import Mathlib
import Submission.Work.ZeroDensity.Jutila.grahamDefs
import Submission.Work.LinnikAreas.Density4.BzS3.S3InnerDefs

/-!
# Vocabulary for the two-sided `S₃` (cross) computation of the Möbius corrections `Bz`

The target of the chapter `BzCrossAux.lean` is Graham's `S₃` term in its two-sided form,

  `Σ_{n ≤ N} Bz_w(n)·Bz_y(n) = N·log(N/y) + O(N)`   (`1 ≤ w ≤ y ≤ N`),

with `Bz_z(n) = Σ_{z < d ∣ n} μ(d)·log(d/z)` (`grahamDefs.lean`).  This file fixes the objects of
the exact reindexing which reduces that sum to the inner squarefree-coprime `m`-sum `s3G` of
`LinnikAreas.Density4.BzS3.S3InnerDefs`.

## The reindexing

Writing the two divisor variables of `Bz_w(n)` and `Bz_y(n)` as `d` and `e` (`w < d ∣ n`,
`y < e ∣ n`), putting `m = gcd(d,e)`, `t = d/m`, `r = e/m` (so `(r,t) = 1` and `d = m·t`,
`e = m·r`) and `n = q·r·t·m`, the termwise identity `μ(d)μ(e) = μ(m)²μ(r)μ(t)` (valid because
squarefreeness forces `m ⊥ r·t`) gives

  `Σ_{n≤N} Bz_w(n)·Bz_y(n) = Σ_{q,r,t} [r ⟂ t]·μ(r)μ(t)·
      Σ_{m ≤ ⌊N/(qrt)⌋, (m,rt)=1, m sqfree, mt > w, mr > y} log(mt/w)·log(mr/y)`.

The inner sum is over `m ∈ (B, M]` with `B = max ⌊w/t⌋ ⌊y/r⌋` and `M = ⌊N/(qrt)⌋`, hence equals
`s3G (r*t) (log(w/t)) (log(y/r)) M − s3G (r*t) (log(w/t)) (log(y/r)) B` because
`log(mt/w) = log m − log(w/t)` and `log(mr/y) = log m − log(y/r)`.

## The restriction of the `q`-, `r`-, `t`-ranges

The inner `m`-sum is empty unless both conditions `mt > w` and `mr > y` are satisfiable inside
`m ≤ ⌊N/(qrt)⌋`, which forces (`t ≥ 1`, `r ≥ 1`)

  `q·t·y < N`   (from `y < mr ≤ N/(qt)`),   `q·r·w < N`   (from `w < mt ≤ N/(qr)`),

so that the only non-vanishing terms have `q ≤ ⌊N/y⌋`, `r ≤ ⌊N/(q·w)⌋`, `t ≤ ⌊N/(q·y)⌋` — the
ranges of `czCross` below.  (Note that with `w ≤ y` the `t`-bound is the sharper one; it is the
one that produces the main term `N·log(N/y)` at the end: the `q`-sum runs only up to `N/y`.)

## The three pieces

With `α = czAl w t = log(w/t)`, `β = czBe y r = log(y/r)`, `MM = czMM r t`, the "main term"
`czMain c α β X = s3c c·X·((log X − α − 1)(log X − β − 1) + 1)` of `s3G c α β X` splits the sum:

* `czCross w y N`           — the exact reindexed sum (with the floor `⌊N/(qrt)⌋`);
* `czModelFloor w y N`      — the same sum with `s3G` replaced by its main term `s3main`;
* `czModelCont w y N`       — as `czModelFloor`, but with `⌊N/(qrt)⌋` replaced by `N/(qrt)`;
* `czModelB w y N`          — the part taken at the *lower* cut-off `B = max ⌊w/t⌋ ⌊y/r⌋`.

The expected estimates are `czCross − (czModelFloor − czModelB) = O(N)` (the accumulated Abel
error), `czModelFloor − czModelCont = O(N)` (the floor error), `czModelCont = N log(N/y) + O(N)`
(the main term) and `czModelB = O(N)` (the boundary contribution).
-/

namespace Work.ZeroDensity.Jutila

open Finset

noncomputable section

/-- The Möbius multiplier `[r ⟂ t]·μ(r)·μ(t)` of the reindexed sum. -/
def czMM (r t : ℕ) : ℝ :=
  if Nat.Coprime r t then
    (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0

/-- `α = log(w/t)`: the shift attached to the divisor `d = m·t` of the `w`-side. -/
def czAl (w : ℝ) (t : ℕ) : ℝ := Real.log (w / (t : ℝ))

/-- `β = log(y/r)`: the shift attached to the divisor `e = m·r` of the `y`-side. -/
def czBe (y : ℝ) (r : ℕ) : ℝ := Real.log (y / (r : ℝ))

/-- The upper cut-off `M = ⌊N/(qrt)⌋` of the inner `m`-sum. -/
def czUp (N q r t : ℕ) : ℕ := N / (q * r * t)

/-- The lower cut-off `B = max ⌊w/t⌋ ⌊y/r⌋` of the inner `m`-sum: `mt > w` and `mr > y`
hold exactly for `B < m`. -/
def czLo (w y : ℝ) (r t : ℕ) : ℕ := max ⌊w / (t : ℝ)⌋₊ ⌊y / (r : ℝ)⌋₊

/-- Upper bound `⌊N/y⌋` of the `q`-range. -/
def czQ (y : ℝ) (N : ℕ) : ℕ := ⌊(N : ℝ) / y⌋₊

/-- Upper bound `⌊N/(q w)⌋` of the `r`-range. -/
def czR (w : ℝ) (N q : ℕ) : ℕ := ⌊(N : ℝ) / ((q : ℝ) * w)⌋₊

/-- Upper bound `⌊N/(q y)⌋` of the `t`-range. -/
def czT (y : ℝ) (N q : ℕ) : ℕ := ⌊(N : ℝ) / ((q : ℝ) * y)⌋₊

/-- The real-cut-off main term `C_c·X·((log X − α − 1)(log X − β − 1) + 1)` of `s3G`.
At an integer `X` it agrees with `LinnikAreas.Density4.BzS3.s3main c α β X`. -/
def czMain (c : ℕ) (α β X : ℝ) : ℝ :=
  LinnikAreas.Density4.BzS3.s3c c * X * ((Real.log X - α - 1) * (Real.log X - β - 1) + 1)

/-- At an integer cut-off `czMain` is `s3main`. -/
lemma czMain_natCast (c X : ℕ) (α β : ℝ) :
    czMain c α β (X : ℝ) = LinnikAreas.Density4.BzS3.s3main c α β X := rfl

/-- **The exact reindexed two-sided `S₃` sum.**  For `1 ≤ w ≤ y`, `y ≤ N`,
`Σ_{n ≤ N} Bz_w(n)·Bz_y(n)` equals the triple sum over
`q ≤ ⌊N/y⌋`, `r ≤ ⌊N/(qw)⌋`, `t ≤ ⌊N/(qy)⌋` of `[r ⟂ t]μ(r)μ(t)` times the difference of the
two inner squarefree-coprime sums at the cut-offs `M = ⌊N/(qrt)⌋` and `B = max ⌊w/t⌋ ⌊y/r⌋`. -/
def czCross (w y : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 (czQ y N), ∑ r ∈ Finset.Icc 1 (czR w N q),
    ∑ t ∈ Finset.Icc 1 (czT y N q),
      czMM r t * (LinnikAreas.Density4.BzS3.s3G (r * t) (czAl w t) (czBe y r) (czUp N q r t)
        - LinnikAreas.Density4.BzS3.s3G (r * t) (czAl w t) (czBe y r) (czLo w y r t))

/-- The model sum at the upper cut-off, `s3G` replaced by `s3main` (floor cut-off). -/
def czModelFloor (w y : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 (czQ y N), ∑ r ∈ Finset.Icc 1 (czR w N q),
    ∑ t ∈ Finset.Icc 1 (czT y N q),
      czMM r t * LinnikAreas.Density4.BzS3.s3main (r * t) (czAl w t) (czBe y r) (czUp N q r t)

/-- The model sum at the upper cut-off with the floor `⌊N/(qrt)⌋` replaced by the real value
`N/(qrt)` (the "continuous model"). -/
def czModelCont (w y : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 (czQ y N), ∑ r ∈ Finset.Icc 1 (czR w N q),
    ∑ t ∈ Finset.Icc 1 (czT y N q),
      czMM r t * czMain (r * t) (czAl w t) (czBe y r) ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ)))

/-- The model sum at the lower cut-off `B = max ⌊w/t⌋ ⌊y/r⌋`. -/
def czModelB (w y : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 (czQ y N), ∑ r ∈ Finset.Icc 1 (czR w N q),
    ∑ t ∈ Finset.Icc 1 (czT y N q),
      czMM r t * LinnikAreas.Density4.BzS3.s3main (r * t) (czAl w t) (czBe y r) (czLo w y r t)

end

end Work.ZeroDensity.Jutila
