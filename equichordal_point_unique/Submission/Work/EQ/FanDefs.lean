import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.charValDefs

/-! Definitions shared by the `fan_trichotomy` development (`Work.EQ.fan_trichotomy`).

The stable fan `fan a h ε` is built from the tail of `ε` outwards: level `j` of a word `ε` is the
suffix `ε.drop j`, and the fan centres walk on `-1/2 + 2ℤ`.  This file fixes the bookkeeping:

* `fanTh a` — the contraction constant `λ(5+a)/((1+a)(5-a))` of the fan walk (Rychlik's `ϑ`);
* `lvl ε j` — the state of the walk carried by level `j` (state `0` is `A₁ = -1/2`);
* `fanN ε j` — the number of non-`A₁` centres strictly inside level `j`;
* `fanPi a K ε j` — the product `∏_{j ≤ l < |ε|} (1 + K λ^{2l})` of the "Cauchy loss" factors;
* `wFan a h ε` — the semi-projective coordinate `y/(x - a/2)` of the fan point. -/

namespace Work.EQ

open Complex Filter _root_.Topology
open scoped BigOperators

noncomputable section

/-- The contraction constant of the fan walk: `ϑ = λ (5+a)/(5-a)`, where `λ = (1-a)/(1+a)`.
It satisfies `λ < ϑ < 1` for `0 < a < 1`, and `λ |(c - a/2)/(c + a/2)| ≤ ϑ` for every centre
`c ∈ -1/2 + 2ℤ` with `c ≠ -1/2`. -/
def fanTh (a : ℝ) : ℝ := (1 - a) * (5 + a) / ((1 + a) * (5 - a))

/-- The state of the fan walk carried by level `j` of the word `ε`, i.e. by the suffix
`ε.drop j`.  State `0` carries the centre `A₁ = -1/2`. -/
def lvl (ε : List Bool) (j : ℕ) : ℕ := stAux (ε.drop j).reverse 0

/-- The number of levels strictly inside level `j` (i.e. `i` with `j < i ≤ |ε|`) whose centre is
not `A₁`.  This is the number of remaining "visits" from level `j` down to the germ. -/
def fanN (ε : List Bool) (j : ℕ) : ℕ :=
  ((Finset.range (ε.length + 1)).filter (fun i => j < i ∧ lvl ε i ≠ 0)).card

/-- The product of the "Cauchy loss" factors over the levels `j ≤ l < |ε|`. -/
def fanPi (a K : ℝ) (ε : List Bool) (j : ℕ) : ℝ :=
  (Finset.Icc j (ε.length - 1)).prod (fun l => 1 + K * (eqLam a) ^ (2 * l))

/-- The semi-projective coordinate `w = y / (x - a/2)` of a fan point (the cotangent of the line
from `O₂ = (a/2, 0)`). -/
def wFan (a : ℝ) (h : ℂ → ℂ) (ε : List Bool) (u : ℂ) : ℂ :=
  (fan a h ε u).2 / ((fan a h ε u).1 - ((a / 2 : ℝ) : ℂ))

end

end Work.EQ
