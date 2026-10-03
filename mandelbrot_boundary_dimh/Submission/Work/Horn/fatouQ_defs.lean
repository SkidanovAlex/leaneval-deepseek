import Mathlib
import Submission.Work.Horn.flower_q
import Submission.Work.FatouCoord.Main

/-!
# The approximate Fatou coordinate of a parabolic germ of order `q+1` (definitions)

For a germ `f z = z (1 + z^q H z)` with `H = Hfun f q a` holomorphic at `0` and `H 0 = a ≠ 0`
we build the *approximate* Abel coordinate

  `A z = c / z^q + ∑_{i=1}^{q-1} (g_i / (i - q)) (1/z)^{q-i} + (g_q + (q+1)/2) log z`,

where `c = cc q a = -1/(q a)` is the chart constant and `g_i` are the Taylor coefficients of
`1 / H` at `0`.  Its defect `A (f z) - A z - 1` is `O (z ^ (q+1))` on the petal; the Fatou
coordinate is then this coordinate minus the sum of the defects along the orbit.

All the analytic content is in the companion files (`Acorr_defect`, ...); here we only fix the
vocabulary, so that the pieces can be stated and proved separately.

## Main definitions

* `gcoef f q a i` — the coefficient of `z ^ i` in the Taylor expansion of `1 / Hfun f q a` at `0`;
* `Lbranch q a z` — the branch of `log` on the petal, normalised through the chart `z^q / c`;
* `Acorr f q a z` — the approximate Abel coordinate;
* `zBranch q a j w` — the inverse chart, the `j`-th branch of the `q`-th root;
* `gfun f q a j w` — the chart dynamics `w ↦ c / (f z)^q`,
* `Xfun f q a j w = Acorr f q a (zBranch q a j w)` and the defect `Efun`.
-/

namespace Work.Horn.FatouQ

open Work.Horn.Flower

noncomputable section


/-- Bundling of the quantitative input used throughout the `FatouQ` development: the germ
hypotheses (`Flower.Setup`), the quantitative bounds at radius `ρ` (`Flower.Bounds`) and the
petal facts at level `M` (`Flower.PetalFacts`), together with the two scale conditions
`‖cc‖/M < ρ^q` (petals inside the disc of the bounds) and `0 < M`. -/
structure PetalDatum (f : ℂ → ℂ) (D : Set ℂ) (q : ℕ) (a : ℂ) (ρ M : ℝ) : Prop where
  hS : Setup f D q a
  hρ : 0 < ρ
  hb : Bounds f D q a ρ
  hM : 0 < M
  hRM : ‖cc q a‖ / M < ρ ^ q
  hgeo : PetalFacts q a M

/-- The coefficient of `z ^ i` in the Taylor expansion of `1 / H` at `0`, where
`H = Hfun f q a = (f z - z)/z^(q+1)` (`H 0 = a`). -/
def gcoef (f : ℂ → ℂ) (q : ℕ) (a : ℂ) (i : ℕ) : ℂ :=
  iteratedDeriv i (fun z : ℂ => (Hfun f q a z)⁻¹) 0 / ((i.factorial : ℕ) : ℂ)

/-- The branch of the logarithm used on the petal: `log z` is defined through the chart
`z ^ q / c`, which takes values in the right half plane on the petal. -/
def Lbranch (q : ℕ) (a : ℂ) (z : ℂ) : ℂ :=
  (Complex.log (z ^ q / cc q a) + Complex.log (cc q a)) / (q : ℂ)

/-- The approximate Abel (Fatou) coordinate of the germ in the `z`-plane. -/
def Acorr (f : ℂ → ℂ) (q : ℕ) (a : ℂ) (z : ℂ) : ℂ :=
  cc q a / z ^ q
    + (∑ i ∈ Finset.Icc 1 (q - 1), gcoef f q a i / ((i : ℂ) - (q : ℂ)) * (z⁻¹) ^ (q - i))
    + (gcoef f q a q + ((q : ℂ) + 1) / 2) * Lbranch q a z

/-- The inverse of the chart `z ↦ c/z^q` on the `j`-th petal. -/
def zBranch (q : ℕ) (a : ℂ) (j : Fin q) (w : ℂ) : ℂ := rootFun q a j (cc q a / w)

/-- The dynamics in the chart `w = c / z^q`. -/
def gfun (f : ℂ → ℂ) (q : ℕ) (a : ℂ) (j : Fin q) (w : ℂ) : ℂ :=
  chartQ q a (f (zBranch q a j w))

/-- The approximate coordinate in the chart. -/
def Xfun (f : ℂ → ℂ) (q : ℕ) (a : ℂ) (j : Fin q) (w : ℂ) : ℂ :=
  Acorr f q a (zBranch q a j w)

/-- The defect of the approximate coordinate in the chart. -/
def Efun (f : ℂ → ℂ) (q : ℕ) (a : ℂ) (j : Fin q) (w : ℂ) : ℂ :=
  Xfun f q a j (gfun f q a j w) - Xfun f q a j w - 1

end

end Work.Horn.FatouQ
