import Mathlib.Analysis.Real.Sqrt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseK15.AlphaAux` — the one-variable form of the Bogoliubov angle

FS's squeezing parameter of the two-mode Bogoliubov algebra is

`α(𝒜,ℬ) = ℬ / (𝒜 + √(𝒜²-ℬ²))`  (`Work.BoseB7.alphaCoef`).

It is **homogeneous of degree `0`** in `(𝒜,ℬ)`: for `𝒜 > 0`,

`α(𝒜,ℬ) = ℬ/(𝒜(1 + √(1-(ℬ/𝒜)²))) = h(ℬ/𝒜)`,

with `h(r) = r/(1+√(1-r²))` the `tan(θ/2)`-parametrisation of the angle.  This
file records only the definition of `h`; everything about it lives in the
modules of this directory.
-/

noncomputable section

namespace Work.BoseK15

/-- The one-variable form of the Bogoliubov squeezing parameter:
`h r = r/(1+√(1-r²)) = tan(½·arcsin r)` for `|r| ≤ 1`. -/
noncomputable def h (r : ℝ) : ℝ := r / (1 + Real.sqrt (1 - r ^ 2))

end Work.BoseK15
