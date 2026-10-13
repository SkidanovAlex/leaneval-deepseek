/-
Copyright: work module for the Elgindi finite-time singularity project.

# Vocabulary for the right-endpoint lemma `sliceRightSmall`

The one-dimensional operator `Lzero1 u = -u'' + (tan θ · u)' - 6u` has the explicit kernel
element `y₁ θ = sin 2θ`.  Against `y₁` we form the **Wronskian flux**

  `Bflux u θ = cos θ * (u'(θ) * sin 2θ - u(θ) * 2 cos 2θ) = cos θ * (sin 2θ)^2 * (u/sin 2θ)'(θ)`

and its companion

  `Wn u θ = u θ / sin 2θ`.

They satisfy the two pointwise identities (proved in `SRSAux/BIdent.lean`)

* `deriv (Bflux u) θ = -cos θ * sin 2θ * Lzero1 u θ`  (so `Bflux` is a primitive of an
  `L¹` function of `Lzero1 u`, and therefore has a limit at `π/2`);
* `deriv (Wn u) θ = Bflux u θ / (cos θ * (sin 2θ)^2)`.

The endpoint analysis of `sliceRightSmall` rests on these: `Wn` is the amplitude of `u`
(`u = Wn u · sin 2θ`), and the only way `Wn` can grow like `δ^{-2}` (`δ = π/2 - θ`, the bad
mode `~ δ^{-1}` of `u`) is for `Bflux` to stay away from `0` near `π/2`; the weighted
`L²`-integrability of `u` forbids exactly that, and the weighted `L²`-integrability of
`Lzero1 u` then bounds `Bflux` quantitatively.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.FTS.EllipticEst.AngAWeak.AngWeakDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

/-- The Wronskian flux of `u` against the kernel element `sin 2θ`. -/
def Bflux (u : ℝ → ℝ) (θ : ℝ) : ℝ :=
  Real.cos θ * (deriv u θ * Real.sin (2 * θ) - u θ * (2 * Real.cos (2 * θ)))

/-- The amplitude of `u` above `sin 2θ`: `Wn u θ = u θ / sin 2θ`. -/
def Wn (u : ℝ → ℝ) (θ : ℝ) : ℝ := u θ / Real.sin (2 * θ)

end Work.FTS.EllipticEst.AngAWeak
