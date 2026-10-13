/-
# `Work.FTS.EllSol.EllPkgAux.MollConvDefs` — the vocabulary of the double-mollification smoothness

`Work.FTS.EllSol.EllPkgAux.mollAdm` asserts that the doubly-mollified datum
`zmoll G δ ε` is `C^∞` on the half strip `(0,∞) × (-1, π/2+1)` and vanishes on the two
angular boundary lines.  The proof route used here is the *two-dimensional convolution* one:

* `Hxy G` is the uncurried integrand `(t,s) ↦ Qext G (exp t) s`;
* `Kd δ ε` is the two-dimensional mollifier `(t,s) ↦ sKer δ t · sKer ε s`;
* `Gquad G` kills `G` outside the open quadrant — the hypotheses of `TraceClass` only concern
  the open quadrant and the two boundary lines, so replacing `G` by `Gquad G` does not change
  `Qext` on the range of arguments met by the mollification, while it makes the integrand
  vanish off `[-π/2 π]` in the angular variable;
* `E2sl G w = ∫_{Iθ} (∂_θ²G(w,θ))² σ_η(θ)` and `MG G` is the dominating function used to
  bound the slice `G(w,·)` on `(0,π/2)` by a function of `w` alone that is locally integrable.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The datum `G` killed outside the *open* quadrant.  All the hypotheses of `TraceClass` and
`FourInts` concern the open quadrant (and the two boundary lines, where `TraceClass` provides
the values), so `Gquad G` may be used in place of `G` when the arguments of `Qext` are known
to lie in `(0,π/2)`. -/
def Gquad (G : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => if θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) then G z θ else 0

/-- The uncurried integrand of the double mollification, `(t,s) ↦ Qext G (exp t) s`. -/
def Hxy (G : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => Work.FTS.EllSol.PkgK5.K5c.Qext G (Real.exp p.1) p.2

/-- The two-dimensional mollifier `(t,s) ↦ sKer δ t · sKer ε s` (`t` is the logarithmic radial
variable, `s` the angular one). -/
def Kd (δ ε : ℝ) : ℝ × ℝ → ℝ :=
  fun p => Work.FTS.EllSol.PkgK5.K5c.sKer δ p.1 * Work.FTS.EllSol.PkgK5.K5c.sKer ε p.2

/-- The angular slice functional `∫_{Iθ} (∂_θ²G(w,θ))² σ_η(θ)` (without the radial weight). -/
def E2sl (G : ℝ → ℝ → ℝ) (w : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2
    * Work.FTS.EllipticEst.thEta θ

/-- **The dominating function of the slice.**  `MG G w` bounds `|G w τ|` uniformly for
`τ ∈ (0,π/2)`; it is built from the two interior values at `θ = π/4` (continuous, hence locally
bounded, in `w`) and the square root of the slice functional `E2sl G w` (locally integrable in
`w` by Cauchy–Schwarz from the `ttIntS`-integrability hypothesis). -/
def MG (G : ℝ → ℝ → ℝ) (w : ℝ) : ℝ :=
  |G w (Real.pi / 4)| + |Work.Spaces.pth G w (Real.pi / 4)| + Real.sqrt (E2sl G w)

/-- The half strip which is the domain of the strip-admissibility predicate. -/
def Strp : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)

end Work.FTS.EllSol.EllPkgAux
