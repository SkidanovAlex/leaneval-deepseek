/-
# `Work.FTS.PhiStar.RadialWAux.PhiPsiDefs` — the rescaled Green pieces with a general exponent

`Work.FTS.PhiStar.Radial.radGreen α m c z = K·( z^{-q}·∫₀^z c t^{q-1} dt
                                                   + z^p·∫_{u>z} c u^{-p-1} du )`,
`K = 1/(α(4m+5))`, `p = 2m/α`, `q = (2m+5)/α`.  Substituting `t = z u` in the two integrals gives
the *rescaled* pieces

  `radPhi α m c z = ∫₀¹ c (z u) u^{q-1} du`,   `radPsi α m c z = ∫_{u>1} c (z u) u^{-p-1} du`,

so that `radGreen α m c z = K·(radPhi α m c z + radPsi α m c z)` (`radGreen_eq_rescaled`).

The `(z+1)/z·radGreen` factor of the `FlatW` target needs the *divided* pieces
`radPhi/z` and `radPsi/z`, whose exponents are `q+1` resp. `p-1`; this file fixes the two
general-exponent families

  `PhiQ Q c z = ∫₀¹ c (z u) u^{Q-1} du`,   `PsiP P c z = ∫_{u>1} c (z u) u^{-P-1} du`

(so `radPhi α m = PhiQ (radQ α m)`, `radPsi α m = PsiP (radP α m)`), with the elementary side
facts used by the estimates.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.RadialWAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RadialWAux

set_option autoImplicit false

/-- `PhiQ Q c z = ∫₀¹ c (z u) u^{Q-1} du`, the inner rescaled Green piece with exponent `Q > 0`. -/
def PhiQ (Q : ℝ) (c : ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ u in (0 : ℝ)..1, c (z * u) * u ^ (Q - 1)

/-- `PsiP P c z = ∫_{u>1} c (z u) u^{-P-1} du`, the outer rescaled Green piece. -/
def PsiP (P : ℝ) (c : ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ u in Set.Ioi 1, c (z * u) * u ^ (-P - 1)

/-- `radPhi` is `PhiQ` at the exponent `radQ`. -/
theorem radPhi_eq_PhiQ (α : ℝ) (m : ℕ) (c : ℝ → ℝ) :
    radPhi α m c = PhiQ (radQ α m) c := rfl

/-- `radPsi` is `PsiP` at the exponent `radP`. -/
theorem radPsi_eq_PsiP (α : ℝ) (m : ℕ) (c : ℝ → ℝ) :
    radPsi α m c = PsiP (radP α m) c := rfl

end Work.FTS.PhiStar.RadialWAux
