import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.Cores.pPureShiftAux.MajEst
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `H2W/PsiSlices/CascadeRecursion` — the cascade recursion for class-legal data

The amplitude balance of the level tower at `θ = π/2` (`(1-N²)·B = α²z²·B₂ + α(5+α)z·B₁`, from
`WeakPureAux.cascadeBalance` / `cascadeBalance_sourceless`), transported to the radial shifts of a
weak-class datum, where the class makes the source `ℋ⁰`-honest for the levels `m ≤ 2`:

* `hkMem_zero_DzIter_source` — `HkMem α 2 F` implies `HkMem α 0 (D_z^m F)` for `m ≤ 2`;
* `contDiffOn_slice_DzIter_psi` — the `θ`-slice of a radial shift is `C^∞` on `(0, π/2)`;
* **`cascadeRecursion`** — the level-`m` (`m ≤ 2`) amplitude balance for a class datum;
* **`cascadeAmpZero_level`** — a nonzero order-`N` (`N ≥ 2`) amplitude of the level-`m` slice
  (`m ≤ 2`) is incompatible with the order-`N` amplitudes of its two `z`-derivatives existing;
* **`cascadeAscentStep`** / **`cascadeAscentStepLevel`** — the top-order step: with `B ≠ 0`, the
  order-`(N+2)` amplitude of `D_z^{m+1} Ψ` or of `D_z^{m+2} Ψ` is nonzero.

See `PsiSlices/NOTES_pzIterSliceIntegrable_addendum3.md` §5 for what these prove collectively
(the amplitude world is asymmetric; the iteration stops at level `2`, where the class's source
honesty ends).
-/

namespace Work.FTS.EllipticEst.H2W.PsiSlices

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-! ## The cascade recursion at the radial shifts of a class datum

`H2W/WeakPureAux/cascadeBalance.lean` and `cascadeSourceless.lean` prove the amplitude balance of
the tower at `θ = π/2` for a datum whose *source* is `ℋ⁰`-honest:

  `(1 - N²)·B = α²z²·B₂ + α(5+α)z·B₁`   (`N ≥ 2`),

`B` being the order-`N` amplitude of the slice and `B₁`, `B₂` the order-`(N+2)` amplitudes of its
two `z`-derivatives.  For the *weak class* that source honesty is available only at the levels
`m ≤ 2` (`HkMem α 2 F` implies `HkMem α 0 (D_z^m F)` there), and the level-`m` equation is that of
the shifted datum `(D_z^m F, D_z^m Ψ)` (`TT.bslOp_DzIter_eq`).  This section records the resulting
*class-level* recursion — the object the cascade analysis of `WeakPureAux/NOTES_cascade.md` runs
on — together with the level-`m` "no isolated higher-order amplitude" statement: a nonzero
order-`N` (`N ≥ 2`) amplitude at level `m ≤ 2` forces the order-`N` amplitudes of the two
neighbouring slices to *fail to exist*.  (The remaining two ingredients of the cascade — the
*ascent* along the levels and the *summability obstruction* — are recorded as the next steps in
`NOTES_pzIterSliceIntegrable_addendum3.md`.) -/







end
end Work.FTS.EllipticEst.H2W.PsiSlices
