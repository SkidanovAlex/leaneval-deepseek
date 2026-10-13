/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/regQo_const_mul.lean` — `RegQo` is closed under
multiplication by a constant

`RegQo α k f` is the open-quadrant regularity class

  `SmoothOpen f ∧ HkMem α k f ∧ BdryTraces α k f`

(`OpenClass.lean`), i.e. exactly the three ingredients of an interior integration by parts:
`C^∞` on the open quadrant `(0,∞) × (0,π/2)`, honesty of the `ℋ^k`-integrand, and vanishing of
the `k`-th order boundary traces.  `UnifIPO`'s `smul_fst` clause consumes this closure, which is
why it is stated here for an *arbitrary* order `k` and an arbitrary real constant `c`.

The proof is the conjunction of the three closure properties, each already in the team library:

* `SmoothOpen (c·f)` — `Work.FTS.EllipticEst.SmoothOpen.const_mul'` (`EllHyp_certificates.lean`),
  i.e. `ContDiffOn.const` times `ContDiffOn.mul`;
* `HkMem α k (c·f)` — `Work.FTS.LocData.HkMem_const_mul` (`LocData/HkMem_const_mul.lean`):
  the `ℋ^k`-integrand is *exactly* multiplied by `c²` (`hkIntegrand_const_mul`), because `deriv`
  is linear over constants with no differentiability hypothesis, so both integrability clauses
  transfer;
* `BdryTraces α k (c·f)` — `Work.FTS.ClassC.bdryTraces_smul` (`ClassC/A1.lean`): the mixed
  derivative of `c·f` is `c` times the mixed derivative of `f`, so each trace becomes `c²` times
  a trace tending to `0`.

The file is complete and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.ClassC.A1
import Submission.Work.FTS.EllipticEst.EllHyp_certificates

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **`RegQo` is closed under multiplication by a constant.**

If `f` is `C^∞` on the open quadrant, honest in `ℋ^k` and has vanishing boundary traces up to
order `k`, then so is `z ↦ c * f z θ` for every real `c`.  This is the `smul_fst` regularity
requirement of the open coercivity interface `UnifIPO`. -/
theorem regQo_const_mul {α c : ℝ} {k : ℕ} {f : Work.FTS.Galerkin.Fn}
    (h : Work.FTS.StrongEps.EpsE4Thr.RegQo α k f) :
    Work.FTS.StrongEps.EpsE4Thr.RegQo α k (fun z θ => c * f z θ) := by
  obtain ⟨hsm, hmem, htr⟩ := h
  exact ⟨hsm.const_mul' c, Work.FTS.LocData.HkMem_const_mul α k c hmem,
    Work.FTS.ClassC.bdryTraces_smul htr c⟩

end Work.FTS.StrongEps.EpsE4Thr
