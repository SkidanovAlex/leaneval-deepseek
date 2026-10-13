/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsE4Thr/TransO/DefsO.lean` — the open-class per-level package of the transfer

`CoercivityFix/Transfer/L4Step.LevelPkg α n IP CC` bundles, for the level-`n` pairing `IP`,

* the algebraic package `Transfer.CommSm α n IP` (congruence on the open quadrant, additivity on
  the finite-order class `Q0Sm`, and the two `𝓛̂`-commutators), and
* for every `f ∈ CoerAdm α`, the two `AddOKSm` triples of the splittings
  `D_θ(𝓛_Γ^T f) = 𝓛̂(D_θf) + E1 α f`, `D_z(𝓛_Γ^T f) = 𝓛̂(D_zf) + E2 α f` together with the two
  Cauchy–Schwarz bounds on the error pairings.

Its regularity clause is *frozen* to the class `Work.FTS.Nonlin.CoerAdm` (`SmoothQuad`), which the
route's projected mollified slices do not satisfy.  This module fixes the open twin
`LevelPkgO`, whose regularity clause is the class `CoerAdmO` of `EpsE4Thr/OpenClass.lean`.  The
`CommSm` component is already phrased in the finite-order class `Q0Sm` and is shared verbatim.

Everything here is `sorry`-free (the module only *defines* a structure).
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.Transfer.CoreDefs
import Submission.Work.FTS.CoercivityFix.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.TransO

open Work.FTS.Galerkin (Fn)
open Work.FTS.StrongEps.EpsE4Thr (CoerAdmO)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The open-class analogue of `Transfer.LevelPkg`**: the algebraic package `CommSm α n IP`
together with, for every `f ∈ CoerAdmO α`, the two split packages of the transfer identities and
the two Cauchy–Schwarz bounds on the error pairings. -/
def LevelPkgO (α : ℝ) (n : ℕ) (IP : Fn → Fn → ℝ) (CC : ℝ) : Prop :=
  Work.FTS.CoercivityFix.Transfer.CommSm α n IP ∧
    (∀ f : Fn, CoerAdmO α f →
      Work.FTS.CoercivityFix.Transfer.AddOKSm α n
          (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f))
          (Work.FTS.CoercivityFix.Transfer.E1 α f) (Work.Spaces.Dth f) ∧
      Work.FTS.CoercivityFix.Transfer.AddOKSm α n
          (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f))
          (Work.FTS.CoercivityFix.Transfer.E2 α f) (Work.Spaces.Dz f) ∧
      |IP (Work.FTS.CoercivityFix.Transfer.E1 α f) (Work.Spaces.Dth f)|
          ≤ CC * Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
              * Work.Spaces.HkNorm α n (Work.Spaces.Dth f) ∧
      |IP (Work.FTS.CoercivityFix.Transfer.E2 α f) (Work.Spaces.Dz f)|
          ≤ CC * Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E2 α f)
              * Work.Spaces.HkNorm α n (Work.Spaces.Dz f))

end Work.FTS.StrongEps.EpsE4Thr.TransO
