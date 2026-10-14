import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.Final.Assembly
import Submission.Work.FTS.Final.Small

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology NNReal
open MeasureTheory Set Filter

namespace Work.FTS.Final

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith IsDynEqOn)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Physical (PhysClock)

set_option autoImplicit false

/-- **The meridian equation of the reconstruction from the dynamics.**

The fake-time equation of the strong route (`hSol.2`) together with the regularity package
`RegPkgMin`, the interior regularity and oddness of the stream function, the static derivation data
and the clock data produce the meridian scalar equation on `(0, C.T)` for the meridian pair
`(merProfile α A B g C, merPsi (pExp α) A B Φ C)` of the physical reconstruction.

This is `Work.FTS.Final.MeridianMin.meridianEq_of_dynEq_of_regPkgMin` with the two interfaces of
the assembly (`IsDynGSolWith`, `ClockData`) unpacked. -/
theorem hMer_of_dyn {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {g Φ : Fam} {A B : ℝ → ℝ} {C : PhysClock}
    (hSol : IsDynGSolWith (IsBslSolPos (Work.FTS.Regularity.pExp α)) (Work.FTS.Regularity.pExp α)
      Φ g)
    (hRegMin : RegPkgMin (Work.FTS.Regularity.pExp α) g)
    (hΦ : ∀ τ : ℝ, 0 < τ →
      ContDiffOn ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2 τ) Work.Construction.Qd)
    (hΦodd : ∀ τ : ℝ, 0 < τ → ∀ Z Θ : ℝ, Φ Z (-Θ) τ = -Φ Z Θ τ)
    (hD : Work.FTS.MeridianDyn.ProfDerivData (Work.FTS.Regularity.pExp α) Φ g)
    (hClock : ClockData (Work.FTS.Regularity.pExp α) Φ g A B C) :
    MeridianEqOn (Work.FTS.Physical.merProfile α A B g C)
      (Work.FTS.MeridianDyn.merPsi (Work.FTS.Regularity.pExp α) A B Φ C) C.T :=
  Work.FTS.Final.MeridianMin.meridianEq_of_dynEq_of_regPkgMin hα hα13 hSol.2 hRegMin hΦ hΦodd hD
    hClock.2.1 hClock.2.2.1 hClock.2.2.2.1 hClock.2.2.2.2 hClock.1


end Work.FTS.Final
