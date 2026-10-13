import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.Dz_LGammaT_eq
import Submission.Work.FTS.StrongPersist.H6Aux.LhatCommOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-
# `D_z(𝓛_Γ^T f) = 𝓛̂(D_z f) + E₂ α f` — the transfer of the `D_z`-commutator, open class

The open-class (`Work.FTS.EllipticEst.SmoothOpen`, i.e. genuine `C^∞` on the *open* quadrant
`(0,∞) × (0,π/2)`) twin of `Work.FTS.CoercivityFix.Transfer.Dz_LGammaT_eq`, whose hypothesis is
the interior class `Work.FTS.LocData.SmoothQuad` (`C^∞` on the strip `z > -1`).

With the split `𝓛_Γ^T = 𝓛̂ + Corr` (`CoercivityFix.LGammaT_eq_Lhat_add_Corr`), differentiating the
two `z`-slices at an interior point splits the identity into

* `D_z(𝓛̂ f) = 𝓛̂(D_z f) + Ê₂ f` — `Work.FTS.StrongPersist.H6Aux.Dz_Lhat_of_open`, already stated
  for `SmoothOpen` (the interior character of the `𝒟_z`-commutator of `𝓛̂`);
* `D_z(Corr α f) z θ = Γ(θ)·radS α f z` — `Transfer.Dz_Corr_eq`, which needs only
  `Work.Coercivity.HardyHyp f` and `0 < z` (nothing about smoothness), because `Corr` is an
  angular factor times a purely *radial* profile and `D_z` falls on the radial factor only;
* `Ê₂ f + Γ·radS = E₂ α f` — definitional (`Transfer.E2_eq`).

The two `z`-slices `t ↦ 𝓛̂ f t θ` and `t ↦ Corr α f t θ` are differentiable at `z > 0`: the first
from `SmoothOpen f` (all its summands are slices of `SmoothOpen` functions, differentiated by
`SmoothOpen.hasDerivAt_slice`), the second from `Transfer.hasDerivAt_Corr_slice` (`HardyHyp`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.TransO

theorem Dz_LGammaT_eq_O (α : ℝ) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hfH : Work.Coercivity.HardyHyp f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.Dz (Work.Coercivity.LGammaT α f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
        + Work.FTS.CoercivityFix.Transfer.E2 α f z θ := by
  have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ, hθ2⟩
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩
  -- ## the `z`-slices are differentiable at `z`
  have hfz : HasDerivAt (fun t : ℝ => f t θ) (Work.Spaces.pz f z θ) z :=
    hf.hasDerivAt_slice hθI hz
  have hDzz : HasDerivAt (fun t : ℝ => Work.Spaces.Dz f t θ)
      (Work.Spaces.pz (Work.Spaces.Dz f) z θ) z :=
    hf.Dz.hasDerivAt_slice hθI hz
  have hDthz : HasDerivAt (fun t : ℝ => Work.Spaces.Dth f t θ)
      (Work.Spaces.pz (Work.Spaces.Dth f) z θ) z :=
    hf.Dth.hasDerivAt_slice hθI hz
  have hLz : DifferentiableAt ℝ (fun t : ℝ => Work.FTS.CoercivityFix.Lhat f t θ) z := by
    have hne : (1 + z : ℝ) ≠ 0 := by positivity
    have hfun : (fun t : ℝ => Work.FTS.CoercivityFix.Lhat f t θ)
        = fun t : ℝ => f t θ + Work.Spaces.Dz f t θ - 2 * f t θ / (1 + t)
            - 3 * Work.Spaces.Dth f t θ / (1 + t) :=
      funext fun t => Work.FTS.CoercivityFix.Lhat_eq f t θ
    rw [hfun]
    exact (((hfz.differentiableAt.add hDzz.differentiableAt).sub
      (((differentiableAt_const (2 : ℝ)).mul hfz.differentiableAt).div
        ((differentiableAt_const (1 : ℝ)).add differentiableAt_id) hne)).sub
      (((differentiableAt_const (3 : ℝ)).mul hDthz.differentiableAt).div
        ((differentiableAt_const (1 : ℝ)).add differentiableAt_id) hne))
  have hhasC := Work.FTS.CoercivityFix.Transfer.hasDerivAt_Corr_slice (z := z) (θ := θ)
    α f hfH hz
  have hdiffC : DifferentiableAt ℝ (fun t : ℝ => Work.FTS.CoercivityFix.Corr α f t θ) z :=
    hhasC.differentiableAt
  -- ## the two commutators
  have hL : Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
        + Work.FTS.CoercivityFix.E2hat f z θ :=
    Work.FTS.StrongPersist.H6Aux.Dz_Lhat_of_open Work.FTS.EllipticEst.isOpen_Q0 hf hmem hz
  have hC : Work.Spaces.Dz (Work.FTS.CoercivityFix.Corr α f) z θ
      = Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z :=
    Work.FTS.CoercivityFix.Transfer.Dz_Corr_eq α f hfH hz
  -- ## the slices add
  have hslice : (fun t : ℝ => Work.Coercivity.LGammaT α f t θ)
      = (fun t : ℝ => Work.FTS.CoercivityFix.Lhat f t θ)
        + (fun t : ℝ => Work.FTS.CoercivityFix.Corr α f t θ) := by
    funext t
    rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α f]
    rfl
  -- ## the conclusion
  rw [show Work.Spaces.Dz (Work.Coercivity.LGammaT α f) z θ
      = z * deriv (fun t : ℝ => Work.Coercivity.LGammaT α f t θ) z from rfl]
  rw [hslice, deriv_add hLz hdiffC, mul_add]
  rw [show z * deriv (fun t : ℝ => Work.FTS.CoercivityFix.Lhat f t θ) z
        = Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ from rfl, hL]
  rw [show z * deriv (fun t : ℝ => Work.FTS.CoercivityFix.Corr α f t θ) z
        = Work.Spaces.Dz (Work.FTS.CoercivityFix.Corr α f) z θ from rfl, hC]
  rw [Work.FTS.CoercivityFix.Transfer.E2_eq]
  ring

end Work.FTS.StrongEps.EpsE4Thr.TransO
