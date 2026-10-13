/-
# `Work.R1G.Support` — where the G-route's deficit lives

The explicit cut-off deficit `Work.R1G.cutDeficit` is *localised*: the `St1` bump `χ` satisfies
`χ = 1` on `|x| ≤ 1` and `χ = 0` off `|x| < 2`, so its derivative vanishes in the transparent region
`ρ < L` and in the vacuum `ρ > 2L`.  Consequently the deficit of the interface — the *only* leftover
of residual R1 at the honest (modulated) data — is supported in the closed annulus
`L ≤ ρ ≤ 2L`, exactly where the cut field differs from the self-similar one.

Combined with `Work.R1G.ModulatedData.meridianResid_cut_eq_cutDeficit` this gives the sharp form of
the G-route's cancellation: **the constructed field, paired with the self-similar stream function,
solves the meridian equation on the whole transparent region `ρ < L`** — in particular inside the
`St5` witness ball, where the blow-up lower bound lives.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.R1G.GEquation
import Submission.Work.R1G.cutDeficit_eq_zero_of_rho_lt
import Submission.Work.R1G.cutDeficit_eq_zero_of_two_mul_lt_rho

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.R1G

variable {α : NNReal}

/-- **The explicit deficit is supported in the closed annulus `L ≤ ρ ≤ 2L`.**  It vanishes where the
cut-off is transparent (`ρ < L`) and where the constructed field vanishes (`2L < ρ`). -/
theorem cutDeficit_eq_zero_of_not_mem_annulus {α : NNReal}
    (P : Work.ConstructionInstance.ProfileData α) (ψ W : ℝ → ℝ → ℝ → ℝ) {r z t : ℝ}
    (h : Work.Cyl.rhoP r z < P.L ∨ 2 * P.L < Work.Cyl.rhoP r z) :
    cutDeficit P ψ W r z t = 0 := by
  rcases h with h | h
  · exact cutDeficit_eq_zero_of_rho_lt P ψ W h
  · exact cutDeficit_eq_zero_of_two_mul_lt_rho P ψ W h

/-- **The cut field solves the meridian equation in the transparent region `ρ < L`.**  At the
self-similar pair with the profile equation at the effective rate (`hres`), the meridian residual of
the *cut* field `χ(ρ/L)·ssVort` against the self-similar stream function vanishes identically for
`ρ(r,z) < L`: the deficit is supported in `L ≤ ρ ≤ 2L` and nowhere else. -/
theorem meridianResid_cut_ssVortOf_eq_zero_of_rho_lt (P : Work.ConstructionInstance.ProfileData α)
    {p κ : ℝ} (hp : 0 < p) {lam : ℝ → ℝ} {F Φ : ℝ → ℝ → ℝ}
    {r z t : ℝ} (hr : 0 < r) (hz : 0 < z) (ht : 0 < t)
    (hlam : 0 < lam t) (hder : HasDerivAt lam (-κ) t)
    (hF : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => F q.1 q.2)
      (Work.Cyl.rhoP r z ^ p / lam t, Work.Cyl.thetaP r z))
    (hΦ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2)
      (Work.Cyl.rhoP r z ^ p / lam t, Work.Cyl.thetaP r z))
    (hres : profileResidGen p κ F Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z) = 0)
    (hρ : Work.Cyl.rhoP r z < P.L) :
    Work.CoreResiduals.meridianResid
        (fun r z t => Work.Stability.chi (Work.Cyl.rhoP r z / P.L)
          * Work.CoreResiduals.ssVort p lam F r z t)
        (Work.CoreResiduals.ssPsi p lam Φ) r z t = 0 := by
  rw [meridianResid_cut_ssVortOf_eq P hp hr hz ht hlam hder hF hΦ hres]
  exact cutDeficit_eq_zero_of_not_mem_annulus P _ _ (Or.inl hρ)

/-- **The G-route's cancellation, sharply.**  At a `ModulatedData` whose `g`-equation has vanishing
far-field term (the honest modulation), the constructed (cut) field paired with the self-similar
stream function satisfies the meridian equation on the whole transparent region `ρ < L` — in
particular on the `St5` witness ball.  The residual R1 of the interface is therefore *localised to
the annulus* `L ≤ ρ ≤ 2L`. -/
theorem ModulatedData.meridianResid_cut_eq_zero_of_rho_lt (D : ModulatedData α)
    (hΦ : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      ContDiffAt ℝ 2 (fun q : ℝ × ℝ => D.Φ q.1 q.2) (z, θ))
    (hF : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      ContDiffAt ℝ 1 (fun q : ℝ × ℝ => profOf D.P q.1 q.2) (z, θ))
    (hFar : ∀ z θ : ℝ, D.Far z θ = 0)
    {r z t : ℝ} (hr : 0 < r) (hz : 0 < z) (ht : t ∈ Set.Ioo 0 D.P.T)
    (hρ : Work.Cyl.rhoP r z < D.P.L) :
    Work.CoreResiduals.meridianResid
        (fun r z t => Work.Stability.chi (Work.Cyl.rhoP r z / D.P.L) * ssVortOf D.P r z t)
        (ssPsiOf D.P D.Φ) r z t = 0 := by
  rw [D.meridianResid_cut_eq_cutDeficit hΦ hF hFar r z t hr hz ht]
  exact cutDeficit_eq_zero_of_not_mem_annulus D.P _ _ (Or.inl hρ)

end Work.R1G
