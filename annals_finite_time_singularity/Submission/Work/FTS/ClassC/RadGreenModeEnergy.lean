/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS/ClassC/RadGreenModeEnergy` — the sharp per-mode bound for the Dirichlet Green solution

Instantiates `ModeEnergyCS.modeWeightedEnergy_sq` at the explicit mode-`m` Dirichlet Green
function `a = radGreen α m c` of `PhiStar/Radial/Defs.lean`, whose mode ODE
`−α²z²a'' − α(5+α)za' + λ_m a = c` is `Radial.radGreen_solves` (`λ_m = lamR m = 2m(2m+5)`):

  `μ_m² · ∫_0^∞ a² w²  ≤  ∫_0^∞ c² w²`,   `μ_m = λ_m − 3α² − 3α(5+α)/2 ≥ 11.8` (`m ≥ 1`,
  `α ≤ 1/4`).

The two boundary hypotheses of `modeWeightedEnergy_sq` are the `flux` conditions, supplied by
`flux_radGreen_atTop`/`flux_radGreen_zero` from the asymptotic limits
`radGreen_far_limits`/`radGreen_near_limits`; the four weighted-`L²` integrability hypotheses are
carried explicitly (they are the `radGreen_l2_*` / `radGreen_dzIter_*` bounds of
`EllExist/Honesty/`).

This is the per-mode input of the level-`0` estimate `NOTES_mode_sum_level0.md`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.ModeEnergyCS
import Submission.Work.FTS.ClassC.flux_radGreen_atTop
import Submission.Work.FTS.ClassC.flux_radGreen_zero
import Submission.Work.FTS.ClassC.radGreen_far_limits
import Submission.Work.FTS.ClassC.radGreen_near_limits
import Submission.Work.FTS.PhiStar.Radial.radGreen_solves

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

local notation "w" => Work.Spaces.w
local notation "a" => Work.FTS.PhiStar.Radial.radGreen

/-- **The sharp weighted `L²` per-mode bound for `radGreen`.** -/
theorem radGreen_modeEnergy {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m)
    {c : ℝ → ℝ}
    (hcont : ContinuousOn c (Set.Ioi 0))
    (hdec : ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 1 ≤ t → |c t| ≤ K / t)
    (hvy : ∃ K p : ℝ, 0 < K ∧ 3 / 2 < p ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → |c t| ≤ K * t ^ p)
    (hg0 : MeasureTheory.IntegrableOn
      (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1))
    (hg0' : MeasureTheory.IntegrableOn
      (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioo 0 1))
    (hginf : MeasureTheory.IntegrableOn
      (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1))
    (hderiv : ∀ z : ℝ, 0 < z → HasDerivAt (a α m c) (deriv (a α m c) z) z)
    (hderiv2 : ∀ z : ℝ, 0 < z → HasDerivAt (deriv (a α m c)) (deriv (deriv (a α m c)) z) z)
    (hint1 : MeasureTheory.IntegrableOn
      (fun z => (z * deriv (a α m c) z) ^ 2 * (w z) ^ 2) (Set.Ioi 0))
    (hint2 : MeasureTheory.IntegrableOn
      (fun z => (a α m c z) ^ 2 * (w z) ^ 2) (Set.Ioi 0))
    (hint3 : MeasureTheory.IntegrableOn
      (fun z => c z * a α m c z * (w z) ^ 2) (Set.Ioi 0))
    (hint4 : MeasureTheory.IntegrableOn
      (fun z => (c z) ^ 2 * (w z) ^ 2) (Set.Ioi 0)) :
    (Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2) ^ 2
        * (∫ z in Set.Ioi 0, (a α m c z) ^ 2 * (w z) ^ 2)
      ≤ ∫ z in Set.Ioi 0, (c z) ^ 2 * (w z) ^ 2 := by
  -- the mode ODE, in the orientation of `modeWeightedEnergy_sq`
  have hode : ∀ z : ℝ, 0 < z →
      α ^ 2 * z ^ 2 * deriv (deriv (a α m c)) z + α * (5 + α) * z * deriv (a α m c) z
        = Work.FTS.PhiStar.Radial.lamR m * a α m c z - c z := by
    intro z hz
    have h := Work.FTS.PhiStar.Radial.radGreen_solves hα m hcont hg0 hg0' hginf z hz
    linarith
  have hac : ContinuousOn (a α m c) (Set.Ioi 0) := fun z hz =>
    (hderiv z hz).continuousAt.continuousWithinAt
  -- the two flux boundary conditions
  have hnear := radGreen_near_limits hα hα4 m hm hcont hvy hg0 hg0' hginf hderiv
  have hfar := radGreen_far_limits hα hα4 m hcont hdec hg0 hg0' hginf hderiv
  have hflux0 : ContinuousWithinAt (flux α (a α m c)) (Set.Ici 0) 0 :=
    flux_radGreen_zero m hnear.1 hnear.2
  have hfluxinf : Filter.Tendsto (flux α (a α m c)) Filter.atTop (nhds 0) :=
    flux_radGreen_atTop hα m hfar.1 hfar.2
  have hmu : 0 < Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2 := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    rw [Work.FTS.PhiStar.Radial.lamR]
    nlinarith [sq_nonneg α, hα.le, hα4, hm1]
  exact modeWeightedEnergy_sq (α := α) (lam := Work.FTS.PhiStar.Radial.lamR m) hα hac hderiv
    hderiv2 hode hint1 hint2 hint3 hint4 hflux0 hfluxinf hmu

end Work.FTS.ClassC
