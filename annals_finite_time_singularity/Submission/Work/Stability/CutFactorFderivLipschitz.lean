import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.Stability.Cutoff
import Submission.Work.Cyl.Frame

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The derivative of the cut-off factor is Lipschitz

The cut-off factor on `ℝ³` is `x ↦ chi (ρ x / L)`, where `ρ x = ‖x‖` (`Work.Cyl.rho`) and `chi` is
the `C^∞` bump of `Work.Stability.Cutoff` (equal to `1` on `[-1,1]` and to `0` off `(-2,2)`).

We prove `Work.Stability.CutFactorFderivLipschitz`: `fderiv ℝ (x ↦ chi (ρ x / L))` is Lipschitz.

The argument is the classical "smooth, compactly supported ⟹ the derivative is Lipschitz":
* `x ↦ chi (ρ x / L)` is `C^n` for every `n : ℕ` — near the origin it is identically `1`, and away
  from the origin it is the composition of the `C^∞` bump with the smooth `‖·‖/L`;
* it has compact support, contained in the ball of radius `2L` (it vanishes where `ρ ≥ 2L`);
* so `fderiv ℝ (·)` of it is again smooth (`ContDiff ℝ 1`) with compact support, and a `C^1`
  function with compact support is Lipschitz (`ContDiff.lipschitzWith_of_hasCompactSupport`).
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.Stability

set_option autoImplicit false

/-! ## Smoothness of the cut-off factor -/

/-- Away from the origin the cut-off factor `x ↦ chi (ρ x / L)` is the composition of the `C^∞`
bump `chi` with the smooth function `x ↦ ρ x / L = ‖x‖ / L`. -/
theorem cutFactorContDiffAt_ne_zero {L : ℝ} (n : ℕ) {x : Work.Cyl.R3} (hx : x ≠ 0) :
    ContDiffAt ℝ (n : WithTop ℕ∞)
      (fun y : Work.Cyl.R3 => Work.Stability.chi (Work.Cyl.rho y / L)) x := by
  have hchi : ContDiffAt ℝ (n : WithTop ℕ∞) Work.Stability.chi (Work.Cyl.rho x / L) :=
    Work.Stability.chi_contDiff.contDiffAt.of_le (by exact_mod_cast le_top)
  have hnorm : ContDiffAt ℝ (n : WithTop ℕ∞) (fun y : Work.Cyl.R3 => ‖y‖) x :=
    contDiffAt_norm ℝ hx
  have hdiv : ContDiffAt ℝ (n : WithTop ℕ∞) (fun y : Work.Cyl.R3 => ‖y‖ / L) x :=
    hnorm.div_const L
  have hden : ContDiffAt ℝ (n : WithTop ℕ∞) (fun y : Work.Cyl.R3 => Work.Cyl.rho y / L) x := by
    simpa only [Work.Cyl.rho_eq_norm] using hdiv
  -- NOTE (ChiExplicit repoint): see `CutFactorContDiff`: `Work.Stability.chi` now unfolds to a
  -- composition, so `g` and `f` are given explicitly.
  exact ContDiffAt.comp (g := Work.Stability.chi)
    (f := fun y : Work.Cyl.R3 => Work.Cyl.rho y / L) x hchi hden

/-- Near the origin the cut-off factor is identically `1` (`chi ≡ 1` on `[-1,1]` while
`ρ x / L → 0`), hence `C^n` there. -/
theorem cutFactorContDiffAt_zero {L : ℝ} (hL : 0 < L) (n : ℕ) :
    ContDiffAt ℝ (n : WithTop ℕ∞)
      (fun y : Work.Cyl.R3 => Work.Stability.chi (Work.Cyl.rho y / L)) 0 := by
  have hrho0 : Work.Cyl.rho (0 : Work.Cyl.R3) = 0 := by
    rw [Work.Cyl.rho_eq_norm]; simp
  have hcont : Continuous (fun y : Work.Cyl.R3 => Work.Cyl.rho y) := by
    rw [show (fun y : Work.Cyl.R3 => Work.Cyl.rho y) = fun y => ‖y‖ from
      funext Work.Cyl.rho_eq_norm]
    exact continuous_norm
  have htend : Tendsto (fun y : Work.Cyl.R3 => Work.Cyl.rho y) (𝓝 0) (𝓝 0) := by
    rw [← hrho0]; exact hcont.tendsto _
  have hev : (fun y : Work.Cyl.R3 => Work.Stability.chi (Work.Cyl.rho y / L))
      =ᶠ[𝓝 (0 : Work.Cyl.R3)] (fun _ => (1 : ℝ)) := by
    filter_upwards [htend.eventually (Iio_mem_nhds hL)] with y hy
    apply Work.Stability.chi_eq_one
    rw [abs_le]
    constructor
    · have : 0 ≤ Work.Cyl.rho y / L := div_nonneg (Work.Cyl.rho_nonneg y) hL.le
      linarith
    · rw [div_le_one hL]; exact le_of_lt hy
  exact contDiffAt_const.congr_of_eventuallyEq hev

/-- The cut-off factor `x ↦ chi (ρ x / L)` is `C^n` on all of `ℝ³`, for every `n : ℕ`. -/
theorem cutFactor_contDiff {L : ℝ} (hL : 0 < L) (n : ℕ) :
    ContDiff ℝ (n : WithTop ℕ∞)
      (fun x : Work.Cyl.R3 => Work.Stability.chi (Work.Cyl.rho x / L)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x 0 with hx | hx
  · rw [hx]; exact cutFactorContDiffAt_zero hL n
  · exact cutFactorContDiffAt_ne_zero n hx

/-! ## Compact support of the cut-off factor -/

/-- Off the ball of radius `2L` the cut-off factor vanishes, so its support is contained in the
closed ball of radius `2L` (`ρ = ‖·‖`). -/
theorem cutFactor_support_subset {L : ℝ} (hL : 0 < L) :
    Function.support (fun x : Work.Cyl.R3 => Work.Stability.chi (Work.Cyl.rho x / L)) ⊆
      Metric.closedBall (0 : Work.Cyl.R3) (2 * L) := by
  intro x hx
  rw [Function.mem_support] at hx
  rw [Metric.mem_closedBall, dist_zero_right, ← Work.Cyl.rho_eq_norm]
  by_contra h
  rw [not_le] at h
  have hzero : Work.Stability.chi (Work.Cyl.rho x / L) = 0 := by
    apply Work.Stability.chi_eq_zero
    rw [abs_of_nonneg (div_nonneg (Work.Cyl.rho_nonneg x) hL.le)]
    rw [le_div_iff₀ hL]
    linarith
  exact hx hzero

/-- The cut-off factor has compact support (its support lies in the compact ball of radius
`2L`). -/
theorem cutFactor_hasCompactSupport {L : ℝ} (hL : 0 < L) :
    HasCompactSupport (fun x : Work.Cyl.R3 => Work.Stability.chi (Work.Cyl.rho x / L)) :=
  HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Work.Cyl.R3) (2 * L)) (cutFactor_support_subset hL)

/-! ## The derivative is Lipschitz -/

/-- The derivative `fderiv ℝ (x ↦ chi(ρ(x)/L))` of the cut-off factor is Lipschitz: the cut-off
factor is `C^∞`, so its derivative is `C^1`; the derivative is supported in the ball of radius `2L`
(it vanishes where `ρ > 2L`), and being continuous with compact support its own derivative is
bounded. -/
theorem CutFactorFderivLipschitz {L : ℝ} (hL : 0 < L) :
    ∃ K : NNReal, LipschitzWith K
      (fderiv ℝ (fun x : Work.Cyl.R3 => Work.Stability.chi (Work.Cyl.rho x / L))) := by
  have hcs : HasCompactSupport
      (fun x : Work.Cyl.R3 => Work.Stability.chi (Work.Cyl.rho x / L)) :=
    cutFactor_hasCompactSupport hL
  have hcd : ContDiff ℝ (2 : WithTop ℕ∞)
      (fun x : Work.Cyl.R3 => Work.Stability.chi (Work.Cyl.rho x / L)) :=
    cutFactor_contDiff hL 2
  have hcs' : HasCompactSupport
      (fderiv ℝ (fun x : Work.Cyl.R3 => Work.Stability.chi (Work.Cyl.rho x / L))) :=
    hcs.fderiv ℝ
  have hcd' : ContDiff ℝ (1 : WithTop ℕ∞)
      (fderiv ℝ (fun x : Work.Cyl.R3 => Work.Stability.chi (Work.Cyl.rho x / L))) :=
    hcd.fderiv_right (by norm_num)
  exact ContDiff.lipschitzWith_of_hasCompactSupport hcs' hcd' (by norm_num)

end Work.Stability
