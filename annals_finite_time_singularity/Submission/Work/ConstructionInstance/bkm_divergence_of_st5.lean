/-
# `Work.ConstructionInstance.bkm_divergence_of_st5` — the quantitative half of `St5`

This module closes the *quantitative* half of the maximality residual `SelfSimMaximal` of
`Work.ConstructionInstance.Tie`: for the self-similar ansatz velocity
`ansatzV P = BS(solVort P · )` (`Tie.ansatzV`), the Beale–Kato–Majda integral diverges at the
blow-up time,

  `bkm (ansatzV P) t = ∫₀ᵗ ⨆ₓ ‖∇×(ansatzV P · s) x‖ ds  ⟶  +∞   (t → T⁻)`.

## How the statement is assembled from the delivered chapters

`Work.StabilityFar.bkm_divergence_of_vortLinfLower` (`St5`) needs exactly two inputs at the level
of the ansatz: the pointwise `1/(T-t)` lower bound on the vorticity sup-norm, and the
interval-integrability of `t ↦ ‖ω(·,t)‖_∞` up to `t < T`.  Both are supplied here, from the
*definitional* data of `ProfileData` and the Biot–Savart law `hlaw` alone:

* **the lower bound** (`ansatzV_vortLinfLower`): by `hlaw`, the vorticity of the ansatz is the
  constructed field, `∇×(ansatzV P · t) = solVort P · t` (`vorticity_ansatzV`); the modulation
  bound `λ̄(t) ≤ 2(T-t)` and the *self-similar* lower bound `c₀α ≤ λ̄(t)‖ω(x,t)‖` at some point
  (`Reduced.solVort_hansatz`, whose witness is the profile scale `z = 1` with the cut-off
  transparent there) turn it into `VortLinfLower (ansatzV P) T (c₀α/2)` through
  `Work.StabilityFar.vortLinfLower_of_ansatz` — the same reduction that
  `Work.SolutionDelivery.BKM` performs for the delivered `ConstructedSolution`;
* **the integrability** (`intervalIntegrable_vortLInf_ansatzV`): `t ↦ ⨆ₓ ‖ω(x,t)‖` is
  *continuous* on every strip `[0,S]`, `S < T`, because the slices are supported in the fixed ball
  `B(0,R)` (`Reduced.solVort_supp`) and bounded there (`Reduced.solVort_bdd`), so the full-space
  supremum is the supremum over a compact ball of a jointly continuous family
  (`Reduced.solVort_cont` + `Work.SolutionDelivery.Sup.ciSup_norm_vorticity_eq_ciSup_closedBall` +
  `Work.SolutionDelivery.Sup.continuousOn_ciSup_closedBall`).

The remaining half of maximality (the Beale–Kato–Majda *continuation* input `Work.LWP.BKMExtension`
turning this divergence into non-extendability) is the LWP chapter's, and is not used here.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.ConstructionInstance.Tie
import Submission.Work.ConstructionInstance.Reduced
import Submission.Work.StabilityFar.St5
import Submission.Work.SolutionDelivery.BKM
import Submission.Work.SolutionDelivery.Sup.ciSup_norm_vorticity_eq_ciSup_closedBall
import Submission.Work.SolutionDelivery.Sup.continuousOn_ciSup_closedBall
import Submission.Work.LWP.Inputs
import Submission.Work.ConstructionInstance.intervalIntegrable_vortLInf_ansatzV

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-- **The Biot–Savart identity for the ansatz, on the physical interval.**  On `[0,T)` the
vorticity of the ansatz velocity is the constructed self-similar field `solVort P` (this is
`Tie.vorticity_ansatzV` transported from the window `preWindow T = (-2,T)` to `[0,T)`). -/
theorem vorticity_ansatzV_Ico {α : NNReal} (P : ProfileData α) (hlaw : Work.LWP.BiotSavartLaw) :
    ∀ t ∈ Set.Ico 0 P.T, ∀ x : R3,
      vorticity (fun y => ansatzV P y t) x = solVort P x t :=
  fun t ht x => vorticity_ansatzV P hlaw t ⟨by linarith [ht.1], ht.2⟩ x

/-- **The `St5` lower bound for the ansatz**: `‖ω(·,t)‖_∞ ≥ (c₀α/2)/(T-t)` on `[0,T)`, where
`c₀ = c₀star α` is the explicit profile constant (`ProfileData.c₀star`).

The point where the vorticity is large is the `St5` witness of `Reduced.solVort_hansatz`
(the maximising profile scale `z = 1`, where the cut-off is transparent because
`λ̄(t)^{1/p} ≤ (2T)^{1/p} ≤ L`); the two remaining ingredients are the two-sided modulation bound
`λ̄(t) ≤ 2(T-t)` (`ProfileData.hlam_le`) and the positivity of `λ̄` on the window
(`ProfileData.hlam`). -/
theorem ansatzV_vortLinfLower {α : NNReal} (P : ProfileData α) (hlaw : Work.LWP.BiotSavartLaw) :
    Work.StabilityFar.VortLinfLower (ansatzV P) P.T (c₀star α * (α : ℝ) / 2) := by
  have hα : 0 < (α : ℝ) := P.hα
  have hc₀ : 0 < c₀star α := c₀star_pos P.hα P.hα13
  have hvort := vorticity_ansatzV_Ico P hlaw
  refine Work.StabilityFar.vortLinfLower_of_ansatz (u := ansatzV P) (T := P.T)
    (c₀ := c₀star α) (α := (α : ℝ)) (lam := P.lam) ?_ ?_ hc₀ hα ?_ ?_
  · -- `λ̄ > 0` on `[0,T)`
    intro t ht
    exact P.hlam t ⟨by linarith [ht.1], ht.2⟩
  · -- `λ̄(t) ≤ 2(T-t)` on `[0,T)`
    intro t ht
    exact P.hlam_le t ht
  · -- the slice sup is honest: bounded by `M/λ̄(t)`
    intro t ht
    refine ⟨P.M / P.lam t, ?_⟩
    rintro _ ⟨x, rfl⟩
    change ‖vorticity (fun y => ansatzV P y t) x‖ ≤ P.M / P.lam t
    rw [hvort t ht x]
    have hlt : 0 < P.lam t := P.hlam t ⟨by linarith [ht.1], ht.2⟩
    exact (le_div_iff₀ hlt).mpr
      (by rw [mul_comm]; exact solVort_bdd P t ⟨by linarith [ht.1], ht.2⟩ x)
  · -- the pointwise lower bound: the `St5` witness of the construction
    intro t ht
    obtain ⟨x, hx⟩ := solVort_hansatz P t ht
    exact ⟨x, by rwa [hvort t ht x]⟩

/-- **The quantitative half of the maximality residual**: the BKM integral of the self-similar
ansatz diverges as `t → T⁻`.

This is `St5` (`Work.StabilityFar.bkm_divergence_of_vortLinfLower`) applied to the two inputs
derived from the profile data and the Biot–Savart law: the pointwise lower bound
`ansatzV_vortLinfLower` and the interval-integrability of `t ↦ ‖ω(·,t)‖_∞`
(`intervalIntegrable_vortLInf_ansatzV`, from the continuity of that function on the strips). -/
theorem bkm_divergence_of_st5 {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (hlaw : Work.LWP.BiotSavartLaw) :
    Filter.Tendsto (Work.LWP.bkm (Work.ConstructionInstance.ansatzV P))
      (nhdsWithin P.T (Set.Iio P.T)) Filter.atTop := by
  have hc : 0 < c₀star α * (α : ℝ) / 2 := by
    have h1 : 0 < c₀star α := c₀star_pos P.hα P.hα13
    have h2 : 0 < (α : ℝ) := P.hα
    positivity
  exact Work.StabilityFar.bkm_divergence_of_vortLinfLower P.hT hc
    (ansatzV_vortLinfLower P hlaw) (intervalIntegrable_vortLInf_ansatzV P hlaw)

end Work.ConstructionInstance
