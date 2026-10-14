import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.CoreResiduals.BiotSavart.biotSavartSpaceTime_holds
import Submission.Work.FTS.Physical.BiotSavart.bsAdmissibleStripFull_comp_clock
import Submission.Work.FTS.Physical.BiotSavart.contDiffOn_uncurry_ico
import Submission.Work.FTS.Physical.BiotSavart.isOdd_physVel_of_swirlShape
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS_MuLamOK.Rows.rl0_final
import Submission.Work.SolutionDelivery.DatumOdd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Physical

open PhysClock

/-- **Joint `C^{1,α}` of the reconstructed velocity on a strip.**  This is the space-time
Schauder estimate of the workspace, read at the physical velocity. -/
theorem isContDiffHolderOn_physVel {α : ℝ≥0} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {ω : R3 → ℝ → R3} {R S : ℝ} (hS : 0 < S)
    (hbun : Work.CoreResiduals.BSAdmissibleStripFull α ω R S) :
    IsContDiffHolderOn ℝ α (physVel ω).uncurry (Set.univ ×ˢ Set.Icc (0 : ℝ) S) := by
  have h := (Work.CoreResiduals.BiotSavart.biotSavartSpaceTime_holds (α := α) hα hα1).2.2 ω R S hS hbun
  exact h



/-- **Oddness of the reconstructed velocity from the swirl shape of its vorticity.**  If the slice
`ω(·,t)` is the `(ρ,θ)`-swirl field `W(ρ(x),θ(x))·e_θ(x)` with `W` odd in the angle, then
`BS ω(·,t)` is odd.  This is the form in which the physical vorticity of the fake-time profile is
known to be symmetric. -/
theorem isOdd_physVel_of_swirlShape {W : ℝ → ℝ → ℝ} {ω : R3 → ℝ → R3} {t : ℝ}
    (hshape : ∀ x : R3, ω x t = W (Work.Cyl.rho x) (Work.Cyl.theta x) • Work.Cyl.eTheta x)
    (hW : ∀ ρ θ : ℝ, W ρ (-θ) = - W ρ θ) :
    IsOdd ((physVel ω) · t) :=
  Work.FTS.Physical.BiotSavart.isOdd_physVel_of_swirlShape hshape hW

/-- **The `L^∞`-norm of the vorticity is the sup-norm of the physical vorticity.**  An immediate
consequence of the identification `∇×(BS ω(·,t)) = ω(·,t)` of the Biot–Savart law; it is what makes
the pointwise profile bound produce `BlowupAt.lower`. -/
theorem vortLInf_physVel_eq {ω : R3 → ℝ → R3} {T : ℝ}
    (h : ∀ t ∈ Set.Ico 0 T, ∀ x : R3, vorticity (fun y => physVel ω y t) x = ω x t)
    {t : ℝ} (ht : t ∈ Set.Ico 0 T) :
    Work.LWP.vortLInf (physVel ω) t = ⨆ x, ‖ω x t‖ := by
  unfold Work.LWP.vortLInf
  exact iSup_congr (fun x => by rw [h t ht x])

/-- **Transport of an admissible strip bundle along a clock.**  The strip bundle of the
space-time Schauder estimate is preserved by a reparametrisation `ωc x t = ω x (τ t)` along a
differentiable Lipschitz clock `τ` whose derivative is bounded and `α`-Hölder: this is what
carries node N7's fake-time bundle (`Work.FTS.Regularity.physVort_bundle`) to the physical-time
bundle consumed by `blowupAt_of_physical`. -/
theorem bsAdmissibleStripFull_comp_clock {α : NNReal} {ω : R3 → ℝ → R3} {R S T : ℝ}
    (hS : 0 < S) (hT : 0 < T) (hbun : Work.CoreResiduals.BSAdmissibleStripFull α ω R S)
    {tau d : ℝ → ℝ}
    (hmem : ∀ t ∈ Set.Icc (0 : ℝ) T, tau t ∈ Set.Icc (0 : ℝ) S)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt tau (d t) t)
    (hlip : ∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ t' ∈ Set.Icc (0 : ℝ) T,
      |tau t - tau t'| ≤ L * |t - t'|)
    (hdbdd : ∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, |d t| ≤ L)
    (hdholder : ∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ t' ∈ Set.Icc (0 : ℝ) T,
      |d t - d t'| ≤ L * |t - t'| ^ ((α : NNReal) : ℝ)) :
    Work.CoreResiduals.BSAdmissibleStripFull α (fun x t => ω x (tau t)) R T :=
  Work.FTS.Physical.BiotSavart.bsAdmissibleStripFull_comp_clock hS hT hbun hmem hderiv hlip hdbdd
    hdholder

/-- **The decay clause of the initial datum for compactly supported bounded vorticity.**  This is
the only place where the compact support of the constructed vorticity is used for the decay clause
of the challenge statement: `‖ω x‖ ≤ C (‖x‖^α + 1)^{-1}` is trivial away from the support. -/
theorem vorticityDecay_of_support {α : ℝ≥0} {ω : R3 → R3} {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hsupp : ∀ x : R3, ω x ≠ 0 → x ∈ Metric.closedBall 0 R) (hbdd : ∀ x : R3, ‖ω x‖ ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : R3, ‖ω x‖ ≤ C / (‖x‖ ^ (α : ℝ) + 1) :=
  Work.FTS.Physical.BiotSavart.vorticityDecay_of_support hR hM hsupp hbdd

end Work.FTS.Physical
