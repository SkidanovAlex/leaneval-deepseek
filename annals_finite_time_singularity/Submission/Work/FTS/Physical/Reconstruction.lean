/-
# `Work.FTS.Physical.Reconstruction` — the physical reconstruction theorem (node N8)

This is the assembly node of the physical reconstruction: from the data of the *dynamically
rescaled* solution of the paper's fake-time equation one produces a genuine solution of the
incompressible Euler equation on `ℝ³` with a finite-time blow-up, in the shape of the `BlowupAt`
interface that the top-level wiring (node N0) consumes.

## The inputs

The fake-time dynamic solution is delivered upstream as

* the physical vorticity `ω` (the rescaled profile, `Physical/Profile.lean`), compactly supported
  in a fixed ball, together with the strip bundle `BSAdmissibleStripFull α ω R S` of the regularity
  transfer (node N7);
* the Biot–Savart law `∇×(BS ω(·,t)) = ω(·,t)`, `div (BS ω(·,t)) = 0` (the identification step of
  the reconstruction, whose uniqueness half is `Physical/Liouville.lean`);
* the parity/axisymmetry data giving the oddness of `BS ω` (`Physical/BiotSavart.lean`);
* the vorticity equation in physical variables, transferred from the fake-time equation by the
  chain rule along the clock;
* the profile lower bound `‖ω(·,t)‖_∞ ≥ c/(T-t)` (`Physical/LowerBound.lean`);
* the pressure, from the elliptic input `Work.LWP.PressureReconstruction α` of the LWP chapter.

## The conclusions

* `BlowupAt α T`: the Euler solution on `[0,T)`, odd at every time, jointly `C^{1,α}` on the
  strips, with the datum's decay clause — the reconstruction result proper;
* `blowupAt_of_profile`: the same with the vorticity presented by the explicit fake-time profile,
  the clock and RegPkg data entering through the hypotheses of `Physical/Profile.lean`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.Physical.Defs
import Submission.Work.FTS.Physical.BiotSavart
import Submission.Work.FTS.Physical.LowerBound
import Submission.Work.LWP.Inputs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Physical

/-- **The physical reconstruction theorem.**  From the physical vorticity `ω` of the dynamically
rescaled solution, the Biot–Savart law, the parity data, the physical vorticity equation, the
`C^{1,α}` regularity bundle and the profile lower bound, the velocity `BS ω` and a pressure are a
finite-time blow-up in the sense of `BlowupAt α T`.

The velocity is `u = physVel ω = BS ω(·,t)`; the pressure is produced by the Poincaré lemma from
the vorticity equation through `Work.LWP.PressureReconstruction α` (the elliptic input of the LWP
chapter: for `C^{1,α}` fields the product `(∇u)·u` is not differentiable, so `p` is obtained as the
Schauder solution of `-Δp = div((u·∇)u)`). -/
noncomputable def blowupAt_of_physical {α : ℝ≥0} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {ω : R3 → ℝ → R3} {R T : ℝ} (hT : 0 < T) (hR : 0 < R)
    (hsupp : ∀ t ∈ Set.Ico 0 T, ∀ x : R3, ω x t ≠ 0 → x ∈ Metric.closedBall 0 R)
    (hbun : ∀ S ∈ Set.Ioo 0 T, Work.CoreResiduals.BSAdmissibleStripFull α ω R S)
    (hcurl : ∀ t ∈ Set.Ico 0 T, ∀ x : R3,
      vorticity (fun y => physVel ω y t) x = ω x t)
    (hdivu : ∀ t ∈ Set.Ico 0 T, div (fun y => physVel ω y t) = 0)
    (hodd : ∀ t ∈ Set.Ico 0 T, IsOdd ((physVel ω) · t))
    (hvort : Work.LWP.VorticityEquation (physVel ω) ω)
    (hcd0 : IsContDiffHolder ℝ α ((physVel ω) · 0))
    (hpress : Work.LWP.PressureReconstruction α)
    (hlow : ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico 0 T, c / (T - t) ≤ ⨆ x, ‖ω x t‖) :
    BlowupAt α T := by
  -- the `C^{1,α}` strips of the reconstructed velocity
  have hstrip : ∀ S ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α (physVel ω).uncurry
      (Set.univ ×ˢ Set.Icc (0 : ℝ) S) :=
    fun S hS => isContDiffHolderOn_physVel hα hα1 hS.1 (hbun S hS)
  -- the pressure, from the vorticity equation
  -- (`BlowupAt` is data, not a proposition, so the existential of `PressureReconstruction` is
  --  eliminated with `Classical.choose` rather than with `obtain`)
  have hex := hpress (physVel ω) ω T hstrip hcurl hdivu hvort
  -- the decay clause of the datum, from the uniform support and bound of the bundle
  have hdecay : ∃ C : ℝ, 0 < C ∧ ∀ x : R3,
      ‖vorticity ((physVel ω) · 0) x‖ ≤ C / (‖x‖ ^ (α : ℝ) + 1) := by
    obtain ⟨M, hM⟩ := (hbun (T / 2) ⟨by linarith, by linarith⟩).1.2.2.1
    have hM0 : 0 ≤ M := le_trans (norm_nonneg _)
      (hM 0 (Set.mem_Icc.mpr ⟨le_rfl, by linarith⟩) 0)
    refine vorticityDecay_of_support (α := α) (R := R) (M := M) hR.le hM0 ?_ ?_
    · intro x hx
      rw [hcurl 0 ⟨le_rfl, hT⟩ x] at hx
      exact hsupp 0 ⟨le_rfl, hT⟩ x hx
    · intro x
      rw [hcurl 0 ⟨le_rfl, hT⟩ x]
      exact hM 0 (Set.mem_Icc.mpr ⟨le_rfl, by linarith⟩) x
  refine ⟨physVel ω, hex.choose, hT,
    ⟨contDiffOn_uncurry_ico hα hα1 hT hbun, hex.choose_spec.1, hex.choose_spec.2,
      fun t ht => hdivu t ⟨ht.1.le, ht.2⟩, rfl⟩,
    hdivu 0 ⟨le_rfl, hT⟩, hodd, hcd0, hdecay, hstrip, ?_⟩
  obtain ⟨c, hc, hcl⟩ := hlow
  exact ⟨c, hc, fun t ht => by rw [vortLInf_physVel_eq hcurl ht]; exact hcl t ht⟩

end Work.FTS.Physical
