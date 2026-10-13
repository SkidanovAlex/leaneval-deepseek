/-
# `Work.CoreResiduals.Reductions` — the routing: each residual from its owner chapter's input

This module makes the routing of `NOTES.md` §3.4 formal:

* **R3** (`VortSmooth P`, `C¹` of the ansatz velocity on the two-sided window) follows from the
  general *space-time Calderón–Zygmund* input `BiotSavartSpacetimeC1` applied to the explicit field
  `solVort P`, provided that field satisfies the admissibility bundle `BSAdmissibleOnWindow`
  (support, local boundedness, local `x`-Hölder regularity, local `t`-differentiability with
  locally bounded derivative and measurable slices);
* **R2** (`LGClass α P`, the spacetime Lichtenstein–Gunther class) follows from the general
  *space-time Schauder* input `BiotSavartSpaceTime α`, provided the explicit field satisfies the
  strip bundle `BSAdmissibleStrip` (uniform boundedness, uniform `x`-Hölder and time-Hölder on the
  strip) — see `BiotSavart.solVort_BSAdmissibleStrip`;
* **R4** (`TimeHolderDeriv P`) is *equivalent* to second-order profile/modulation data
  (`timeHolderDeriv_of_secondOrderData`, re-exported here in the vocabulary of this area);
* **R1** (`VortEq α P`) is the zero-deficit case of the corrected equation
  `VortEqWithDeficit α P Def` (`vortEq_iff_noDeficit`); the honest equation for the *cut* field
  carries the cut-off deficit `Def` (`Work.Stability.Far`), and `Model.fstar_rate_rigid` shows that
  at the delivered inhabitant the deficit cannot vanish (`NOTES.md` §findings).

Nothing here is conditional on unproved mathematics beyond the two named inputs, which are stated
in `Defs.lean` as the precise residual of R2 and R3. -/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.Defs
import Submission.Work.CoreResiduals.Model
import Submission.Work.CoreResiduals.TimeHolderDeriv
import Submission.Work.CoreResiduals.BiotSavart.biotSavart_contDiffOn_far
import Submission.Work.CoreResiduals.solVort_BSAdmissibleStrip
import Submission.Work.CoreResiduals.solVort_timeDerivStrip
import Submission.Work.CoreResiduals.timeDerivStripHolder_of_locallyLipschitz
import Submission.Work.ConstructionInstance.solVort_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.CoreResiduals

/-! ## R3 -/

/-- **R3 from the space-time `C¹` input.**  Applying the general Biot–Savart regularity statement
`BiotSavartSpacetimeC1` to the explicit field `solVort P` gives `C¹` of the ansatz velocity at
every point of the two-sided window. -/
theorem vortSmooth_of_spacetimeC1 {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (h : BiotSavartSpacetimeC1) (hadm : BSAdmissibleOnWindow (solVort P) P.R P.T)
    (hlip : TimeDerivLocallyLipschitz (solVort P) P.T) :
    VortSmooth P := by
  intro q hq
  change ContDiffWithinAt ℝ 1
    (fun q : R3 × ℝ => Work.LWP.biotSavart (fun y => Work.ConstructionInstance.solVort P y q.2) q.1)
    (Set.univ ×ˢ Work.ConstructionInstance.preWindow P.T) q
  exact (h (Work.ConstructionInstance.solVort P) P.R P.T hadm hlip q.1 q.2 hq.2).contDiffWithinAt

/-- **R3 at the model data**, from the space-time `C¹` input and the admissibility bundle of the
explicit field. -/
theorem vortSmoothModel_of_spacetimeC1 {α : NNReal} (h : BiotSavartSpacetimeC1)
    (hadm : ∃ I : Inhabitant α, BSAdmissibleOnWindow (solVort I.P) I.P.R I.P.T ∧
      TimeDerivLocallyLipschitz (solVort I.P) I.P.T) :
    VortSmoothModel α := by
  obtain ⟨I, hI, hlip⟩ := hadm
  exact ⟨I.P, inhabitant_isModelData I, vortSmooth_of_spacetimeC1 I.P h hI hlip⟩

/-! ## R3: the far-field half, unconditionally

Outside the support ball there is no singularity in the Biot–Savart integral, so the `C¹` clause of
R3 holds *for real* on `{x | 2R < ‖x‖}`, with no hypothesis beyond the profile data. -/

/-- **The far-field half of R3, proved**: on every time slice `t` of the half-window, the ansatz
velocity is `C¹` outside `B(0, 2R)`. -/
theorem ansatzV_contDiffOn_far {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    {t : ℝ} (ht : t ∈ Work.ConstructionInstance.preWindow P.T) :
    ContDiffOn ℝ 1 (fun x : R3 => Work.ConstructionInstance.ansatzV P x t)
      {x : R3 | 2 * P.R < ‖x‖} := by
  have hlt : 0 < P.lam t := P.hlam t ht
  have hR : 0 < P.R := lt_of_lt_of_le (by linarith [P.hL]) P.hRbig
  have hM : 0 ≤ P.M / P.lam t := div_nonneg P.hM hlt.le
  have hbdd : ∀ a : R3, ‖Work.ConstructionInstance.solVort P a t‖ ≤ P.M / P.lam t := by
    intro a
    rw [le_div_iff₀ hlt, mul_comm]
    exact Work.ConstructionInstance.solVort_bdd P t ht a
  have hsupp : ∀ a : R3, Work.ConstructionInstance.solVort P a t ≠ 0 →
      a ∈ Metric.closedBall 0 P.R :=
    fun a ha => Work.ConstructionInstance.solVort_supp P t a ha
  have hm : MeasureTheory.AEStronglyMeasurable
      (fun a : R3 => Work.ConstructionInstance.solVort P a t) MeasureTheory.volume :=
    (Work.ConstructionInstance.solVort_integrable P t ht).aestronglyMeasurable
  have h := Work.CoreResiduals.BiotSavart.biotSavart_contDiffOn_far
    (ω := fun a : R3 => Work.ConstructionInstance.solVort P a t) hR hM hbdd hsupp hm
  simpa [Work.ConstructionInstance.ansatzV] using h

/-! ## R2 -/

/-- **The full strip bundle of R2 for the explicit field**: the strip admissibility
(`solVort_BSAdmissibleStrip`), the time-regularity (`solVort_timeDerivStrip`) and the second-order
time-regularity of `∂ₜω` (`timeDerivStripHolder_of_locallyLipschitz`, which turns the local
Lipschitzness of `∂ₜω` — R3's second-order condition — into the strip form; for the model data it
is also the content of R4, `TimeHolderDeriv`).  This is the hypothesis of `BiotSavartSpaceTime α`. -/
theorem solVort_BSAdmissibleStripFull {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (hlip : TimeDerivLocallyLipschitz (solVort P) P.T)
    {S : ℝ} (hS : 0 < S) (hST : S < P.T) :
    BSAdmissibleStripFull α (solVort P) P.R S :=
  ⟨solVort_BSAdmissibleStrip P hS hST, solVort_timeDerivStrip P hS hST,
    timeDerivStripHolder_of_locallyLipschitz P hlip hS hST⟩


/-- **R2 from the space-time Schauder input.** -/
theorem lgClass_of_spaceTime {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (h : BiotSavartSpaceTime α)
    (hadm : ∀ S : ℝ, 0 < S → S < P.T → BSAdmissibleStripFull α (solVort P) P.R S) :
    LGClass α P := by
  intro S hS
  exact h.2.2 (Work.ConstructionInstance.solVort P) P.R S hS.1 (hadm S hS.1 hS.2)

/-- **R2 at the model data**, from the space-time Schauder input and the strip bundle of the
explicit field. -/
theorem lgClassModel_of_spaceTime {α : NNReal} (h : BiotSavartSpaceTime α)
    (hadm : ∃ I : Inhabitant α,
      ∀ S : ℝ, 0 < S → S < I.P.T → BSAdmissibleStripFull α (solVort I.P) I.P.R S) :
    LGClassModel α := by
  obtain ⟨I, hI⟩ := hadm
  exact ⟨I.P, inhabitant_isModelData I, lgClass_of_spaceTime I.P h hI⟩

/-! ## R4 -/

/-- **R4 from second-order data** (finding H, re-exported in the vocabulary of this area):
the time-Hölder regularity of `∂ₜω` on the strips follows from the second `z`-differentiability of
the profile with the weighted bound `|z²∂_z²F| ≤ Cg''`, and the second differentiability of the
modulation with `|λ̄''| ≤ K₂`. -/
theorem timeHolderDeriv_of_secondOrderData {α : NNReal}
    (P : Work.ConstructionInstance.ProfileData α)
    (hgdiff2 : ∀ z θ : ℝ, 0 < z → HasDerivAt
      (fun z' : ℝ => Work.Spaces.pz
        (Work.ConstructionInstance.profile (Work.ConstructionInstance.profExp α) P.g) z' θ)
      (Work.Spaces.pz (Work.Spaces.pz
        (Work.ConstructionInstance.profile (Work.ConstructionInstance.profExp α) P.g)) z θ) z)
    {Cg'' K₂ : ℝ}
    (hg3 : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |z ^ 2 * Work.Spaces.pz (Work.Spaces.pz
        (Work.ConstructionInstance.profile (Work.ConstructionInstance.profExp α) P.g)) z θ| ≤ Cg'')
    (hlamdif2 : ∀ t ∈ Work.ConstructionInstance.preWindow P.T,
      HasDerivAt (deriv P.lam) (deriv (deriv P.lam) t) t)
    (hlamd2 : ∀ t ∈ Work.ConstructionInstance.preWindow P.T,
      |deriv (deriv P.lam) t| ≤ K₂) :
    TimeHolderDeriv P :=
  Work.ConstructionInstance.selfSimTimeHolderDeriv_of_secondOrderData P hgdiff2 hg3 hlamdif2 hlamd2

/-! ## R1 -/

/-- **R1 in its corrected form.**  The delivered residual is the zero-deficit case of the equation
with the cut-off deficit (`vortEq_iff_noDeficit`); the honest form for the *cut* ansatz of the
construction carries the deficit `Work.Stability.Far` of `Work.Stability.GEquationFar`
(`NOTES.md` §findings records the two obstructions to the zero-deficit form at the delivered
inhabitant: the cut-off is not transparent on the support, and the model's rate `κ = 1/2` is not
the reference rate `κ* = 1` of the profile `F_*`). -/
theorem vortEq_of_noDeficit {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (h : VortEqWithDeficit P (fun _ _ => 0)) : VortEq α P :=
  (vortEq_iff_noDeficit P).mpr h

end Work.CoreResiduals
