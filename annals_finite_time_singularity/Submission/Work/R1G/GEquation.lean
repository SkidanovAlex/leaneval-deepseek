/-
# `Work.R1G.GEquation` — the promotion of the `g`-equation to the profile equation

Deliverable 1 of the G-route: the **modulated profile data**.  Its content is that the `St2`/`St3`
`g`-equation `Work.Stability.GEquationFar` — whose right-hand side `gDynRHS` is *explicit* — is
exactly the *profile equation at the effective rate* for the full profile `F = F_* + g`, i.e. the
promotion of the Construction area's **reduced** identity
`Work.Construction.Fstar_stationary_identity`
(`F_* + D_zF_* - (1/α)L₁₂(F_*)F_* = 0`) to the full equation
`2κ(F + D_zF) + UVR p F Φ = 0`.

The engine is `Work.R1G.profileResid_eq_gEqResidual` (the `gDynRHS` identification, delegated in
this directory): the profile residual and the `g`-equation residual are *the same function*.  With
it, everything the G-route needs about the modulation is a rewriting:
`GEquationStat ⟺ ProfileEq` (at zero deficit), and — by `Work.R1G.Meridian` — the uncut
self-similar pair solves the meridian equation.

## Main statements

* `Work.R1G.profileResid_eq_far_of_gEquationStat` — the profile residual of the delivered data at
  the effective rate is the `g`-equation's far-field term;
* `Work.R1G.profileEq_of_gEquationStat` — **the promotion**, at zero deficit;
* `Work.R1G.ModulatedData.profileResid_eq_far`,
  `Work.R1G.ModulatedData.profileEq_of_far_zero` — the same at a `ModulatedData`;
* `Work.R1G.ModulatedData.meridianResid_cut_eq` — the deficit cancellation in meridian form.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.R1G.Defs
import Submission.Work.R1G.profileResid_eq_gEqResidual_qd
import Submission.Work.R1G.Meridian
import Submission.Work.R1G.CutDeficit

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

/-! ## The `gDynRHS` identification, and the promotion -/

/-- **The profile residual is the `g`-equation's far-field term.**  At the delivered data, with the
derivation bundle `GDerivData`, the profile equation at the effective rate holds *up to* exactly the
`Far` of `Work.Stability.GEquationFar`. -/
theorem profileResid_eq_far_of_gEquationStat (P : Work.ConstructionInstance.ProfileData α)
    {κ : ℝ} {Φ Far : ℝ → ℝ → ℝ}
    (hD : GDerivDataQd (Work.ConstructionInstance.profExp α) (gOf3 P) (phiOf3 Φ))
    (hG : GEquationStat P κ Φ Far) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → profileResid P κ Φ z θ = Far z θ := by
  intro z θ hzθ
  rw [profileResid_eq_gEqResidual_qd P κ Φ hD hzθ,
    (gEquationStat_iff P κ Φ Far).mp hG z θ hzθ]

/-- **THE PROMOTION.**  At zero deficit the `g`-equation of the delivered data is *exactly* the
profile equation at the effective rate: the Construction area's reduced identity
`Work.Construction.Fstar_stationary_identity` promoted through the `St2`/`St3` modulation content
(the `(F,K)`-terms and the `N₀`, `N`, `N_*` nonlinearities, all collected by the explicit
`Work.Stability.gDynRHS`). -/
theorem profileEq_of_gEquationStat (P : Work.ConstructionInstance.ProfileData α) {κ : ℝ}
    {Φ : ℝ → ℝ → ℝ}
    (hD : GDerivDataQd (Work.ConstructionInstance.profExp α) (gOf3 P) (phiOf3 Φ))
    (hG : GEquationStat P κ Φ (fun _ _ => 0)) : ProfileEq P κ Φ := by
  rw [profileEq_iff]
  intro z θ hzθ
  rw [profileResid_eq_far_of_gEquationStat P hD hG z θ hzθ]

/-- The profile equation at the effective rate is *equivalent* to the zero-deficit `g`-equation
(with the derivation bundle): the equivalence direction `⟹` is
`Work.Stability.DynGEquation` composed with the promotion, and `⟸` is the promotion itself. -/
theorem gEquationStat_zero_iff_profileEq (P : Work.ConstructionInstance.ProfileData α) {κ : ℝ}
    {Φ : ℝ → ℝ → ℝ}
    (hD : GDerivDataQd (Work.ConstructionInstance.profExp α) (gOf3 P) (phiOf3 Φ)) :
    GEquationStat P κ Φ (fun _ _ => 0) ↔ ProfileEq P κ Φ := by
  constructor
  · exact profileEq_of_gEquationStat P hD
  · intro h
    rw [gEquationStat_iff]
    intro z θ hzθ
    rw [← profileResid_eq_gEqResidual_qd P κ Φ hD hzθ, (profileEq_iff P κ Φ).mp h z θ hzθ]

/-! ## At a `ModulatedData` -/

/-- The profile residual of a `ModulatedData` at the effective rate is its far-field term. -/
theorem ModulatedData.profileResid_eq_far (D : ModulatedData α) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      profileResid D.P D.κ D.Φ z θ = D.Far z θ :=
  profileResid_eq_far_of_gEquationStat D.P D.hD D.hFar

/-- **The modulated data satisfies the profile equation at the effective rate** as soon as its
`g`-equation has vanishing far-field term — i.e. the honest modulation `g ≠ 0` cancels the profile
residual, which is the whole point of the modulation (for `g = 0` the reduced identity
`Fstar_stationary_identity` does *not* promote). -/
theorem ModulatedData.profileEq_of_far_zero (D : ModulatedData α)
    (hFar : ∀ z θ : ℝ, D.Far z θ = 0) : ProfileEq D.P D.κ D.Φ :=
  profileEq_of_gEquationStat D.P D.hD
    ((gEquationStat_iff D.P D.κ D.Φ (fun _ _ => 0)).mpr
      (fun z θ hzθ => by rw [D.gEqResidual_eq_far z θ hzθ, hFar z θ]))

/-- **The uncut self-similar pair of a `ModulatedData` solves the meridian equation** in the
physical window, once the modulation's far-field term vanishes. -/
theorem ModulatedData.meridianResid_eq_zero (D : ModulatedData α)
    (hΦ : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      ContDiffAt ℝ 2 (fun q : ℝ × ℝ => D.Φ q.1 q.2) (z, θ))
    (hF : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      ContDiffAt ℝ 1 (fun q : ℝ × ℝ => profOf D.P q.1 q.2) (z, θ))
    (hFar : ∀ z θ : ℝ, D.Far z θ = 0) :
    ∀ r z t : ℝ, 0 < r → 0 < z → t ∈ Set.Ioo 0 D.P.T →
      Work.CoreResiduals.meridianResid (ssVortOf D.P) (ssPsiOf D.P D.Φ) r z t = 0 :=
  meridianResid_ssVortOf_eq_zero D.P D.hrate hΦ hF (D.profileEq_of_far_zero hFar)

/-! ## The deficit cancellation in meridian form -/

/-- **THE DEFICIT CANCELLATION.**  At a `ModulatedData` whose `g`-equation has far-field term `Far`,
the meridian residual of the **construct ed (cut)** field `χ(ρ/L)·ssVort` against the self-similar
stream function is the sum of

* the (cut-off-weighted) image of the profile-level `g`-equation deficit `Far`, and
* the explicit, local cut-off term `cutDeficit P ψ W`;

so the `g`-equation cancels the *entire* self-similar (profile) part of the residual, and the only
leftover is the explicit cut-off term.  This is residual R1 in meridian form. -/
theorem ModulatedData.meridianResid_cut_eq (D : ModulatedData α)
    (hΦ : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      ContDiffAt ℝ 2 (fun q : ℝ × ℝ => D.Φ q.1 q.2) (z, θ))
    (hF : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      ContDiffAt ℝ 1 (fun q : ℝ × ℝ => profOf D.P q.1 q.2) (z, θ)) :
    ∀ r z t : ℝ, 0 < r → 0 < z → t ∈ Set.Ioo 0 D.P.T →
      Work.CoreResiduals.meridianResid
          (fun r z t => Work.Stability.chi (Work.Cyl.rhoP r z / D.P.L)
            * ssVortOf D.P r z t)
          (ssPsiOf D.P D.Φ) r z t
        = Work.Stability.chi (Work.Cyl.rhoP r z / D.P.L)
            * ((2 * (D.P.lam t) ^ 2)⁻¹ *
                D.Far (Work.Cyl.rhoP r z ^ Work.ConstructionInstance.profExp α / D.P.lam t)
                  (Work.Cyl.thetaP r z))
          + cutDeficit D.P (ssPsiOf D.P D.Φ) (ssVortOf D.P) r z t := by
  intro r z t hr hz ht
  have htpos : 0 < t := ht.1
  have hmem : t ∈ Work.ConstructionInstance.preWindow D.P.T := ⟨by linarith, ht.2⟩
  have hlam : 0 < D.P.lam t := D.P.hlam t hmem
  have hder : HasDerivAt D.P.lam (-D.κ) t := D.hrate t hmem
  have hΘpos : 0 < Work.Cyl.thetaP r z := Real.arctan_pos.mpr (div_pos hz hr)
  have hΘlt : Work.Cyl.thetaP r z < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have hZ : 0 < Work.Cyl.rhoP r z ^ Work.ConstructionInstance.profExp α / D.P.lam t :=
    div_pos (Real.rpow_pos_of_pos (Work.Cyl.rhoP_pos hr z) _) hlam
  have hmemQ : (Work.Cyl.rhoP r z ^ Work.ConstructionInstance.profExp α / D.P.lam t,
      Work.Cyl.thetaP r z) ∈ Work.Construction.Qd := ⟨hZ, hΘpos, hΘlt⟩
  have hkey := meridianResid_cut_ssVort_eq D.P (hp := profExp_pos_of_data D.P) hr hz htpos hlam
    hder (hF _ _ hmemQ) (hΦ _ _ hmemQ)
  simp only [ssVortOf, ssPsiOf] at hkey ⊢
  rw [hkey]
  have hpr : 2 * D.κ *
        (profOf D.P (Work.Cyl.rhoP r z ^ Work.ConstructionInstance.profExp α / D.P.lam t)
            (Work.Cyl.thetaP r z)
          + Work.Spaces.Dz (profOf D.P)
              (Work.Cyl.rhoP r z ^ Work.ConstructionInstance.profExp α / D.P.lam t)
              (Work.Cyl.thetaP r z))
      + Work.Construction.UVR (Work.ConstructionInstance.profExp α) (profOf D.P) D.Φ
          (Work.Cyl.rhoP r z ^ Work.ConstructionInstance.profExp α / D.P.lam t)
          (Work.Cyl.thetaP r z)
      = profileResid D.P D.κ D.Φ
          (Work.Cyl.rhoP r z ^ Work.ConstructionInstance.profExp α / D.P.lam t)
          (Work.Cyl.thetaP r z) := rfl
  rw [hpr, profileResid_eq_far_of_gEquationStat D.P D.hD D.hFar _ _ hmemQ]
  simp only [cutDeficit, chiRad]

/-- **The deficit is exactly the explicit cut-off term when the modulation cancels the
profile residual**: with `Far = 0` (the honest modulation) the meridian residual of the constructed
field against the self-similar stream function is `cutDeficit` and nothing else. -/
theorem ModulatedData.meridianResid_cut_eq_cutDeficit (D : ModulatedData α)
    (hΦ : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      ContDiffAt ℝ 2 (fun q : ℝ × ℝ => D.Φ q.1 q.2) (z, θ))
    (hF : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      ContDiffAt ℝ 1 (fun q : ℝ × ℝ => profOf D.P q.1 q.2) (z, θ))
    (hFar : ∀ z θ : ℝ, D.Far z θ = 0) :
    ∀ r z t : ℝ, 0 < r → 0 < z → t ∈ Set.Ioo 0 D.P.T →
      Work.CoreResiduals.meridianResid
          (fun r z t => Work.Stability.chi (Work.Cyl.rhoP r z / D.P.L)
            * ssVortOf D.P r z t)
          (ssPsiOf D.P D.Φ) r z t
        = cutDeficit D.P (ssPsiOf D.P D.Φ) (ssVortOf D.P) r z t := by
  intro r z t hr hz ht
  rw [D.meridianResid_cut_eq hΦ hF r z t hr hz ht, hFar]
  simp only [cutDeficit, chiRad, mul_zero, zero_add]

end Work.R1G
