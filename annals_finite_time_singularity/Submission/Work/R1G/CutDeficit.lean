/-
# `Work.R1G.CutDeficit` — the explicit cut-off deficit of residual R1

This module instantiates the cut-off identity `Work.R1G.meridianResid_cut` at the self-similar pair
`(ssVort p λ F, ssPsi p λ Φ)` and at the profile equation of the G-route.  The result is the
**explicit deficit** of the interface:

  `meridianResid (χ(ρ/L)·ssVort) (ssPsi) = χ(ρ/L)·(2λ²)⁻¹·(profile residual) + cutDeficit`,

so that when the modulation `g ≠ 0` cancels the profile residual (`profileResid = 0`, the
`g`-equation of `Work.Stability.GEquationFar` with vanishing far-field term) the *only* leftover in
the meridian residual of the constructed (cut) field is the fully explicit, local term
`cutDeficit P ψ W = (χ'(ρ/L)/L)·((∂_zψ)(r/ρ) - (ψ/r + ∂_rψ)(z/ρ))·W`.

This is the honest form of "the deficit carried by the interface": it is what the modulation has to
cancel, and it is a *function* (not a hypothesis).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.R1G.Defs
import Submission.Work.R1G.meridianResid_cut_ssVort_eq

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

/-- **The deficit of the G-route in meridian form.**  At the self-similar pair
`(ssVort p λ F, ssPsi p λ Φ)`, if the *profile residual* vanishes at
`(Z,Θ) = (ρ(r,z)^p/λ(t), arctan(z/r))` — the profile equation at the effective rate `2κ` — then the
meridian residual of the **cut** field `χ(ρ/L)·ssVort` against the self-similar stream function is
*exactly* the explicit cut-off deficit `cutDeficit`.

In the G-route's own vocabulary this is "the `g`-equation cancels the profile residual, leaving the
cut-off term": for a modulation `g ≠ 0` whose `g`-equation (`GEquationStat`, i.e.
`Work.Stability.GEquationFar`) has vanishing far-field term, `hres` below is
`profileResid_eq_gEqResidual` (`Work.R1G.profileResid_eq_gEqResidual`) read backwards. -/
theorem meridianResid_cut_ssVortOf_eq {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    {p κ : ℝ} (hp : 0 < p) {lam : ℝ → ℝ} {F Φ : ℝ → ℝ → ℝ}
    {r z t : ℝ} (hr : 0 < r) (hz : 0 < z) (ht : 0 < t)
    (hlam : 0 < lam t) (hder : HasDerivAt lam (-κ) t)
    (hF : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => F q.1 q.2)
      (Work.Cyl.rhoP r z ^ p / lam t, Work.Cyl.thetaP r z))
    (hΦ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2)
      (Work.Cyl.rhoP r z ^ p / lam t, Work.Cyl.thetaP r z))
    (hres : profileResidGen p κ F Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
      = 0) :
    Work.CoreResiduals.meridianResid
        (fun r z t => Work.Stability.chi (Work.Cyl.rhoP r z / P.L)
          * Work.CoreResiduals.ssVort p lam F r z t)
        (Work.CoreResiduals.ssPsi p lam Φ) r z t
      = cutDeficit P (Work.CoreResiduals.ssPsi p lam Φ)
          (Work.CoreResiduals.ssVort p lam F) r z t := by
  have hkey := meridianResid_cut_ssVort_eq P hp hr hz ht hlam hder hF hΦ
  rw [hkey]
  have hpr : 2 * κ * (F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
        + Work.Spaces.Dz F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z))
      + Work.Construction.UVR p F Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
      = profileResidGen p κ F Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z) := rfl
  rw [hpr, hres]
  simp only [mul_zero, zero_add]
  rfl

/-- **The deficit is where the cut-off bites**: the explicit cut-off deficit vanishes identically
where the cut-off is transparent (`χ' = 0`), and it is the *only* leftover of the meridian residual
once the profile equation at the effective rate holds. -/
theorem meridianResid_cut_ssVortOf_eq_zero_of_chi_deriv_eq_zero {α : NNReal}
    (P : Work.ConstructionInstance.ProfileData α) {p κ : ℝ} (hp : 0 < p) {lam : ℝ → ℝ}
    {F Φ : ℝ → ℝ → ℝ} {r z t : ℝ} (hr : 0 < r) (hz : 0 < z) (ht : 0 < t)
    (hlam : 0 < lam t) (hder : HasDerivAt lam (-κ) t)
    (hF : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => F q.1 q.2)
      (Work.Cyl.rhoP r z ^ p / lam t, Work.Cyl.thetaP r z))
    (hΦ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2)
      (Work.Cyl.rhoP r z ^ p / lam t, Work.Cyl.thetaP r z))
    (hres : profileResidGen p κ F Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z) = 0)
    (hχ : deriv Work.Stability.chi (Work.Cyl.rhoP r z / P.L) = 0) :
    Work.CoreResiduals.meridianResid
        (fun r z t => Work.Stability.chi (Work.Cyl.rhoP r z / P.L)
          * Work.CoreResiduals.ssVort p lam F r z t)
        (Work.CoreResiduals.ssPsi p lam Φ) r z t = 0 := by
  rw [meridianResid_cut_ssVortOf_eq P hp hr hz ht hlam hder hF hΦ hres]
  simp only [cutDeficit, chiRad, hχ, zero_div, zero_mul]


/-- **The self-similar stream-function route to R1 yields *exactly* the cut-off deficit.**  At the
self-similar pair with the profile equation at the effective rate satisfied (which is what the
`g`-equation gives, `Work.R1G.profileEq_of_gEquationStat`), the meridian residual of the
**constructed (cut)** field is the explicit cut-off deficit `cutDeficit` — and nothing else.

Since `cutDeficit` is *not* identically zero (`Work.R1G.exists_cutDeficit_ne_zero`: the cut-off
derivative `χ'(ρ/L)/L` is nonzero somewhere in `L < ρ < 2L`), this **refutes the self-similar
stream-function route** of `Work.CoreResiduals.R1Status.SelfSimStreamFunction` as a route to R1 at a
cut field: the honest stream function of the constructed velocity cannot be the self-similar one —
it must be the *actual* (elliptic-consistent) one, `bslOp p Φ = -χ(ρP/L)·profile` rather than
`bslOp p Φ = -profile` (`Work.R1G.vorticity_psiField_bslOp`). -/
theorem selfSimRoute_residual_eq_cutDeficit {α : NNReal}
    (P : Work.ConstructionInstance.ProfileData α) {κ : ℝ} (hκ : EffRate P κ) {Φ : ℝ → ℝ → ℝ}
    (hΦ : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2) (z, θ))
    (hF : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      ContDiffAt ℝ 1 (fun q : ℝ × ℝ => profOf P q.1 q.2) (z, θ))
    (h : ProfileEq P κ Φ) :
    ∀ r z t : ℝ, 0 < r → 0 < z → t ∈ Set.Ioo 0 P.T →
      Work.CoreResiduals.meridianResid
          (cutProfile P (ssVortOf P)) (ssPsiOf P Φ) r z t
        = cutDeficit P (ssPsiOf P Φ) (ssVortOf P) r z t := by
  intro r z t hr hz ht
  have htpos : 0 < t := ht.1
  have hmem : t ∈ Work.ConstructionInstance.preWindow P.T := ⟨by linarith, ht.2⟩
  have hlam : 0 < P.lam t := P.hlam t hmem
  have hder : HasDerivAt P.lam (-κ) t := hκ t hmem
  have hΘpos : 0 < Work.Cyl.thetaP r z := Real.arctan_pos.mpr (div_pos hz hr)
  have hΘlt : Work.Cyl.thetaP r z < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have hZ : 0 < Work.Cyl.rhoP r z ^ Work.ConstructionInstance.profExp α / P.lam t :=
    div_pos (Real.rpow_pos_of_pos (Work.Cyl.rhoP_pos hr z) _) hlam
  have hmemQ : (Work.Cyl.rhoP r z ^ Work.ConstructionInstance.profExp α / P.lam t,
      Work.Cyl.thetaP r z) ∈ Work.Construction.Qd := ⟨hZ, hΘpos, hΘlt⟩
  have hres : profileResidGen (Work.ConstructionInstance.profExp α) κ (profOf P) Φ
      (Work.Cyl.rhoP r z ^ Work.ConstructionInstance.profExp α / P.lam t)
      (Work.Cyl.thetaP r z) = 0 := by
    have := (profileEq_iff P κ Φ).mp h _ _ hmemQ
    rwa [profileResid_apply] at this
  exact meridianResid_cut_ssVortOf_eq P (hp := profExp_pos_of_data P) hr hz htpos hlam hder
    (hF _ _ hmemQ) (hΦ _ _ hmemQ) hres

end Work.R1G
