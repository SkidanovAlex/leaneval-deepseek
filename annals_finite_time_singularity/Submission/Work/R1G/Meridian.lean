/-
# `Work.R1G.Meridian` — the meridian equation of the uncut pair from the profile equation

The G-route's *uncut* half: once the modulation `g ≠ 0` solves the profile equation at the
effective rate `2κ` (`Work.R1G.ProfileEq`, the promotion of
`Work.Construction.Fstar_stationary_identity` through the `St2`/`St3` content, see
`Work.R1G.GEquation`), the self-similar pair `(ssVort p λ̄ (F_* + g), ssPsi p λ̄ Φ)` solves the
meridian scalar equation in the window `0 < t < T`.

This is the reduction of `Work.R1G.SelfSimStreamFunction`'s second clause (the `R1UncutRoute` of
`Work.CoreResiduals.R1Status`): the meridian equation holds as soon as the profile equation does,
with no elliptic input.  The *cut* field's residual is then the explicit cut-off deficit
(`Work.R1G.meridianResid_cut_ssVortOf_eq`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.R1G.Defs
import Submission.Work.R1G.meridianResid_ssVort_eq

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

/-- **The uncut self-similar pair solves the meridian equation.**  If the full profile
`F = F_* + P.g` satisfies the profile equation at the effective rate `2κ` (`ProfileEq`) and the
modulation is `κ`-compatible on the pre-window (`EffRate`), then the meridian residual of
`(ssVortOf P, ssPsiOf P Φ)` vanishes in the physical window `0 < t < P.T`.

The differentiability hypotheses are the pointwise `C¹`/`C²` conditions of `F` and `Φ` on the open
quadrant that the chain-rule reduction consumes. -/
theorem meridianResid_ssVortOf_eq_zero (P : Work.ConstructionInstance.ProfileData α)
    {κ : ℝ} (hκ : EffRate P κ) {Φ : ℝ → ℝ → ℝ}
    (hΦ : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2) (z, θ))
    (hF : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      ContDiffAt ℝ 1 (fun q : ℝ × ℝ => profOf P q.1 q.2) (z, θ))
    (h : ProfileEq P κ Φ) :
    ∀ r z t : ℝ, 0 < r → 0 < z → t ∈ Set.Ioo 0 P.T →
      Work.CoreResiduals.meridianResid (ssVortOf P) (ssPsiOf P Φ) r z t = 0 := by
  intro r z t hr hz ht
  have htpos : 0 < t := ht.1
  have hlt : t < P.T := ht.2
  have hmem : t ∈ Work.ConstructionInstance.preWindow P.T := ⟨by linarith, hlt⟩
  have hlam : 0 < P.lam t := P.hlam t hmem
  have hder : HasDerivAt P.lam (-κ) t := hκ t hmem
  have hΘpos : 0 < Work.Cyl.thetaP r z :=
    Real.arctan_pos.mpr (div_pos hz hr)
  have hΘlt : Work.Cyl.thetaP r z < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have hZ : 0 < Work.Cyl.rhoP r z ^ Work.ConstructionInstance.profExp α / P.lam t :=
    div_pos (Real.rpow_pos_of_pos (Work.Cyl.rhoP_pos hr z) _) hlam
  have hmemQ : (Work.Cyl.rhoP r z ^ Work.ConstructionInstance.profExp α / P.lam t,
      Work.Cyl.thetaP r z) ∈ Work.Construction.Qd := ⟨hZ, hΘpos, hΘlt⟩
  have hzero : profileResid P κ Φ
      (Work.Cyl.rhoP r z ^ Work.ConstructionInstance.profExp α / P.lam t)
      (Work.Cyl.thetaP r z) = 0 :=
    (profileEq_iff P κ Φ).mp h _ _ hmemQ
  have hkey := meridianResid_ssVort_eq (p := Work.ConstructionInstance.profExp α)
    (profExp_pos_of_data P) hr hz htpos hlam hder
    (hF _ _ hmemQ) (hΦ _ _ hmemQ)
  simp only [ssVortOf, ssPsiOf]
  rw [hkey]
  show (2 * P.lam t ^ 2)⁻¹ * profileResid P κ Φ
      (Work.Cyl.rhoP r z ^ Work.ConstructionInstance.profExp α / P.lam t)
      (Work.Cyl.thetaP r z) = 0
  rw [hzero, mul_zero]

end Work.R1G
