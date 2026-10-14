import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.Dzg_pthg_split
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.R1G.profileResid_eq_gEqResidual_qd
import Submission.Work.R1G.vorticity_psiField_bslOp
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.Defs
import Submission.Work.Stability.L12Add
import Submission.Work.Stability.MainLHSSubN
-- ===== merged: Submission.Work.FTS.MeridianDyn.Bridge.ProfDerivData_of_regPkg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Bridge

open scoped Real Topology

/-! ## The `τ`-slice of the joint regularity of `RegPkg` -/


/-! ## The static derivation data of the `St2` chain, from the regularity package -/


end Work.FTS.MeridianDyn.Bridge
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Bridge.mainLHS_sub_N_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Bridge

theorem mainLHS_sub_N_eq {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g Φ : Work.FTS.MeridianDyn.Fam}
    {M : Work.Stability.ModState} {z θ τ : ℝ} (hzθ : (z, θ) ∈ Work.Construction.Qd)
    (h2 : Work.Spaces.pz (Work.FTS.Galerkin.slice Φ τ) z θ
      = Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Ftau α g τ)
            (Work.FTS.Galerkin.slice Φ τ)) z θ
        + Work.Spaces.pz (Work.Construction.Theta α (Work.Construction.Ftau α g τ)) z θ)
    (h3 : Work.Spaces.pth (Work.FTS.Galerkin.slice Φ τ) z θ
      = Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Ftau α g τ)
            (Work.FTS.Galerkin.slice Φ τ)) z θ
        + Work.Spaces.pth (Work.Construction.Theta α (Work.Construction.Ftau α g τ)) z θ)
    (h5 : z * Work.Spaces.pz (Work.Construction.Theta α (Work.Construction.Ftau α g τ)) z θ
      = -(1 / (4 * α)) * Work.Construction.s2 θ
          * Work.Construction.FK (Work.Construction.Ftau α g τ) z)
    (h6 : Work.Spaces.pth (Work.Construction.Theta α (Work.Construction.Ftau α g τ)) z θ
      = (1 / (2 * α)) * Real.cos (2 * θ)
          * Work.Construction.L12 (Work.Construction.Ftau α g τ) z)
    (hDz : Work.Spaces.Dz (Work.Construction.Ftau α g τ) z θ
      = Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        + Work.Spaces.Dz (Work.FTS.Galerkin.slice g τ) z θ)
    (hpth : Work.Spaces.pth (Work.Construction.Ftau α g τ) z θ
      = Work.Spaces.pth (Work.Construction.Fstar α) z θ
        + Work.Spaces.pth (Work.FTS.Galerkin.slice g τ) z θ)
    (hL : Work.Construction.L12 (Work.Construction.Ftau α g τ) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z
        + Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) z) :
    Work.Construction.MainLHS α (M.kappa τ - 1) (M.b τ - 1)
        (Work.Construction.Ftau α g τ) z θ
        - Work.Construction.N α (Work.Construction.Ftau α g τ)
            (Work.FTS.Galerkin.slice Φ τ) z θ
      = Work.Coercivity.LGammaT α (Work.FTS.Galerkin.slice g τ) z θ
        - Work.Stability.gDynRHS α M g Φ z θ τ := by
  have hz0 : 0 < z := hzθ.1
  have hz1 : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith)
  have hznn : 0 ≤ z := le_of_lt hz0
  -- Rewrite the two families in the stability vocabulary (`Ftot`/`slice`), with which
  -- `gDynRHS` is written; the conversion is definitional.
  change Work.Construction.MainLHS α (M.kappa τ - 1) (M.b τ - 1)
        (Work.Stability.Ftot α g τ) z θ
        - Work.Construction.N α (Work.Stability.Ftot α g τ)
            (Work.Stability.slice Φ τ) z θ
      = Work.Coercivity.LGammaT α (Work.Stability.slice g τ) z θ
        - Work.Stability.gDynRHS α M g Φ z θ τ
  have hDz' : Work.Spaces.Dz (Work.Stability.Ftot α g τ) z θ
      = Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        + Work.Spaces.Dz (Work.Stability.slice g τ) z θ := hDz
  have hpth' : Work.Spaces.pth (Work.Stability.Ftot α g τ) z θ
      = Work.Spaces.pth (Work.Construction.Fstar α) z θ
        + Work.Spaces.pth (Work.Stability.slice g τ) z θ := hpth
  have hL' : Work.Construction.L12 (Work.Stability.Ftot α g τ) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z
        + Work.Construction.L12 (Work.Stability.slice g τ) z := hL
  have hLstar : Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) :=
    Work.Construction.L12_Fstar_eq hα hα1 hznn
  have hstat : Work.Construction.Fstar α z θ
      + Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      - (1 / α) * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Construction.Fstar α z θ = 0 :=
    Work.Construction.Fstar_stationary_identity hα hα1 hznn
  have hF : Work.Stability.Ftot α g τ z θ
      = Work.Construction.Fstar α z θ + Work.Stability.slice g τ z θ := rfl
  -- the transport term is the `L₁₂(F_*)`-weighted `∂_θg` term
  have hT : Work.Coercivity.Transport (Work.Stability.slice g τ) z θ
      = (3 / (2 * α)) * Work.Construction.s2 θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.pth (Work.Stability.slice g τ) z θ := by
    rw [Work.Coercivity.Transport_eq, hLstar, Work.Construction.s2, Work.Spaces.Dth]
    field_simp
  -- the explicit expansion of `MainLHS` along `F = F_* + g`
  have hex := Work.Construction.MainLHS_explicit (α := α) (μ := M.kappa τ - 1)
    (lam := M.b τ - 1) hα (F := Work.Stability.Ftot α g τ)
    (g := Work.Stability.slice g τ) z θ hz1 hF hDz' hpth' hL' hLstar hstat
  rw [hex]
  -- `𝓛_Γ^T = 𝓛_Γ - Transport + AK·L₁₂(Transport)(0)`
  rw [Work.Construction.LGammaT_eq]
  -- unfold the right hand side: the `N`-terms cancel against the `-N` on the left,
  -- and the two `AK·L₁₂(Transport)(0)` projectors cancel between `𝓛_Γ^T` and `gDynRHS`
  simp only [Work.Stability.gDynRHS, Work.Construction.Nstar]
  rw [hT]
  ring

end Work.FTS.MeridianDyn.Bridge
end
