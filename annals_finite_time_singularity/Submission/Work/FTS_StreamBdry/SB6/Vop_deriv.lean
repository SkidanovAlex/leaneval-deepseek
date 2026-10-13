import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB6.infra
import Submission.Work.FTS_StreamBdry.SB6.psiP_bounds
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB25.law_Dform
import Submission.Work.FTS_StreamBdry.SB3.psiP_DzLe
import Submission.Work.FTS_StreamBdry.SB3.psiP_c2
import Submission.Work.FTS_StreamBdry.SB3.P2Aux.AsmSupport

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.Vop_deriv` — `∂_θV(psiP)` in the far field
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK psiP oddPerS)

set_option autoImplicit false

/-- **The `θ`-derivative of `V(psiP)` in the far field**: the law in `D`-form
`∂_θV(P) = -(α²D_z²P + 5αD_zP + 6P) - F` together with the far-field decay of `D_z^jP` (`j ≤ 2`)
and the vanishing of `F` above `L`. -/
theorem Vop_deriv_le {αG M L Mf Kf : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M)
    (hF : Work.FTS.StreamBdryIface.SrcOK F L Mf)
    (hKf : 0 ≤ Kf)
    (hfar : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z → ∀ j ≤ 2,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ|
        ≤ Kf * Work.Construction.s2 θ * (L / z) ^ (4 / αG)) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z →
      |deriv (fun t => Work.Construction.Vop (psiP αG Ψ) z t) θ|
        ≤ (αG ^ 2 + 5 * |αG| + 6) * Kf * (L / z) ^ (4 / αG) * Work.Construction.s2 θ := by
  intro z θ hmem hzL
  have hL : 0 < L := hF.2.2.2.2.1
  have hzpos : 0 < z := Work.FTS_StreamBdry.Qd_pos hmem
  have hθI : θ ∈ Work.Spaces.Iθ := Work.FTS_StreamBdry.Qd_theta_Iθ hmem
  have hP2 : ContDiffOn ℝ 2 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.psiP_c2 hαG h3 hslot
  have hlaw : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Elliptic.bslOp αG (psiP αG Ψ) z θ = F z θ :=
    Work.FTS_StreamBdry.SB3.P2Aux.bslOp_psiP hαG hsol h3 hslot
  have hkey := Work.FTS_StreamBdry.SB25.law_Dform αG F (psiP αG Ψ) hP2 hlaw z θ hmem
  have hb0 := hfar z θ hmem hzL 0 (by norm_num)
  have hb1 := hfar z θ hmem hzL 1 (by norm_num)
  have hb2 := hfar z θ hmem hzL 2 (by norm_num)
  have hb1' : |Work.Spaces.Dz (psiP αG Ψ) z θ|
      ≤ Kf * Work.Construction.s2 θ * (L / z) ^ (4 / αG) := by
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using hb1
  have hF0 : F z θ = 0 := hF.2.2.2.2.2 z θ hzL hθI
  have hkey' : deriv (fun t => Work.Construction.Vop (psiP αG Ψ) z t) θ
      = -(αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z θ
          + 5 * αG * Work.Spaces.Dz (psiP αG Ψ) z θ + 6 * psiP αG Ψ z θ) - F z θ := by
    simpa only [Work.Spaces.pth] using hkey
  rw [hkey', hF0, sub_zero]
  set A : ℝ := Work.Spaces.DzIter 2 (psiP αG Ψ) z θ with hA
  set B : ℝ := Work.Spaces.Dz (psiP αG Ψ) z θ with hB
  set C : ℝ := psiP αG Ψ z θ with hC
  have hb2' : |A| ≤ Kf * Work.Construction.s2 θ * (L / z) ^ (4 / αG) := by
    rw [hA]; exact hb2
  have hb1'' : |B| ≤ Kf * Work.Construction.s2 θ * (L / z) ^ (4 / αG) := by
    rw [hB]; exact hb1'
  have hb0' : |C| ≤ Kf * Work.Construction.s2 θ * (L / z) ^ (4 / αG) := by
    rw [hC]; exact hb0
  have h1 : |αG ^ 2 * A| = αG ^ 2 * |A| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ αG ^ 2)]
  have h2 : |5 * αG * B| = 5 * |αG| * |B| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5)]
  have h3 : |(6 : ℝ) * C| = 6 * |C| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
  have hb2'' : |A| ≤ Kf * Work.Construction.s2 θ * (L / z) ^ (4 / αG) := hb2'
  have htri : |-(αG ^ 2 * A + 5 * αG * B + 6 * C)|
      ≤ αG ^ 2 * |A| + 5 * |αG| * |B| + 6 * |C| := by
    rw [abs_neg]
    refine (abs_three_le (a := αG ^ 2 * A) (b := 5 * αG * B) (c := 6 * C)).trans ?_
    rw [h1, h2, h3]
  have hstep : αG ^ 2 * |A| + 5 * |αG| * |B| + 6 * |C|
      ≤ αG ^ 2 * (Kf * Work.Construction.s2 θ * (L / z) ^ (4 / αG))
        + 5 * |αG| * (Kf * Work.Construction.s2 θ * (L / z) ^ (4 / αG))
        + 6 * (Kf * Work.Construction.s2 θ * (L / z) ^ (4 / αG)) := by
    refine add_le_add (add_le_add ?_ ?_) ?_
    · exact mul_le_mul_of_nonneg_left hb2'' (by positivity)
    · exact mul_le_mul_of_nonneg_left hb1'' (by positivity)
    · exact mul_le_mul_of_nonneg_left hb0' (by norm_num)
  refine htri.trans (hstep.trans (le_of_eq ?_))
  ring

end Work.FTS_StreamBdry.SB6
