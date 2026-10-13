/-
# Row 19 in the `T2` vocabulary — the target

The declarations of `Submission/Work/FTS/NonlinRows/NRow19T2Parts/` give the two pointwise
families of `Z₁₉ = 𝒱(Φ̃_*)·∂_zF_*`; here they are fed to
`Work.FTS.NonlinRows.wtoHQ_of_pointwise_open`, which yields both the `ℋ⁴`-honesty of `Z₁₉` and
its norm bound, and the result is transported to `N₃^{**} = -2α·Z₁₉` along the open quadrant
(`HkMem_congr_Ioi`, `HkSq_congr_open`, `xn_N3ss_of_nonneg`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.NonlinRows.Defs
import Submission.Work.FTS.NonlinRows.NRow19T2Parts.Gam
import Submission.Work.FTS.OpenPkg.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

theorem NRow19T2 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.VocabO2.Ctx2 α₂ Ci Ct Ce Cs α g Φs Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N3ss α Φs) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3ss α Φs) ≤ K * α ^ 3 := by
  obtain ⟨Cw, hCw, hwto⟩ := Work.FTS.NonlinRows.wtoHQ_of_pointwise_open
  obtain ⟨C2, hC2pos, hC2⟩ := Work.FTS.Nonlinear.Open.Row19Prep.H2b_weight_le
  have hCZpos : 0 < CZ19 C2 := by
    rw [CZ19]
    have h1 : (0 : ℝ) < 10 ^ 20 := by norm_num
    have h2 : (0 : ℝ) < 1 + C2 := by linarith [hC2pos]
    have h3 : (0 : ℝ) < 1 + TB19 := by linarith [TB19_nonneg]
    exact mul_pos (mul_pos h1 h2) h3
  refine ⟨2 * Cw * CZ19 C2 * max Cs 0 + 1, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 2 * Cw * CZ19 C2 * max Cs 0 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCw.le) hCZpos.le) (le_max_right Cs 0)
    linarith
  · intro α g Φs Φg hctx
    obtain ⟨hα, hα1, _hαα₂, _hgal, hs2, _hell⟩ := hctx
    have hs : Work.FTS.VocabO.StarPkgo α Cs Φs := hs2.toStarPkgo
    have hAsm : Work.FTS.EllipticEst.SmoothOpen (A19 α Φs) := smoothOpen_A19 hα hα1 hs
    have hAmem : Work.Spaces.WlInfMem α 4 (A19 α Φs) := hs2.VzW.1
    have hAle : Work.Spaces.WlInf α 4 (A19 α Φs) ≤ Cs * α := hs2.VzW.2
    have hL0 : 0 ≤ Work.Spaces.WlInf α 4 (A19 α Φs) := WlInf_nonneg' α 4 _ hAmem
    have hC2nn : 0 ≤ C2 := hC2pos.le
    have hW0 : 0 ≤ CZ19 C2 * α * Work.Spaces.WlInf α 4 (A19 α Φs) :=
      mul_nonneg (mul_nonneg hCZpos.le hα.le) hL0
    have hsm : Work.FTS.EllipticEst.SmoothOpen (Z19 α Φs) := smoothOpen_Z19 hα hα1 hs
    have hmain := hwto α (Z19 α Φs) (CZ19 C2 * α * Work.Spaces.WlInf α 4 (A19 α Φs))
      hα hα1 hW0 hsm (Z19_eta_bound hα hα1 hAsm hAmem hC2 hC2nn)
      (Z19_gam_bound hα hα1 hAsm hAmem hC2 hC2nn)
    -- transport along the open quadrant
    have hAG : ∀ z θ : ℝ, 0 < z →
        Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs z θ * Work.FTS.Nonlinear.Pieces.RNP.Gs α z θ
          = Z19 α Φs z θ := fun z θ hz => (Z19_eq_Vs_Gs hα z hz θ).symm
    have hmemZ : Work.Spaces.HkMem α 4 (Z19 α Φs) := hmain.1
    have hmemVG : Work.Spaces.HkMem α 4
        (fun z θ => Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs z θ
          * Work.FTS.Nonlinear.Pieces.RNP.Gs α z θ) :=
      Work.Coercivity.HkMem_congr_Ioi α 4 hmemZ (fun z hz θ _ => (hAG z θ hz).symm)
    have hsqeq : Work.Spaces.HkSq α 4 (fun z θ => Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs z θ
          * Work.FTS.Nonlinear.Pieces.RNP.Gs α z θ) = Work.Spaces.HkSq α 4 (Z19 α Φs) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 4
        (f := fun z θ => Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs z θ
          * Work.FTS.Nonlinear.Pieces.RNP.Gs α z θ) (g := Z19 α Φs)
        (fun z θ hz _ _ => hAG z θ hz)
    have hXneq : Work.FTS.Nonlin.Xn α (fun z θ => Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs z θ
          * Work.FTS.Nonlinear.Pieces.RNP.Gs α z θ) = Work.FTS.Nonlin.Xn α (Z19 α Φs) := by
      simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, hsqeq]
    constructor
    · have hN3 : Work.FTS.Nonlin.N3ss α Φs
          = fun z θ => (-2 * α) * (Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs z θ
              * Work.FTS.Nonlinear.Pieces.RNP.Gs α z θ) := by
        funext z θ
        simp only [Work.FTS.Nonlin.N3ss, Work.FTS.Nonlinear.Pieces.RNP.Vs,
          Work.FTS.Nonlinear.Pieces.RNP.Gs]
        ring
      rw [hN3]
      exact Work.FTS.LocData.HkMem_const_mul α 4 (-2 * α) hmemVG
    · have hN3x := Work.FTS.Nonlinear.Pieces.RNP.xn_N3ss_of_nonneg hα.le Φs
      rw [hN3x, hXneq]
      have h1 : Work.FTS.Nonlin.Xn α (Z19 α Φs)
          ≤ Cw * (CZ19 C2 * α * Work.Spaces.WlInf α 4 (A19 α Φs)) := hmain.2
      have h2 : Cw * (CZ19 C2 * α * Work.Spaces.WlInf α 4 (A19 α Φs))
          ≤ Cw * (CZ19 C2 * α * (Cs * α)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCw.le
        exact mul_le_mul_of_nonneg_left hAle (mul_nonneg hCZpos.le hα.le)
      have h3 : 2 * α * (Cw * (CZ19 C2 * α * (Cs * α)))
          = 2 * Cw * CZ19 C2 * Cs * α ^ 3 := by ring
      calc 2 * α * Work.FTS.Nonlin.Xn α (Z19 α Φs)
          ≤ 2 * α * (Cw * (CZ19 C2 * α * Work.Spaces.WlInf α 4 (A19 α Φs))) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ 2 * α * (Cw * (CZ19 C2 * α * (Cs * α))) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 2 * Cw * CZ19 C2 * Cs * α ^ 3 := h3
        _ ≤ (2 * Cw * CZ19 C2 * max Cs 0 + 1) * α ^ 3 := by
            have hle : Cs ≤ max Cs 0 := le_max_left _ _
            have h1 : 0 ≤ 2 * Cw * CZ19 C2 := by positivity
            have h2 : 0 ≤ α ^ 3 := by positivity
            have h3 : 2 * Cw * CZ19 C2 * Cs ≤ 2 * Cw * CZ19 C2 * max Cs 0 :=
              mul_le_mul_of_nonneg_left hle h1
            nlinarith [h2, h3]

end Work.FTS.NonlinRows
