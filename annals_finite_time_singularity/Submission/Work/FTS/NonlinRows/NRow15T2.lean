import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.NonlinRows.Defs
import Submission.Work.FTS.NonlinRows.NRow14
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.NonlinRows.NRow15T2Aux.Defs
import Submission.Work.FTS.NonlinRows.NRow15T2Aux.Jets
import Submission.Work.FTS.NonlinRows.NRow15T2Aux.Bound
import Submission.Work.FTS.NonlinRows.wtoHQ_of_pointwise_open
import Submission.Work.FTS.NonlinRows.NRow10aux.hkmem_of_majorant
import Submission.Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
import Submission.Work.FTS.EllipticEst.HkSq_congr_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open scoped Real Topology

open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false

/-!
# Row 15 of the §8 table, `T2` vocabulary: `N₂^{ss}`

`N₂^{ss} = -2·𝒰(Φ̃_*)·∂_θF_*` is the star-star piece of the second-order row.  Its weighted
form on the open quadrant is the product

  `((z+1)³/z²)·N₂^{ss} = (2·C15 α θ)·G15 α Φs z θ`

(`Work.FTS.NonlinRows.N2ss_weighted_eq`), a `θ`-only angular factor times the weighted star
coefficient `G15 = ((z+1)/z)·(𝒰(Φ̃_*)/sin 2θ)`, whose `𝒲^{4,∞}`-membership (the field `UszW` of
`VocabO2.StarPkgo2`) is exactly what the primed interface provides and what this row consumes.

The proof is the two-step scheme of the sibling rows 10/11: the pointwise `ℋ⁴`-bounds of the
open representative `N2ssO` (`Work.FTS.NonlinRows.row15_ptBound`, proved in
`NRow15T2Aux/Bound.lean`) are fed to the open-quadrant transfer
`Work.FTS.NonlinRows.wtoHQ_of_pointwise_open`, and the result is transported to `N₂^{ss}` itself
along the agreement of the two functions on the open quadrant
(`HkIntegrand_congr`, `HkSq_congr_open`).
-/

theorem NRow15T2 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.VocabO2.Ctx2 α₂ Ci Ct Ce Cs α g Φs Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N2ss α Φs) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2ss α Φs) ≤ K * α ^ 2 := by
  obtain ⟨Cw, hCw, hwto⟩ := wtoHQ_of_pointwise_open
  refine ⟨Cw * KW15 * (max Cs 0 + 1) + 1, ?_, ?_⟩
  · have h1 : 0 ≤ Cw * KW15 * (max Cs 0 + 1) :=
      mul_nonneg (mul_nonneg hCw.le (le_of_lt KW15_pos))
        (by linarith [le_max_right Cs 0])
    linarith
  · intro α g Φs Φg hctx
    obtain ⟨hα, hα1, hαα₂, hgal, hs, hell⟩ := hctx
    have hsp : Work.FTS.VocabO.StarPkgo α Cs Φs := hs.toStarPkgo
    -- the two `𝒲^{4,∞}`-facts about the star coefficient (the field `UszW` of `Ctx2`)
    have hGm : Work.Spaces.WlInfMem α 4 (G15 α Φs) := hs.UszW.1
    have hGle : Work.Spaces.WlInf α 4 (G15 α Φs) ≤ Cs * α := hs.UszW.2
    have hB0 : 0 ≤ Work.Spaces.WlInf α 4 (G15 α Φs) := Work.FTS.H2.WlInf_nonneg hGm
    -- smoothness of the three objects
    have hGs : Work.FTS.EllipticEst.SmoothOpen (G15 α Φs) := smoothOpen_G15 hα hα1 hsp
    have hNsO : Work.FTS.EllipticEst.SmoothOpen (N2ssO α Φs) := smoothOpen_N2ssO hα hα1 hsp
    have hNs : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N2ss α Φs) :=
      smoothOpen_N2ss hα hα1 hsp
    -- the pointwise bounds of the open representative
    have hpt := row15_ptBound (α := α) (Φs := Φs) hα hα1 hGs hGm
    have hW0 : (0 : ℝ) ≤ KW15 * α * Work.Spaces.WlInf α 4 (G15 α Φs) :=
      mul_nonneg (mul_nonneg (le_of_lt KW15_pos) hα.le) hB0
    have hmain := hwto α (N2ssO α Φs) (KW15 * α * Work.Spaces.WlInf α 4 (G15 α Φs))
      hα hα1 hW0 hNsO hpt.1 hpt.2
    -- the two representatives agree on the open quadrant
    have hAgree : Work.FTS.EllipticEst.AgreeOnQ (Work.FTS.Nonlin.N2ss α Φs) (N2ssO α Φs) := by
      intro z θ hz hθ0 hθ1
      rw [N2ss_open_eq hα hz hθ0 hθ1]
      simp only [N2ssO, AG15]
    constructor
    · -- `ℋ⁴`-honesty of `N₂^{ss}`, by domination of the open representative
      have hmaj : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
          Work.Spaces.HkIntegrand α 4 (Work.FTS.Nonlin.N2ss α Φs) z θ
            ≤ 1 * Work.Spaces.HkIntegrand α 4 (N2ssO α Φs) z θ := by
        intro z hz θ hθ
        rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
        · rw [← h0, one_mul,
            Work.FTS.NonlinRows.NRow10aux.HkIntegrand_zero α 4 _ θ,
            Work.FTS.NonlinRows.NRow10aux.HkIntegrand_zero α 4 _ θ]
        · rw [one_mul, ← Work.FTS.EllipticEst.HkIntegrand_congr (α := α) (k := 4) hAgree
            z θ hz0 hθ.1 hθ.2]
      exact (Work.FTS.NonlinRows.NRow10aux.hkmem_of_majorant α 4 (show (0 : ℝ) ≤ 1 by norm_num)
        hNs hmain.1 hmaj).1
    · -- the `α²`-bound, along the agreement of the two `ℋ⁴`-norms
      have hsq : Work.Spaces.HkSq α 4 (Work.FTS.Nonlin.N2ss α Φs)
          = Work.Spaces.HkSq α 4 (N2ssO α Φs) :=
        Work.FTS.EllipticEst.HkSq_congr_open α 4 hAgree
      have hXn : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2ss α Φs)
          = Work.FTS.Nonlin.Xn α (N2ssO α Φs) := by
        simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, hsq]
      rw [hXn]
      calc Work.FTS.Nonlin.Xn α (N2ssO α Φs)
          ≤ Cw * (KW15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)) := hmain.2
        _ ≤ Cw * (KW15 * α * (Cs * α)) := by
            refine mul_le_mul_of_nonneg_left ?_ hCw.le
            exact mul_le_mul_of_nonneg_left hGle
              (mul_nonneg (le_of_lt KW15_pos) hα.le)
        _ = Cw * KW15 * Cs * α ^ 2 := by ring
        _ ≤ Cw * KW15 * (max Cs 0) * α ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg α)
            exact mul_le_mul_of_nonneg_left (le_max_left Cs 0)
              (mul_nonneg hCw.le (le_of_lt KW15_pos))
        _ ≤ (Cw * KW15 * (max Cs 0 + 1) + 1) * α ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg α)
            have h2 : Cw * KW15 * (max Cs 0) ≤ Cw * KW15 * (max Cs 0 + 1) :=
              mul_le_mul_of_nonneg_left (by linarith)
                (mul_nonneg hCw.le (le_of_lt KW15_pos))
            linarith

end Work.FTS.NonlinRows
