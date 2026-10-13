import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.NonlinRows.NRow19T2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.NonlinRows

/-- **Priced row 19**: the `ℋ⁴`-honesty and the `α³`-bound of the star piece `N₃^{**} = -2α · 𝒱(Φ̃_*) · D_zF_*`, with the constant *uniform* in `Cs` (linear loss in `1 + |Cs|`).

This is the priced form of `Work.FTS.NonlinRows.NRow19T2`: that result states
`∃ K, 0 < K ∧ ∀ …, Ctx2 … → HkMem α 4 (N3ss α Φs) ∧ Xn α (N3ss α Φs) ≤ K * α ^ 3`, where
`Ctx2` = `0 < α ∧ α ≤ 1 ∧ α ≤ α₂ ∧ GalClass α g ∧ StarPkgo2 α Cs Φs ∧ EllPkgGo α Ce g Φg`.
Its proof *constructs* the explicit constant `2 * Cw * CZ19 C2 * max Cs 0 + 1` (`Cw` = constant
of `Work.FTS.NonlinRows.wtoHQ_of_pointwise_open`, `CZ19`, `C2` fixed positive constants of
`Work.FTS.NonlinRows.NRow19T2Parts`), and its body uses nothing but `0 < α`, `α ≤ 1`,
`StarPkgo α Cs Φs` and the two `𝒲^{4,∞}` facts about
`A19 α Φs = ((z+1)/z) · 𝒱(Φ̃_*)` (the field `StarPkgo2.VzW` is exactly
`WlInfMem α 4 (A19 α Φs) ∧ WlInf α 4 (A19 α Φs) ≤ Cs * α`).  So the proof is a copy of that
proof with `g`, `Φg`, `hgal`, `hell` dropped and `C = 2 * Cw * CZ19 C2 + 1`, using
`max Cs 0 ≤ 1 + |Cs|`. -/
theorem N3ssPriced : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (Cs : ℝ) (Φs : Work.FTS.Galerkin.Fn),
    Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N3ss α Φs) ∧
    Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3ss α Φs) ≤ C * (1 + |Cs|) * α ^ 3 := by
  obtain ⟨Cw, hCw, hwto⟩ := Work.FTS.NonlinRows.wtoHQ_of_pointwise_open
  obtain ⟨C2, hC2pos, hC2⟩ := Work.FTS.Nonlinear.Open.Row19Prep.H2b_weight_le
  have hCZpos : 0 < CZ19 C2 := by
    rw [CZ19]
    have h1 : (0 : ℝ) < 10 ^ 20 := by norm_num
    have h2 : (0 : ℝ) < 1 + C2 := by linarith [hC2pos]
    have h3 : (0 : ℝ) < 1 + TB19 := by linarith [TB19_nonneg]
    exact mul_pos (mul_pos h1 h2) h3
  refine ⟨2 * Cw * CZ19 C2 + 1, ?_, ?_⟩
  · have h : (0 : ℝ) < 2 * Cw * CZ19 C2 :=
      mul_pos (mul_pos (by norm_num) hCw) hCZpos
    linarith
  · intro α hαI Cs Φs hs2
    obtain ⟨hα, hα1⟩ := hαI
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
      have hA0 : (0 : ℝ) ≤ 2 * Cw * CZ19 C2 :=
        (mul_pos (mul_pos (by norm_num) hCw) hCZpos).le
      have hα3 : (0 : ℝ) ≤ α ^ 3 := by positivity
      have hfin : 2 * Cw * CZ19 C2 * Cs * α ^ 3
          ≤ (2 * Cw * CZ19 C2 + 1) * (1 + |Cs|) * α ^ 3 := by
        have hCs : Cs ≤ 1 + |Cs| := by
          have hle := le_abs_self Cs
          linarith
        have h1 : 2 * Cw * CZ19 C2 * Cs ≤ 2 * Cw * CZ19 C2 * (1 + |Cs|) :=
          mul_le_mul_of_nonneg_left hCs hA0
        have h2 : 2 * Cw * CZ19 C2 * (1 + |Cs|)
            ≤ (2 * Cw * CZ19 C2 + 1) * (1 + |Cs|) := by
          refine mul_le_mul_of_nonneg_right ?_ ?_
          · linarith
          · have hle := abs_nonneg Cs
            linarith
        exact mul_le_mul_of_nonneg_right (le_trans h1 h2) hα3
      calc 2 * α * Work.FTS.Nonlin.Xn α (Z19 α Φs)
          ≤ 2 * α * (Cw * (CZ19 C2 * α * Work.Spaces.WlInf α 4 (A19 α Φs))) :=
            mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num) hα.le)
        _ ≤ 2 * α * (Cw * (CZ19 C2 * α * (Cs * α))) :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg (by norm_num) hα.le)
        _ = 2 * Cw * CZ19 C2 * Cs * α ^ 3 := h3
        _ ≤ (2 * Cw * CZ19 C2 + 1) * (1 + |Cs|) * α ^ 3 := hfin

end Work.FTS.StrongPersist.L3Rhs
