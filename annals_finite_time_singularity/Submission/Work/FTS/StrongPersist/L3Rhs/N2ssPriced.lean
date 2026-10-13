import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.NonlinRows.NRow15T2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs

/-- **Priced row 15**: the `ℋ⁴`-honesty and the `α²`-bound of the star piece `N₂^{**} = -2 · 𝒰(Φ̃_*) · ∂_θF_*`, with the constant *uniform* in `Cs` (linear loss in `1 + |Cs|`).

This is the priced form of `Work.FTS.NonlinRows.NRow15T2`: that result states
`∃ K, 0 < K ∧ ∀ …, Ctx2 … → HkMem α 4 (N2ss α Φs) ∧ Xn α (N2ss α Φs) ≤ K * α ^ 2`, where
`Ctx2` = `0 < α ∧ α ≤ 1 ∧ α ≤ α₂ ∧ GalClass α g ∧ StarPkgo2 α Cs Φs ∧ EllPkgGo α Ce g Φg`.
Its proof *constructs* the explicit constant `Cw * KW15 * (max Cs 0 + 1) + 1` (`Cw` = constant of
`Work.FTS.NonlinRows.wtoHQ_of_pointwise_open`, `KW15` a fixed positive constant of
`Work.FTS.NonlinRows.NRow15T2Aux`), and its body uses nothing but `0 < α`, `α ≤ 1`,
`StarPkgo α Cs Φs` and the two `𝒲^{4,∞}` facts about `G15 α Φs` (the field `StarPkgo2.UszW` is
exactly `WlInfMem α 4 (G15 α Φs) ∧ WlInf α 4 (G15 α Φs) ≤ Cs * α`).  So the proof is a copy of
that proof with `g`, `Φg`, `hgal`, `hell` dropped and `C = Cw * KW15 + 1`, using
`max Cs 0 + 1 ≤ 1 + |Cs|`. -/
theorem N2ssPriced : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (Cs : ℝ) (Φs : Work.FTS.Galerkin.Fn),
    Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N2ss α Φs) ∧
    Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2ss α Φs) ≤ C * (1 + |Cs|) * α ^ 2 := by
  obtain ⟨Cw, hCw, hwto⟩ := Work.FTS.NonlinRows.wtoHQ_of_pointwise_open
  refine ⟨Cw * Work.FTS.NonlinRows.KW15 + 1, ?_, ?_⟩
  · have h : 0 ≤ Cw * Work.FTS.NonlinRows.KW15 :=
      mul_nonneg hCw.le (le_of_lt Work.FTS.NonlinRows.KW15_pos)
    linarith
  · intro α hαIoc Cs Φs hs
    obtain ⟨hα, hα1⟩ := hαIoc
    -- the underlying star package, and the two `𝒲^{4,∞}`-facts about `G15 α Φs`
    have hsp : Work.FTS.VocabO.StarPkgo α Cs Φs := hs.toStarPkgo
    have hGm : Work.Spaces.WlInfMem α 4 (Work.FTS.NonlinRows.G15 α Φs) := hs.UszW.1
    have hGle : Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) ≤ Cs * α := hs.UszW.2
    have hB0 : 0 ≤ Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) :=
      Work.FTS.H2.WlInf_nonneg hGm
    -- smoothness of the three objects
    have hGs : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.NonlinRows.G15 α Φs) :=
      Work.FTS.NonlinRows.smoothOpen_G15 hα hα1 hsp
    have hNsO : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.NonlinRows.N2ssO α Φs) :=
      Work.FTS.NonlinRows.smoothOpen_N2ssO hα hα1 hsp
    have hNs : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N2ss α Φs) :=
      Work.FTS.NonlinRows.smoothOpen_N2ss hα hα1 hsp
    -- the pointwise bounds of the open representative
    have hpt := Work.FTS.NonlinRows.row15_ptBound (α := α) (Φs := Φs) hα hα1 hGs hGm
    have hW0 : (0 : ℝ) ≤ Work.FTS.NonlinRows.KW15 * α
        * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) :=
      mul_nonneg (mul_nonneg (le_of_lt Work.FTS.NonlinRows.KW15_pos) hα.le) hB0
    have hmain := hwto α (Work.FTS.NonlinRows.N2ssO α Φs)
      (Work.FTS.NonlinRows.KW15 * α * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs))
      hα hα1 hW0 hNsO hpt.1 hpt.2
    -- the two representatives agree on the open quadrant
    have hAgree : Work.FTS.EllipticEst.AgreeOnQ (Work.FTS.Nonlin.N2ss α Φs)
        (Work.FTS.NonlinRows.N2ssO α Φs) := by
      intro z θ hz hθ0 hθ1
      rw [Work.FTS.NonlinRows.N2ss_open_eq hα hz hθ0 hθ1]
      simp only [Work.FTS.NonlinRows.N2ssO, Work.FTS.NonlinRows.AG15]
    -- the honesty clause
    constructor
    · -- `ℋ⁴`-honesty of `N₂^{ss}`, by domination of the open representative
      have hmaj : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
          Work.Spaces.HkIntegrand α 4 (Work.FTS.Nonlin.N2ss α Φs) z θ
            ≤ 1 * Work.Spaces.HkIntegrand α 4 (Work.FTS.NonlinRows.N2ssO α Φs) z θ := by
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
          = Work.Spaces.HkSq α 4 (Work.FTS.NonlinRows.N2ssO α Φs) :=
        Work.FTS.EllipticEst.HkSq_congr_open α 4 hAgree
      have hXn : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2ss α Φs)
          = Work.FTS.Nonlin.Xn α (Work.FTS.NonlinRows.N2ssO α Φs) := by
        simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, hsq]
      rw [hXn]
      calc Work.FTS.Nonlin.Xn α (Work.FTS.NonlinRows.N2ssO α Φs)
          ≤ Cw * (Work.FTS.NonlinRows.KW15 * α
              * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)) := hmain.2
        _ ≤ Cw * (Work.FTS.NonlinRows.KW15 * α * (Cs * α)) := by
            refine mul_le_mul_of_nonneg_left ?_ hCw.le
            exact mul_le_mul_of_nonneg_left hGle
              (mul_nonneg (le_of_lt Work.FTS.NonlinRows.KW15_pos) hα.le)
        _ = Cw * Work.FTS.NonlinRows.KW15 * Cs * α ^ 2 := by ring
        _ ≤ (Cw * Work.FTS.NonlinRows.KW15 + 1) * (1 + |Cs|) * α ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg α)
            have hCK : 0 ≤ Cw * Work.FTS.NonlinRows.KW15 :=
              mul_nonneg hCw.le (le_of_lt Work.FTS.NonlinRows.KW15_pos)
            have hCsle : Cs ≤ 1 + |Cs| := by
              linarith [le_abs_self Cs, abs_nonneg Cs]
            have h1Cs : 0 ≤ 1 + |Cs| := by positivity
            calc Cw * Work.FTS.NonlinRows.KW15 * Cs
                ≤ Cw * Work.FTS.NonlinRows.KW15 * (1 + |Cs|) :=
                  mul_le_mul_of_nonneg_left hCsle hCK
              _ ≤ (Cw * Work.FTS.NonlinRows.KW15 + 1) * (1 + |Cs|) :=
                  mul_le_mul_of_nonneg_right (by linarith) h1Cs

end Work.FTS.StrongPersist.L3Rhs
