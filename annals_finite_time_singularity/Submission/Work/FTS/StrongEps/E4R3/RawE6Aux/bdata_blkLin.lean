import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.Defs
import Submission.Work.FTS.GalFields.Norm.HkSq_Lhat_le_uniform
import Submission.Work.FTS.StrongPersist.H6Aux.Corr_HkSq6
import Submission.Work.FTS.StrongEps.EpsRLX.LGTDiffClassC
import Submission.Work.FTS.StrongEps.EpsGdotThird

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- `open scoped Real` makes the bare `π` of the statement below the *notation* for
-- `Real.pi`; without it (and with the workspace's `autoImplicit = false`) `π` is an unknown
-- identifier and the file does not elaborate.  This is the reading of the sibling consumer
-- `RawE6Aux/EpsWPSemitameAux/DevPlaceholders.bdata_blkLin_dev` and of
-- `RawE6Aux/epsWP_semitame_aux`, both of which write the same hypothesis under
-- `open scoped Real`; no other symbol of the statement is affected.
open scoped Real

namespace Work.FTS.StrongEps.E4R3.RawE6Aux

set_option maxHeartbeats 1600000

/-- `BData` for the linear block `blkLin α w = LGammaT α w` of the semi-tame estimate of `epsWP`.  See `Submission/Work/FTS/StrongEps/E4R3/RawE6Aux/NOTES_bdata_blocks.md` for the route. -/
theorem bdata_blkLin (C₀ : ℝ) :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α ∈ Set.Ioc (0 : ℝ) α₀, ∃ KL : ℝ, 0 < KL ∧
    ∀ {w : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)) → w z θ = 0) →
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w KL
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkLin α w) := by
  -- ## the constants of the two halves of `𝓛_Γ^T = 𝓛̂ + Corr`
  obtain ⟨Cl, hClpos, hLhat4⟩ := Work.FTS.GalFields.Norm.HkSq_Lhat_le_uniform
  obtain ⟨Cl6, hCl6pos, hLhat6⟩ := Work.FTS.GalFields.Norm.HkSq_Lhat_le_uniform_aux 6
  obtain ⟨Kang, hKangpos, hang⟩ := Work.FTS.GalFields.Norm.ang_fac_integrable_bound
  obtain ⟨Crad, hCradpos, hrad⟩ :=
    Work.FTS.StrongEps.EpsRLX.RadBound.radA_slot5_le_classC_of
      Work.FTS.StrongEps.EpsRLX.RadBound.L12fSlotLe
  obtain ⟨C6, α₂, hC6pos, hα₂pos, hCorr6⟩ := Work.FTS.StrongPersist.H6Aux.Corr_HkSq6
  have hKCnn : 0 ≤ Kang * Crad := mul_nonneg hKangpos.le hCradpos.le
  refine ⟨min 1 α₂, lt_min one_pos hα₂pos, ?_⟩
  intro α hαIoc
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := le_trans hαIoc.2 (min_le_left _ _)
  have hα₂ : α ∈ Set.Ioc (0 : ℝ) α₂ := ⟨hα, le_trans hαIoc.2 (min_le_right _ _)⟩
  refine ⟨2 * Cl + 2 * (Kang * Crad) + (2 * Cl6 + 2 * C6) + 1, by linarith, ?_⟩
  intro w hC hsmall hzero
  -- ## the datum
  have hmem4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hC.reg 4 (by norm_num) hC.mem
  have hmem5 : Work.Spaces.HkMem α 5 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hC.reg 5 (by norm_num) hC.mem
  have hmem7 : Work.Spaces.HkMem α 7 w := hC.mem
  have hH6 : Work.FTS.StrongPersist.H6Adm α w :=
    Work.FTS.StrongEps.H6Adm_of_classC_of_eqzero hC hzero
  -- ## the two summands of `𝓛_Γ^T = 𝓛̂ + Corr`
  have hLhatsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.CoercivityFix.Lhat w) :=
    Work.FTS.StrongPersist.H6Aux.smoothOpen_Lhat hC.reg
  have hLGTsm : Work.FTS.EllipticEst.SmoothOpen (Work.Coercivity.LGammaT α w) :=
    Work.FTS.GalFields.RHS.smoothOpen_LGammaT_of_L12
      (Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hC) hC.reg
  have hCorrsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.CoercivityFix.Corr α w) :=
    Work.FTS.NonlinRows.smoothOpen_sub hLGTsm hLhatsm
  -- ## level 4
  have hLhatmem4 : Work.Spaces.HkMem α 4 (Work.FTS.CoercivityFix.Lhat w) :=
    Work.FTS.StrongPersist.H6Aux.Lhat_mem α hα 4 hC.reg hmem5
  have hCorrmem4 : Work.Spaces.HkMem α 4 (Work.FTS.CoercivityFix.Corr α w) :=
    Work.FTS.StrongEps.EpsZero.ClassCHk.HkMem_Corr_of_classC hα hα1 hC
  have hLhatSq4 : Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Lhat w)
      ≤ Cl * Work.Spaces.HkSq α 5 w := hLhat4 α hα w hC.reg hmem5
  have hmono45 : Work.Spaces.HkSq α 4 w ≤ Work.Spaces.HkSq α 5 w :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hmem5
  have hCorrSq4 : Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Corr α w)
      ≤ Kang * Crad * Work.Spaces.HkSq α 5 w := by
    obtain ⟨hint, hbd⟩ := hrad α ⟨hα, hα1⟩ w hC.reg hmem4 hC.l12
    have h1 : Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Corr α w)
        ≤ Kang * (Crad * Work.Spaces.HkSq α 4 w) :=
      (Work.FTS.StrongEps.ClassCRHS.HkSq_Corr_le_classC hα hα1 hKangpos
        (hang α hα hα1) hint).trans (mul_le_mul_of_nonneg_left hbd hKangpos.le)
    refine h1.trans ?_
    rw [show Kang * (Crad * Work.Spaces.HkSq α 4 w)
        = Kang * Crad * Work.Spaces.HkSq α 4 w from by ring]
    exact mul_le_mul_of_nonneg_left hmono45 hKCnn
  have hsum4 : Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α w)
      ≤ 2 * (Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Lhat w)
          + Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Corr α w)) := by
    rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α w]
    exact Work.FTS.GalFields.RHS.HkSq_add_le_open α 4 hα hLhatsm hCorrsm hLhatmem4 hCorrmem4
  have hb4 : Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α w)
      ≤ (2 * Cl + 2 * (Kang * Crad)) * Work.Spaces.HkSq α 5 w := by
    calc Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α w)
        ≤ 2 * (Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Lhat w)
            + Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Corr α w)) := hsum4
      _ ≤ 2 * (Cl * Work.Spaces.HkSq α 5 w
            + Kang * Crad * Work.Spaces.HkSq α 5 w) := by linarith
      _ = (2 * Cl + 2 * (Kang * Crad)) * Work.Spaces.HkSq α 5 w := by ring
  -- ## level 6
  have hLhatmem6 : Work.Spaces.HkMem α 6 (Work.FTS.CoercivityFix.Lhat w) :=
    Work.FTS.StrongPersist.H6Aux.Lhat_mem α hα 6 hC.reg hmem7
  obtain ⟨hCorrmem6, hCorrSq6⟩ := hCorr6 α hα₂ w hH6 hmem7
  have hLhatSq6 : Work.Spaces.HkSq α 6 (Work.FTS.CoercivityFix.Lhat w)
      ≤ Cl6 * Work.Spaces.HkSq α 7 w := hLhat6 α hα w hC.reg hmem7
  have hsum6 : Work.Spaces.HkSq α 6 (Work.Coercivity.LGammaT α w)
      ≤ 2 * (Work.Spaces.HkSq α 6 (Work.FTS.CoercivityFix.Lhat w)
          + Work.Spaces.HkSq α 6 (Work.FTS.CoercivityFix.Corr α w)) := by
    rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α w]
    exact Work.FTS.GalFields.RHS.HkSq_add_le_open α 6 hα hLhatsm hCorrsm hLhatmem6 hCorrmem6
  have hLGmem6 : Work.Spaces.HkMem α 6 (Work.Coercivity.LGammaT α w) := by
    rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α w]
    exact Work.FTS.EllipticEst.RPFresh.HkMem_add_open α 6 hLhatsm hCorrsm hLhatmem6 hCorrmem6
  have hb6 : Work.Spaces.HkSq α 6 (Work.Coercivity.LGammaT α w)
      ≤ (2 * Cl6) * Work.Spaces.HkSq α 7 w + (2 * C6) * Work.Spaces.HkSq α 6 w := by
    linarith
  -- ## the assembly
  set KL : ℝ := 2 * Cl + 2 * (Kang * Crad) + (2 * Cl6 + 2 * C6) + 1 with hKLdef
  have hKLnn : 0 ≤ KL := by rw [hKLdef]; linarith
  have hnn5 : 0 ≤ Work.Spaces.HkSq α 5 w := Work.Spaces.HkSq_nonneg α 5 w
  have hnn6 : 0 ≤ Work.Spaces.HkSq α 6 w := Work.Spaces.HkSq_nonneg α 6 w
  have hnn7 : 0 ≤ Work.Spaces.HkSq α 7 w := Work.Spaces.HkSq_nonneg α 7 w
  have hsq : Work.Spaces.HkSq α 6 w ≤ (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by
    nlinarith [hnn6]
  have hb4' : Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α w)
      ≤ KL * (1 + Work.Spaces.HkSq α 5 w) := by
    have hKL4 : 2 * Cl + 2 * (Kang * Crad) ≤ KL := by rw [hKLdef]; linarith
    calc Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α w)
        ≤ (2 * Cl + 2 * (Kang * Crad)) * Work.Spaces.HkSq α 5 w := hb4
      _ ≤ KL * Work.Spaces.HkSq α 5 w := mul_le_mul_of_nonneg_right hKL4 hnn5
      _ ≤ KL * (1 + Work.Spaces.HkSq α 5 w) :=
          mul_le_mul_of_nonneg_left (by linarith) hKLnn
  have hb6' : Work.Spaces.HkSq α 6 (Work.Coercivity.LGammaT α w)
      ≤ KL * (1 + Work.Spaces.HkSq α 7 w)
        + KL * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by
    have hKL6a : 2 * Cl6 ≤ KL := by rw [hKLdef]; linarith
    have hKL6b : 2 * C6 ≤ KL := by rw [hKLdef]; linarith
    calc Work.Spaces.HkSq α 6 (Work.Coercivity.LGammaT α w)
        ≤ (2 * Cl6) * Work.Spaces.HkSq α 7 w + (2 * C6) * Work.Spaces.HkSq α 6 w := hb6
      _ ≤ KL * Work.Spaces.HkSq α 7 w + KL * Work.Spaces.HkSq α 6 w :=
          add_le_add (mul_le_mul_of_nonneg_right hKL6a hnn7)
            (mul_le_mul_of_nonneg_right hKL6b hnn6)
      _ ≤ KL * (1 + Work.Spaces.HkSq α 7 w) + KL * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by
          have h1 : KL * Work.Spaces.HkSq α 7 w ≤ KL * (1 + Work.Spaces.HkSq α 7 w) :=
            mul_le_mul_of_nonneg_left (by linarith) hKLnn
          have h2 : KL * Work.Spaces.HkSq α 6 w ≤ KL * (1 + Work.Spaces.HkSq α 6 w) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq hKLnn
          linarith
  exact ⟨hLGTsm, hLGmem6, hb4', hb6'⟩

end Work.FTS.StrongEps.E4R3.RawE6Aux
