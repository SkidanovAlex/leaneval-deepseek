import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.Sum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.Reserve` — the diagonal reserve

FS `eq:BogHamDiag`/`eq:Q3Cancels` keep the diagonal `Σ_k 𝒟_k b_k†b_k` with FS's
`b_k = a_k + α_ka_{-k}† + c_k` (`eq:Defb_k`, the `c`-number shift *inside* — this is what
`Work.BoseB7.FockData.dNumOpR`, which uses the unshifted `b_k`, does not do).
`qwen_dNumOpShifted_le` shows that this shifted diagonal on the region `RHi` is dominated
by `𝒦^Bog = KzBogFS` plus the scalar `Σ_k ½(𝒵_k+κ_k)`, so the design's reserve
(`dNumOpR` on `RHi`) is paid by `𝒦^Bog` up to that scalar.

## Contents

* `qw_dNumOpShifted_eq` — the value of the reserve;
* `qw_KzBogFS_eq` — the value of `𝒦^Bog` in diagonalised form;
* `qw_dNumOpShifted_le` — the reserve inequality.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseBogFS

open Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- The diagonal coefficient is even: `𝒟_{−k} = 𝒟_k`. -/
theorem bogD_even (E : Q3Env Mode) (ρ : ℝ)
    (hAe : ∀ k, bogA E ρ k = bogA E ρ (-k)) (hBe : ∀ k, bogB E ρ k = bogB E ρ (-k))
    (k : Mode) : bogD E ρ (-k) = bogD E ρ k := by
  simp only [bogD, hAe k, hBe k]

/-- `𝒟α²[a_k,a_k†]-type term ≤ the zero point`: `𝒟_kα_k²·ccr2_k ≤ 𝒵_k` whenever
`ccr2_k ≤ 2`. -/
theorem bogD_alpha_sq_ccr_le (E : Q3Env Mode) (ρ : ℝ) (k : Mode) (F : FockData Mode)
    (hA : 0 < bogA E ρ k) (hB : |bogB E ρ k| ≤ bogA E ρ k)
    (hccr : bogCcr2 F k ≤ 2) :
    bogD E ρ k * (bogAlpha E ρ k) ^ 2 * bogCcr2 F k
      ≤ Work.BoseB6.bogZeroPoint (bogA E ρ k) (bogB E ρ k) := by
  have hDnn : 0 ≤ bogD E ρ k := by
    simp only [bogD]
    exact le_of_lt (Submission.BoseGases.bogD_pos (A := bogA E ρ k) (B := bogB E ρ k) hA hB)
  have hα2 : 0 ≤ bogD E ρ k * (bogAlpha E ρ k) ^ 2 := mul_nonneg hDnn (sq_nonneg _)
  have hzp : 2 * (bogD E ρ k * (bogAlpha E ρ k) ^ 2)
      = Work.BoseB6.bogZeroPoint (bogA E ρ k) (bogB E ρ k) := by
    simpa only [bogD, bogAlpha, bogA, bogB] using
      two_mul_bogD_mul_alpha_sq (bogA E ρ k) (bogB E ρ k) hA hB
  have h := mul_le_mul_of_nonneg_left hccr hα2
  linarith [hzp]

/-- The value of the shifted diagonal reserve on a region. -/
theorem qw_dNumOpShifted_eq (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (s : Finset Mode)
    (f : F.H) :
    F.qw f (∑ k ∈ s, (bogD E ρ k) • ((bogBShiftDag F E ρ k) ∘ₗ (bogBShift F E ρ k)))
      = ∑ k ∈ s, (bogD E ρ k) * F.normSq ((bogBShift F E ρ k) f) := by
  rw [qw_sum_finset F s (fun k => bogD E ρ k)
    (fun k => (bogBShiftDag F E ρ k) ∘ₗ (bogBShift F E ρ k)) f]
  exact Finset.sum_congr rfl fun k _ => by
    rw [FockData.qw, LinearMap.comp_apply, bp_bogBShiftDag_bogBShift, FockData.normSq]

/-- The value of `𝒦^Bog` (`KzBogFS`) in diagonalised form: the diagonal minus the sum of
the zero points and `κ`-errors. -/
theorem qw_KzBogFS_eq (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (f : F.H)
    (hA : ∀ k, 0 < bogA E ρ k) (hB : ∀ k, |bogB E ρ k| ≤ bogA E ρ k)
    (hAB : ∀ k, 0 < bogA E ρ k + bogB E ρ k)
    (hAe : ∀ k, bogA E ρ k = bogA E ρ (-k)) (hBe : ∀ k, bogB E ρ k = bogB E ρ (-k))
    (hCe : ∀ k, bogC E ρ k = bogC E ρ (-k)) :
    F.qw f (KzBogFS F E ρ)
      = (∑ k : Mode, (bogD E ρ k) * F.normSq ((bogBShift F E ρ k) f))
        - (∑ k : Mode, (1 / 2 : ℝ) * ((bogD E ρ k) * (bogAlpha E ρ k) ^ 2 * bogCcr2 F k
            + Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k)))
          * F.normSq f := by
  have hterm : ∀ k : Mode, F.qw f (bogPairOp F E ρ k)
      = (bogD E ρ k) * F.normSq ((bogBShift F E ρ k) f)
        + (bogD E ρ k) * F.normSq ((bogBShift F E ρ (-k)) f)
        - ((bogD E ρ k) * (bogAlpha E ρ k) ^ 2 * bogCcr2 F k
            + Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k))
          * F.normSq f := by
    intro k
    rw [qw_bogPairOp_eq F E ρ k (hA k) (hB k) (hAB k) (hAe k).symm (hBe k).symm (hCe k).symm f]
    ring
  have hre : (∑ k : Mode, (bogD E ρ k) * F.normSq ((bogBShift F E ρ (-k)) f))
      = ∑ k : Mode, (bogD E ρ k) * F.normSq ((bogBShift F E ρ k) f) := by
    rw [← sum_neg_index
      (fun u : Mode => (bogD E ρ u) * F.normSq ((bogBShift F E ρ (-u)) f))]
    exact Finset.sum_congr rfl fun k _ => by
      simp only [bogD_even E ρ hAe hBe k, neg_neg]
  rw [KzBogFS_eq_sum, qw_sum]
  rw [show (∑ k : Mode, (1 / 2 : ℝ) * F.qw f (bogPairOp F E ρ k))
      = ∑ k : Mode, (1 / 2 : ℝ) * ((bogD E ρ k) * F.normSq ((bogBShift F E ρ k) f)
          + (bogD E ρ k) * F.normSq ((bogBShift F E ρ (-k)) f)
          - ((bogD E ρ k) * (bogAlpha E ρ k) ^ 2 * bogCcr2 F k
              + Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k)) * F.normSq f)
      from Finset.sum_congr rfl fun k _ => by rw [hterm k]]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hre]
  rw [← Finset.mul_sum]
  ring

/-- **The diagonal reserve is dominated by `𝒦^Bog`.**  For every state `f`, the shifted
diagonal `Σ_{k∈RHi} 𝒟_k(b_k+c_k)†(b_k+c_k)` is at most `⟨f, 𝒦^Bog f⟩` plus the scalar
`Σ_k ½(𝒵_k+κ_k)·‖f‖²`. -/
theorem qw_dNumOpShifted_le (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (f : F.H)
    (hA : ∀ k, 0 < bogA E ρ k) (hB : ∀ k, |bogB E ρ k| ≤ bogA E ρ k)
    (hAB : ∀ k, 0 < bogA E ρ k + bogB E ρ k)
    (hAe : ∀ k, bogA E ρ k = bogA E ρ (-k)) (hBe : ∀ k, bogB E ρ k = bogB E ρ (-k))
    (hCe : ∀ k, bogC E ρ k = bogC E ρ (-k))
    (hccr : ∀ k, bogCcr2 F k ≤ 2) :
    F.qw f (dNumOpShifted F E ρ (RHi F (Work.BoseFixR.KzEnvAt E ρ)))
      ≤ F.qw f (KzBogFS F E ρ)
        + (∑ k : Mode, (1 / 2 : ℝ) * (Work.BoseB6.bogZeroPoint (bogA E ρ k) (bogB E ρ k)
            + Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k)))
          * F.normSq f := by
  have hDnn : ∀ k : Mode, 0 ≤ bogD E ρ k := fun k => by
    simp only [bogD]
    exact le_of_lt (Submission.BoseGases.bogD_pos (A := bogA E ρ k) (B := bogB E ρ k)
      (hA k) (hB k))
  have hsub : (∑ k ∈ (Work.BoseB7.excited Mode).filter (RHi F (Work.BoseFixR.KzEnvAt E ρ)),
        (bogD E ρ k) * F.normSq ((bogBShift F E ρ k) f))
      ≤ ∑ k : Mode, (bogD E ρ k) * F.normSq ((bogBShift F E ρ k) f) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      ((Finset.filter_subset _ _).trans (Finset.subset_univ _))
      (fun k _ _ => mul_nonneg (hDnn k) (F.bp_nonneg _))
  have hcost : (∑ k : Mode, (1 / 2 : ℝ) * ((bogD E ρ k) * (bogAlpha E ρ k) ^ 2 * bogCcr2 F k
        + Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k)))
      ≤ ∑ k : Mode, (1 / 2 : ℝ) * (Work.BoseB6.bogZeroPoint (bogA E ρ k) (bogB E ρ k)
        + Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k)) :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
      (add_le_add (bogD_alpha_sq_ccr_le E ρ k F (hA k) (hB k) (hccr k)) le_rfl) (by norm_num)
  have hd := qw_dNumOpShifted_eq F E ρ
    ((Work.BoseB7.excited Mode).filter (RHi F (Work.BoseFixR.KzEnvAt E ρ))) f
  have hk := qw_KzBogFS_eq F E ρ f hA hB hAB hAe hBe hCe
  simp only [dNumOpShifted]
  rw [hd, hk]
  have hnn : 0 ≤ F.normSq f := F.bp_nonneg f
  nlinarith [hsub, hcost, hnn]

end Work.BoseBogFS
