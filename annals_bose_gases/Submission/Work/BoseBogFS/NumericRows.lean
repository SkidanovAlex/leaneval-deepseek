import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.SharpSlots
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.NumericRows` — the gate rows that `BogNumeric` already implies

Several slots of the capstone `SharpCap.bogOpBoundAtFSWith_of_sharpData` are *consequences*
of the gate row `hnum : BogNumeric F E ρ` (plus `hDsup`/`hbigM`), because the two-mode
algebra of `Submission/Bog2Mode.lean` gives them for free:

* `bogAlpha_sq_le_one_of_numeric` — the slot `hα : (α_k)² ≤ 1`: `α = ℬ/(𝒜+√(𝒜²−ℬ²))` and
  `|ℬ| ≤ 𝒜` give `|α| ≤ 1` (the squeezing parameter is sub-unit); this **removes `hα` from
  the interface**;
* `bogD_nonneg_of_numeric` — `𝒟 = (𝒜+√(𝒜²−ℬ²))/2 ≥ 0`, hence `G` may be taken to be the
  defining sum `Σ_{RHi}𝒟_kγ_k²` with `hG : … ≤ G` *reflexive* and `hG0 : 0 ≤ G` free
  (`sum_RHi_bogD_mul_gammaSq_nonneg`);
* `zpKapSum_nonneg` — `zpKapSum = Σ_k ½(bogZeroPoint + bogKappaErr) ≥ 0` (both summands are
  nonnegative under the gate), hence `winKbar_add_zpKapSum_pos` **removes `hSpos`** given
  `hDsup` and `hbigM`;
* `bogZeroPoint_nonneg_of_numeric`, `bogKappaErr_nonneg_of_numeric` — the two summands.

This module is the chapter's own arithmetic; the remaining view-facing rows (`hγ`, `hδ`,
`hwinG`, `hwinGS`) are the χ̂-decay/localisation rows of the GATE/ESTIMATES side.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR Work.BoseB7 Work.BoseB6Est

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- `𝒟_k = (𝒜_k+√(𝒜_k²−ℬ_k²))/2 ≥ 0` under the gate row. -/
theorem bogD_nonneg_of_numeric {F : FockData Mode} {E : Q3Env Mode} {ρ : ℝ}
    (hnum : BogNumeric F E ρ) (k : Mode) : 0 ≤ bogD E ρ k := by
  have := (Submission.BoseGases.bogD_pos (hnum.hA k) (hnum.hB k)).le
  simpa only [bogD] using this

/-- **The squeezing parameter is sub-unit**: `α_k² ≤ 1` under the gate row.  This is the
slot `hα` of the capstone, vacuous to state separately. -/
theorem bogAlpha_sq_le_one_of_numeric {F : FockData Mode} {E : Q3Env Mode} {ρ : ℝ}
    (hnum : BogNumeric F E ρ) (k : Mode) : (bogAlpha E ρ k) ^ 2 ≤ 1 := by
  have hA : 0 < bogA E ρ k := hnum.hA k
  have hB : |bogB E ρ k| ≤ bogA E ρ k := hnum.hB k
  have hs : 0 ≤ Submission.BoseGases.bogS (bogA E ρ k) (bogB E ρ k) :=
    Submission.BoseGases.bogS_nonneg _ _
  have hden : 0 < bogA E ρ k + Submission.BoseGases.bogS (bogA E ρ k) (bogB E ρ k) := by
    linarith
  have hle : |bogB E ρ k| ≤ bogA E ρ k + Submission.BoseGases.bogS (bogA E ρ k) (bogB E ρ k) := by
    linarith
  have habs : |bogAlpha E ρ k| ≤ 1 := by
    rw [bogAlpha, Submission.BoseGases.bogAlpha, abs_div, abs_of_pos hden, div_le_one hden]
    exact hle
  calc (bogAlpha E ρ k) ^ 2 = |bogAlpha E ρ k| ^ 2 := (sq_abs _).symm
    _ ≤ 1 ^ 2 := by
        exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = 1 := by norm_num

/-- `bogZeroPoint 𝒜 ℬ = 𝒜 − √(𝒜²−ℬ²) ≥ 0` under the gate row. -/
theorem bogZeroPoint_nonneg_of_numeric {F : FockData Mode} {E : Q3Env Mode} {ρ : ℝ}
    (hnum : BogNumeric F E ρ) (k : Mode) :
    0 ≤ Work.BoseB6.bogZeroPoint (bogA E ρ k) (bogB E ρ k) := by
  have hA : 0 < bogA E ρ k := hnum.hA k
  have hB : |bogB E ρ k| ≤ bogA E ρ k := hnum.hB k
  have hle := Submission.BoseGases.bogS_sq_le hA.le hB
  rw [Work.BoseB6.bogZeroPoint]
  have hdef : Real.sqrt ((bogA E ρ k) ^ 2 - (bogB E ρ k) ^ 2)
      = Submission.BoseGases.bogS (bogA E ρ k) (bogB E ρ k) := rfl
  rw [hdef]
  linarith

/-- `bogKappaErr 𝒜 ℬ 𝒞 = 2𝒞²/(𝒜+ℬ) ≥ 0` under the gate rows `0 < 𝒜+ℬ`. -/
theorem bogKappaErr_nonneg_of_numeric {F : FockData Mode} {E : Q3Env Mode} {ρ : ℝ}
    (hnum : BogNumeric F E ρ) (k : Mode) :
    0 ≤ Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k) := by
  rw [Work.BoseB6.bogKappaErr]
  exact div_nonneg (by positivity) (hnum.hAB k).le

/-- **`zpKapSum ≥ 0`** under the gate row (both summands are nonnegative). -/
theorem zpKapSum_nonneg {F : FockData Mode} {E : Q3Env Mode} {ρ : ℝ}
    (hnum : BogNumeric F E ρ) : 0 ≤ zpKapSum E ρ := by
  rw [zpKapSum]
  refine Finset.sum_nonneg fun k _ => ?_
  have h1 := bogZeroPoint_nonneg_of_numeric hnum k
  have h2 := bogKappaErr_nonneg_of_numeric hnum k
  linarith

/-- **`Σ_{RHi} 𝒟_kγ_k² ≥ 0`** — so the caller may take `G μ ρ` to *be* that sum, making the
slots `hG` (reflexive) and `hG0` free. -/
theorem sum_RHi_bogD_mul_gammaSq_nonneg {F : FockData Mode} {E : Q3Env Mode} {ρ : ℝ}
    (hnum : BogNumeric F E ρ) :
    0 ≤ ∑ k ∈ (Work.BoseB7.excited Mode).filter (RHi F (KzEnvAt E ρ)),
      (bogD E ρ k) * (bogGamma E ρ k) ^ 2 := by
  refine Finset.sum_nonneg fun k _ => ?_
  exact mul_nonneg (bogD_nonneg_of_numeric hnum k) (sq_nonneg _)

/-- `Dsup ≥ 0` whenever it dominates `𝒟` (which is `≥ 0`). -/
theorem Dsup_nonneg_of_numeric {F : FockData Mode} {E : Q3Env Mode} {ρ Dsup : ℝ}
    (hnum : BogNumeric F E ρ) (hDsup : ∀ k : Mode, bogD E ρ k ≤ Dsup) : 0 ≤ Dsup := by
  obtain ⟨k⟩ := (inferInstance : Nonempty Mode)
  exact le_trans (bogD_nonneg_of_numeric hnum k) (hDsup k)

/-- **`winKbar E Dsup > 0`** given the gate row, `hDsup` and `0 ≤ E.bigM`. -/
theorem winKbar_pos_of_numeric {F : FockData Mode} {E : Q3Env Mode} {ρ Dsup : ℝ}
    (hnum : BogNumeric F E ρ) (hDsup : ∀ k : Mode, bogD E ρ k ≤ Dsup) (hbigM : 0 ≤ E.bigM) :
    0 < winKbar E Dsup := by
  have h1 : 0 ≤ Dsup := Dsup_nonneg_of_numeric hnum hDsup
  have h2 : (0 : ℝ) ≤ (Fintype.card Mode : ℝ) := by positivity
  have h3 : (0 : ℝ) ≤ 600 * E.bigM + 32 * (Fintype.card Mode : ℝ) + 32 := by linarith
  rw [winKbar]
  have h4 : 0 ≤ Dsup * (600 * E.bigM + 32 * (Fintype.card Mode : ℝ) + 32) :=
    mul_nonneg h1 h3
  linarith

/-- **The slot `hSpos` of the capstone, discharged.**  `winKbar + zpKapSum > 0` from the gate
row, `hDsup` and `0 ≤ E.bigM` — no separate hypothesis is needed. -/
theorem winKbar_add_zpKapSum_pos {F : FockData Mode} {E : Q3Env Mode} {ρ Dsup : ℝ}
    (hnum : BogNumeric F E ρ) (hDsup : ∀ k : Mode, bogD E ρ k ≤ Dsup) (hbigM : 0 ≤ E.bigM) :
    0 < winKbar E Dsup + zpKapSum E ρ :=
  lt_of_lt_of_le (winKbar_pos_of_numeric hnum hDsup hbigM)
    (le_add_of_nonneg_right (zpKapSum_nonneg hnum))

end Work.BoseBogFS
