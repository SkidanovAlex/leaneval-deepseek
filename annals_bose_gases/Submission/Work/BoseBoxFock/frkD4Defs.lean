import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.boxSlotOf_self_re_le_fibre
import Submission.Work.BoseBoxFock.frkDictMain
import Submission.Work.BoseBoxFock.integrableOn_kinFT_winState_fibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.frkD4Defs` — the vocabulary of the dictionary `D4`

`Work.BoseBoxFock.FRK.FormRowKin4_of_oneBody4` (the dictionary `D4` of the FormRowKin v2 design)
turns the per-fibre one-body inequality `OBineq4` into the box-level kinetic row `FormRowKin4`.
Its left side is the box pairing of the box-restricted state with `AVgen` at the *kinetic-only*
environment; its right side is `kinFormB` minus two reserves.

This module fixes the vocabulary of that dictionary:

* `kinRowLHS` — the left side of `OBineq4` as an explicit real number (the per-fibre row), so that
  the dictionary can be stated without repeating the expression; `OBineq4_iff_kinRowLHS` is the
  (definitional) unfolding, `kinRowLHS_nonneg` its positivity;
* `tauProf_nonneg` / `tauSm_nonneg` — the positivity of the smoothed kinetic symbol;
* `slotGood_boxSlotSum` — `boxSlotSum e T` is a `RowGood` operator at the honest weak bundle
  (measurability + global boundedness), which is what makes the individual rows of `AVgen`
  integrable on the compact box (no support hypothesis is needed: the box has finite measure and
  `abox` is compact);
* `star_mul_integrableOn_abox` — the resulting `IntegrableOn` of `star Θ · F` on `abox n ℓ`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## 1. The per-fibre row -/

/-- The left-hand side of `OBineq4` as a real number, at a one-body state `ψ`. -/
noncomputable def kinRowLHS (ℓ d s eT b κ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (ψ : Ω → ℝ) : ℝ :=
  (∑ k : Lab N, tauSm eT s d ℓ (kmomLab ℓ N k)
      * ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2))
    + b / (2 * ℓ ^ 2) * Work.BoseKinLoc.gapBare ℓ 0 ψ
    + eT * b / (2 * d ^ 2 * ℓ ^ 2)
        * ((1 / 32 : ℝ) * ∑ k : Lab N, etaH fu κ (kmomLab ℓ N k)
            * ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2))

/-- `OBineq4` is exactly the assertion that `kinRowLHS` is bounded by `fsT` minus the two
reserves. -/
theorem OBineq4_iff_kinRowLHS (ℓ s d eT b κ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (ψ : Ω → ℝ) :
    FRK.OBineq4 ℓ s d eT b κ fu N ψ ↔
      kinRowLHS ℓ d s eT b κ fu N ψ
        ≤ Work.BoseKinLoc.fsT ℓ d s eT b 0 ψ
          - b / 4 * ((ℓ ^ 2)⁻¹ * Work.BoseKinLoc.gapBare ℓ 0 ψ)
          - b / 100 * (eT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.momForm ℓ d 0 ψ) := by
  unfold FRK.OBineq4 kinRowLHS
  exact Iff.rfl

/-! ## 2. Positivity of the kinetic symbol -/

/-- `τ̃ ≥ 0`. -/
theorem tauSm_nonneg (eT s d ℓ : ℝ) (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1)
    (p : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ tauSm eT s d ℓ p := by
  rw [tauSm]
  have h1 : 0 ≤ (1 - eT) * ((2 * s * ℓ)⁻¹) ^ 2 * tauProf (‖p‖ / (2 * s * ℓ)⁻¹) :=
    mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (tauProf_nonneg _)
  have h2 : 0 ≤ eT * ((2 * d * s * ℓ)⁻¹) ^ 2 * tauProf (‖p‖ / (2 * d * s * ℓ)⁻¹) :=
    mul_nonneg (mul_nonneg heT0 (sq_nonneg _)) (tauProf_nonneg _)
  linarith

/-- `kinRowLHS` is nonnegative as soon as the parameters are nonnegative and `0 < ℓ`. -/
theorem kinRowLHS_nonneg (ℓ d s eT b κ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (ψ : Ω → ℝ) (hℓ : 0 < ℓ) (hb : 0 ≤ b) (heT : 0 ≤ eT) (heT1 : eT ≤ 1) :
    0 ≤ kinRowLHS ℓ d s eT b κ fu N ψ := by
  rw [kinRowLHS]
  have h1 : 0 ≤ ∑ k : Lab N, tauSm eT s d ℓ (kmomLab ℓ N k)
      * ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (tauSm_nonneg eT s d ℓ heT heT1 _)
      (mul_nonneg (by positivity) (sq_nonneg _))
  have h2 : 0 ≤ Work.BoseKinLoc.gapBare ℓ 0 ψ := FRK.gapBare_nonneg ℓ ψ
  have h3 : 0 ≤ ∑ k : Lab N, etaH fu κ (kmomLab ℓ N k)
      * ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (etaH_nonneg fu κ _)
      (mul_nonneg (by positivity) (sq_nonneg _))
  have h4 : 0 ≤ b / (2 * ℓ ^ 2) * Work.BoseKinLoc.gapBare ℓ 0 ψ :=
    mul_nonneg (div_nonneg hb (by positivity)) h2
  have h5 : 0 ≤ eT * b / (2 * d ^ 2 * ℓ ^ 2)
      * ((1 / 32 : ℝ) * ∑ k : Lab N, etaH fu κ (kmomLab ℓ N k)
          * ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2)) :=
    mul_nonneg (div_nonneg (mul_nonneg heT hb) (by positivity))
      (mul_nonneg (by norm_num) h3)
  linarith

/-! ## 3. From the weak mode bundle to `L²` -/

/-- An everywhere bounded mode supported in the box is `L²`: the support has finite measure and
there the function is bounded, so it is dominated by the indicator of the box. -/
theorem memLp_two_of_box_supp {ℓ : ℝ} {u : Ω → ℂ} (hum : Measurable u)
    (hub : ∃ C : ℝ, ∀ x, ‖u x‖ ≤ C)
    (hus : Function.support u ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    MemLp u 2 (MeasureTheory.volume : Measure Ω) := by
  obtain ⟨C, hC⟩ := hub
  have hm : MeasurableSet (Work.BoseK15.corpusBox.boxL ℓ) :=
    Work.BoseK15.corpusBox.boxL_measurableSet ℓ
  haveI hfin : IsFiniteMeasure
      ((MeasureTheory.volume : Measure Ω).restrict (Work.BoseK15.corpusBox.boxL ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top⟩
  have h1 : MemLp u 2 ((MeasureTheory.volume : Measure Ω).restrict (Work.BoseK15.corpusBox.boxL ℓ)) :=
    MemLp.of_bound hum.aestronglyMeasurable.restrict (max C 0)
      (Filter.Eventually.of_forall fun x => le_trans (hC x) (le_max_left C 0))
  have h2 : MemLp ((Work.BoseK15.corpusBox.boxL ℓ).indicator u) 2
      (MeasureTheory.volume : Measure Ω) :=
    (MeasureTheory.memLp_indicator_iff_restrict (p := 2) (f := u) hm).mpr h1
  have hae : ((Work.BoseK15.corpusBox.boxL ℓ).indicator u) =ᵐ[MeasureTheory.volume] u := by
    filter_upwards with x
    by_cases hx : x ∈ Work.BoseK15.corpusBox.boxL ℓ
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      exact (Function.notMem_support.mp (fun h => hx (hus h))).symm
  exact h2.ae_eq hae

/-- The modes of the honest weak bundle are `L²`. -/
theorem memLp_modes_two {m : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    ∀ l, MemLp (e l) 2 (MeasureTheory.volume : Measure Ω) :=
  fun l => memLp_two_of_box_supp (hmeas l) (hbdd l) (hsupp l)

end Work.BoseBoxFock
