import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BSKinetic.cnPlus_eq_slotSum
import Submission.Work.BSKinetic.familyForm_zero_eq
import Submission.Work.BSKinetic.locKinEnWordBox_of_familyBound
import Submission.Work.BSKinetic.tBwordBInd_slotSwap_and_integrable
import Submission.Work.OneBodyKin.Phi_far_nonneg
import Submission.Work.OneBodyKin.SecondOrder.boxHat_one_sub_sq_le
import Submission.Work.OneBodyKin.SecondOrder.symA_zero_small
import Submission.Work.OneBodyKin.SecondOrder.symD_diff_bound_uniform
import Submission.Work.OneBodyKin.SecondOrder.symD_fsKinCoeff_small
import Submission.Work.OneBodyKin.SymBound_iff_SymBoundOne
import Submission.Work.OneBodyKin.SymbolIntegral_fsKinCoeff
import Submission.Work.OneBodyKin.dSpace_eq_fourier
import Submission.Work.OneBodyKin.integrable_fsKinCoeff_shift_mul_profHat_sq
import Submission.Work.OneBodyKin.symA_fsKinCoeff_far_le
import Submission.Work.OneBodyKin.symD_second_order
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.symA_fsKinCoeff_mix` — the two-cut mixture bound for the unprojected symbol

The unprojected symbol of the sliding family at scale `ℓ = 1` is

    `symA 1 F ρ = (2π)⁻³ ∫_p F ‖ρ + p‖ · profHat(p)² dp`

(`Work.OneBodyKin.Defs`), and for the FS cut-off `F = fsKinCoeff c = [·−c]₊²` we write

    `φ(c) := symA 1 (fsKinCoeff c) 0 = (2π)⁻³ ∫_p [‖p‖ − c]₊² profHat(p)² dp`.

With `M₁ := (2π)⁻³ ∫ profHat²·‖t‖`, `M₂ := (2π)⁻³ ∫ profHat²·‖t‖²` (the first two moments of
the squared bump profile) the statement is

    `symA 1 (fsKinCoeff C) ρ ≤ (1−ε)·[‖ρ‖ − dC/2]₊² + ε·[‖ρ‖ − C/2]₊² + β`

under the hypotheses `0 < C`, `0 ≤ d ≤ 1/2`, `0 ≤ ε ≤ 1/2`, the monotonicity-of-cut-off
inequality `hnear : symA 1 (fsKinCoeff C) ρ ≤ φ(C − ‖ρ‖)`, the moment bounds `M₁ ≤ C`,
`8M₂ ≤ (1−d)²C²` and `htail : φ(C/2) ≤ β`.

## Proof (three regions in `t = ‖ρ‖`)

* `t ≤ C/2`: `hnear` gives `symA ≤ φ(C − t) ≤ φ(C/2) ≤ β` (antitone cut-off), and the right
  side is `≥ β` because both mixture terms are nonnegative.
* `C/2 < t ≤ C`: still `≤ φ(C − t) ≤ M₂` (the cut-off `C − t ≥ 0` is subtracted from `‖p‖`),
  while `M₂ ≤ (1−d)²C²/8 ≤ (1−ε)(t − dC/2)²` because `t − dC/2 ≥ C(1−d)/2`.
* `C < t`: with `L := t − C ≥ 0` the far-regime bound `symA_fsKinCoeff_far_le` gives
  `symA ≤ L² + 2L·M₁ + M₂`, and the right side expands into
  `L² + 2L((1−ε)(C − dC/2) + εC/2) + ((1−ε)(C − dC/2)² + εC²/4) + β`; the two comparisons
  `M₁ ≤ (1−ε)(C − dC/2) + εC/2` and `M₂ ≤ (1−ε)(C − dC/2)² + εC²/4 + β` are exactly the
  content of the moment hypotheses.

The first moment is controlled by the second through the elementary (AM–GM/Young) inequality
`x ≤ a + x²/(4a)`, giving `M₁ ≤ 3(1−d)C/8` — comfortably below the budget
`(1−ε)(C−dC/2) + εC/2 ≥ C(3−d)/4` of the mixture.
-/

namespace Work.BoseFixB1

noncomputable section

open MeasureTheory
open scoped Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## 0. The two moments of the bump profile -/

/-- The first moment `M₁ = (2π)⁻³ ∫ profHat(t)² ‖t‖ dt` of the squared bump profile. -/
private noncomputable def M1 : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ t : ℝ³, (Work.OneBodyKin.profHat t) ^ 2 * ‖t‖

/-- The second moment `M₂ = (2π)⁻³ ∫ profHat(t)² ‖t‖² dt` of the squared bump profile. -/
private noncomputable def M2 : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ t : ℝ³, (Work.OneBodyKin.profHat t) ^ 2 * ‖t‖ ^ 2

private lemma M2_nonneg : 0 ≤ M2 := by
  rw [M2]
  exact mul_nonneg (by positivity)
    (integral_nonneg (fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _)))

private lemma integrable_profHat_sq :
    Integrable (fun p : ℝ³ => (Work.OneBodyKin.profHat p) ^ 2) := by
  have h := Work.OneBodyKin.integrable_profHat_sq_mul_norm_pow 0 (by norm_num)
  simpa using h

private lemma integrable_profHat_sq_norm :
    Integrable (fun p : ℝ³ => (Work.OneBodyKin.profHat p) ^ 2 * ‖p‖) := by
  have h := Work.OneBodyKin.integrable_profHat_sq_mul_norm_pow 1 (by norm_num)
  simpa using h

private lemma integrable_profHat_sq_norm_sq :
    Integrable (fun p : ℝ³ => (Work.OneBodyKin.profHat p) ^ 2 * ‖p‖ ^ 2) :=
  Work.OneBodyKin.integrable_profHat_sq_mul_norm_pow 2 le_rfl

private lemma profHat_sq_integral_eq :
    (∫ p : ℝ³, (Work.OneBodyKin.profHat p) ^ 2) = (2 * Real.pi) ^ 3 :=
  Work.OneBodyKin.profHat_sq_integral

/-! ## 1. Elementary properties of the cut-off `fsKinCoeff` -/

/-- `fsKinCoeff c r = (r − c)²` once `c ≤ r`. -/
private lemma fsKinCoeff_eq_of_le {c r : ℝ} (h : c ≤ r) :
    Submission.BoseGases.fsKinCoeff c r = (r - c) ^ 2 := by
  unfold Submission.BoseGases.fsKinCoeff
  rw [max_eq_left (by linarith)]

/-- `fsKinCoeff c r ≤ r²` for `0 ≤ c`, `0 ≤ r`. -/
private lemma fsKinCoeff_le_sq (c r : ℝ) (hc : 0 ≤ c) (hr : 0 ≤ r) :
    Submission.BoseGases.fsKinCoeff c r ≤ r ^ 2 := by
  unfold Submission.BoseGases.fsKinCoeff
  refine pow_le_pow_left₀ (le_max_right _ _) (max_le ?_ ?_) 2
  · linarith
  · exact hr

/-- `fsKinCoeff` is antitone in the cut-off. -/
private lemma fsKinCoeff_anti {c₁ c₂ : ℝ} (h : c₁ ≤ c₂) (r : ℝ) :
    Submission.BoseGases.fsKinCoeff c₂ r ≤ Submission.BoseGases.fsKinCoeff c₁ r := by
  unfold Submission.BoseGases.fsKinCoeff
  refine pow_le_pow_left₀ (le_max_right _ _) (max_le ?_ ?_) 2
  · exact le_trans (by linarith : r - c₂ ≤ r - c₁) (le_max_left _ _)
  · exact le_max_right _ _

private lemma continuous_fsKinCoeff (c : ℝ) :
    Continuous (fun x : ℝ => Submission.BoseGases.fsKinCoeff c x) := by
  unfold Submission.BoseGases.fsKinCoeff
  exact ((continuous_id.sub continuous_const).max continuous_const).pow 2

/-- Integrability of `fsKinCoeff c ‖p‖ · profHat(p)²` for a nonnegative cut-off (`c ≥ 0`): it is
dominated by `profHat(p)² ‖p‖²`. -/
private lemma integrable_fsKinCoeff_mul_profHat_sq {c : ℝ} (hc : 0 ≤ c) :
    Integrable (fun p : ℝ³ =>
      Submission.BoseGases.fsKinCoeff c ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2) := by
  refine integrable_profHat_sq_norm_sq.mono' ?_ ?_
  · exact (((continuous_fsKinCoeff c).comp continuous_norm).mul
      (Work.OneBodyKin.continuous_profHat.pow 2)).aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_of_nonneg
      (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _))]
    calc Submission.BoseGases.fsKinCoeff c ‖p‖ * Work.OneBodyKin.profHat p ^ 2
        ≤ ‖p‖ ^ 2 * Work.OneBodyKin.profHat p ^ 2 :=
          mul_le_mul_of_nonneg_right (fsKinCoeff_le_sq c ‖p‖ hc (norm_nonneg p)) (sq_nonneg _)
      _ = Work.OneBodyKin.profHat p ^ 2 * ‖p‖ ^ 2 := by ring

/-! ## 2. The symbol at `q = 0` as an integral, with monotonicity in the cut-off -/

private lemma symA_one_zero_eq (c : ℝ) :
    Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff c) 0
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³,
          Submission.BoseGases.fsKinCoeff c ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2 := by
  rw [show Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff c) 0
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³,
          Submission.BoseGases.fsKinCoeff c ‖0 + p‖ * (Work.OneBodyKin.profHat p) ^ 2 from by
    simp only [Work.OneBodyKin.symA, inv_one, one_smul]]
  simp only [zero_add]

/-- The symbol at `q = 0` is antitone in the cut-off. -/
private lemma symA_zero_anti {c₁ c₂ : ℝ} (h₁ : 0 ≤ c₁) (h : c₁ ≤ c₂) :
    Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff c₂) 0
      ≤ Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff c₁) 0 := by
  have h₂ : 0 ≤ c₂ := le_trans h₁ h
  rw [symA_one_zero_eq c₂, symA_one_zero_eq c₁]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact integral_mono (integrable_fsKinCoeff_mul_profHat_sq h₂)
    (integrable_fsKinCoeff_mul_profHat_sq h₁)
    (fun p => mul_le_mul_of_nonneg_right (fsKinCoeff_anti h ‖p‖) (sq_nonneg _))

/-- The symbol at `q = 0` at a nonnegative cut-off is at most the second moment `M₂`. -/
private lemma symA_zero_le_M2 {c : ℝ} (hc : 0 ≤ c) :
    Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff c) 0 ≤ M2 := by
  rw [symA_one_zero_eq c, M2]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine integral_mono (integrable_fsKinCoeff_mul_profHat_sq hc)
    integrable_profHat_sq_norm_sq (fun p => ?_)
  calc Submission.BoseGases.fsKinCoeff c ‖p‖ * Work.OneBodyKin.profHat p ^ 2
      ≤ ‖p‖ ^ 2 * Work.OneBodyKin.profHat p ^ 2 :=
        mul_le_mul_of_nonneg_right (fsKinCoeff_le_sq c ‖p‖ hc (norm_nonneg p)) (sq_nonneg _)
    _ = Work.OneBodyKin.profHat p ^ 2 * ‖p‖ ^ 2 := by ring

/-! ## 3. The first moment is controlled by the second -/

/-- **The Young/AM–GM bound on the first moment.**  From `8M₂ ≤ (1−d)²C²` we get
`M₁ ≤ 3(1−d)C/8`: the pointwise inequality `‖p‖ ≤ a + ‖p‖²/(4a)` with `a = (1−d)C/4` gives
`M₁ ≤ a + M₂/(4a) ≤ (1−d)C/4 + (1−d)C/8`. -/
private lemma M1_le_three_eighths {C d : ℝ} (hC : 0 < C) (hd0 : 0 ≤ d) (hd : d ≤ 1 / 2)
    (hM2 : 8 * M2 ≤ (1 - d) ^ 2 * C ^ 2) : M1 ≤ 3 * (1 - d) * C / 8 := by
  set a : ℝ := (1 - d) * C / 4 with ha
  have h1d : 0 < 1 - d := by linarith
  have ha_pos : 0 < a := by rw [ha]; positivity
  have h4a : 0 < 4 * a := by linarith
  have h4a_ne : 4 * a ≠ 0 := ne_of_gt h4a
  -- the pointwise Young inequality
  have hpt : ∀ p : ℝ³, ‖p‖ ≤ a + ‖p‖ ^ 2 / (4 * a) := by
    intro p
    have hcancel : 4 * a * (‖p‖ ^ 2 / (4 * a)) = ‖p‖ ^ 2 := by
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ h4a_ne]
    have hexp : 4 * a * (a + ‖p‖ ^ 2 / (4 * a)) = 4 * a ^ 2 + ‖p‖ ^ 2 := by
      rw [mul_add, hcancel]; ring
    have hkey : 4 * a * ‖p‖ ≤ 4 * a * (a + ‖p‖ ^ 2 / (4 * a)) := by
      rw [hexp]
      nlinarith [sq_nonneg (‖p‖ - 2 * a)]
    exact le_of_mul_le_mul_left hkey h4a
  -- the majorant is a linear combination of the two integrable pieces
  have hmaj_eq : (fun p : ℝ³ => (Work.OneBodyKin.profHat p) ^ 2 * (a + ‖p‖ ^ 2 / (4 * a)))
      = fun p : ℝ³ => a * (Work.OneBodyKin.profHat p) ^ 2
          + (1 / (4 * a)) * ((Work.OneBodyKin.profHat p) ^ 2 * ‖p‖ ^ 2) := by
    funext p; ring
  have hmaj_int : Integrable
      (fun p : ℝ³ => (Work.OneBodyKin.profHat p) ^ 2 * (a + ‖p‖ ^ 2 / (4 * a))) := by
    rw [hmaj_eq]
    exact (integrable_profHat_sq.const_mul a).add
      (integrable_profHat_sq_norm_sq.const_mul (1 / (4 * a)))
  -- comparison of integrals
  have hcomp : (∫ p : ℝ³, (Work.OneBodyKin.profHat p) ^ 2 * ‖p‖)
      ≤ ∫ p : ℝ³, (Work.OneBodyKin.profHat p) ^ 2 * (a + ‖p‖ ^ 2 / (4 * a)) :=
    integral_mono integrable_profHat_sq_norm hmaj_int
      (fun p => mul_le_mul_of_nonneg_left (hpt p) (sq_nonneg _))
  have hval : (∫ p : ℝ³, (Work.OneBodyKin.profHat p) ^ 2 * (a + ‖p‖ ^ 2 / (4 * a)))
      = a * (2 * Real.pi) ^ 3
        + (1 / (4 * a)) * (∫ p : ℝ³, (Work.OneBodyKin.profHat p) ^ 2 * ‖p‖ ^ 2) := by
    rw [hmaj_eq, integral_add (integrable_profHat_sq.const_mul a)
      (integrable_profHat_sq_norm_sq.const_mul _), integral_const_mul, integral_const_mul,
      profHat_sq_integral_eq]
  have hM1a : M1 ≤ a + (1 / (4 * a)) * M2 := by
    rw [M1, M2]
    have hπ : (0 : ℝ) < (2 * Real.pi) ^ 3 := by positivity
    calc ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, (Work.OneBodyKin.profHat p) ^ 2 * ‖p‖)
        ≤ ((2 * Real.pi) ^ 3)⁻¹ *
            ∫ p : ℝ³, (Work.OneBodyKin.profHat p) ^ 2 * (a + ‖p‖ ^ 2 / (4 * a)) :=
          mul_le_mul_of_nonneg_left hcomp (by positivity)
      _ = ((2 * Real.pi) ^ 3)⁻¹ * (a * (2 * Real.pi) ^ 3
            + (1 / (4 * a)) * (∫ p : ℝ³, (Work.OneBodyKin.profHat p) ^ 2 * ‖p‖ ^ 2)) := by
          rw [hval]
      _ = a + (1 / (4 * a)) * (((2 * Real.pi) ^ 3)⁻¹ *
            ∫ p : ℝ³, (Work.OneBodyKin.profHat p) ^ 2 * ‖p‖ ^ 2) := by
          have hπne : (2 * Real.pi) ^ 3 ≠ 0 := ne_of_gt hπ
          field_simp
  -- numeric finish
  have hM2le : M2 ≤ (1 - d) ^ 2 * C ^ 2 / 8 := by nlinarith [hM2]
  have hnum : a + (1 / (4 * a)) * M2 ≤ 3 * (1 - d) * C / 8 := by
    have hcancel : 4 * a * (1 / (4 * a) * M2) = M2 := by
      rw [← mul_assoc, mul_one_div_cancel h4a_ne, one_mul]
    have hexp : 4 * a * (a + (1 / (4 * a)) * M2) = 4 * a ^ 2 + M2 := by
      rw [mul_add, ← mul_assoc, mul_one_div_cancel h4a_ne, one_mul]; ring
    have key : 4 * a * (a + (1 / (4 * a)) * M2) ≤ 4 * a * (3 * (1 - d) * C / 8) := by
      rw [hexp, ha]
      nlinarith [hM2le]
    exact le_of_mul_le_mul_left key h4a
  linarith [hM1a, hnum]

/-! ## 4. The two moment comparisons needed in the far region -/

/-- In the far region the mixture budget for the first moment,
`M₁ ≤ (1−ε)(C − dC/2) + εC/2`. -/
private lemma M1_le_mix {C d ε : ℝ} (hC : 0 < C) (hd0 : 0 ≤ d) (hd : d ≤ 1 / 2)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) (hM2 : 8 * M2 ≤ (1 - d) ^ 2 * C ^ 2) :
    M1 ≤ (1 - ε) * (C - d * C / 2) + ε * (C / 2) := by
  have h1 : M1 ≤ 3 * (1 - d) * C / 8 := M1_le_three_eighths hC hd0 hd hM2
  have hK : 0 ≤ C - d * C / 2 := by nlinarith [hd, hC]
  have hK3 : 3 * (1 - d) * C / 8 ≤ (C - d * C / 2) / 2 := by
    have h : C - d * C / 2 = C * (2 - d) / 2 := by ring
    rw [h]
    nlinarith [hd, hC]
  have hhalf : (1 : ℝ) / 2 ≤ 1 - ε := by linarith
  have h4 : (C - d * C / 2) / 2 ≤ (1 - ε) * (C - d * C / 2) := by
    have hX : (C - d * C / 2) / 2 = (1 / 2) * (C - d * C / 2) := by ring
    rw [hX]
    exact mul_le_mul_of_nonneg_right hhalf hK
  have h5 : (1 - ε) * (C - d * C / 2) ≤ (1 - ε) * (C - d * C / 2) + ε * (C / 2) := by
    have : 0 ≤ ε * (C / 2) := mul_nonneg hε0 (by linarith)
    linarith
  linarith [h1, hK3, h4, h5]

/-- In the far region the mixture budget for the second moment,
`M₂ ≤ (1−ε)(C − dC/2)² + ε(C/2)² + β`. -/
private lemma M2_le_mix {C d ε β : ℝ} (hC : 0 < C) (hd0 : 0 ≤ d) (hd : d ≤ 1 / 2)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) (hβ : 0 ≤ β)
    (hM2 : 8 * M2 ≤ (1 - d) ^ 2 * C ^ 2) :
    M2 ≤ (1 - ε) * (C - d * C / 2) ^ 2 + ε * (C / 2) ^ 2 + β := by
  have h1 : M2 ≤ (1 - d) ^ 2 * C ^ 2 / 8 := by nlinarith [hM2]
  have h4 : (1 - d) ^ 2 ≤ 4 * (1 - d / 2) ^ 2 := by nlinarith [hd0]
  have h5 : (1 - d) ^ 2 * C ^ 2 / 8 ≤ (1 / 2) * ((C - d * C / 2) ^ 2) := by
    have h6 : (C - d * C / 2) ^ 2 = C ^ 2 * (1 - d / 2) ^ 2 := by ring
    rw [h6]
    nlinarith [h4, hC]
  have h7 : (1 / 2) * ((C - d * C / 2) ^ 2) ≤ (1 - ε) * ((C - d * C / 2) ^ 2) := by
    have h8 : (1 : ℝ) / 2 ≤ 1 - ε := by linarith
    exact mul_le_mul_of_nonneg_right h8 (sq_nonneg _)
  have h9 : 0 ≤ ε * (C / 2) ^ 2 + β := by
    have := mul_nonneg hε0 (sq_nonneg (C / 2))
    linarith
  linarith [h1, h5, h7, h9]

/-- In the middle region (`C/2 ≤ t ≤ C`) the second moment is paid by the `(1−ε)`-branch:
`M₂ ≤ (1−ε)(t − dC/2)²`. -/
private lemma M2_le_region2 {C d ε t : ℝ} (hC : 0 < C) (hd0 : 0 ≤ d) (hd : d ≤ 1 / 2)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) (ht : C / 2 ≤ t) (hM2 : 8 * M2 ≤ (1 - d) ^ 2 * C ^ 2) :
    M2 ≤ (1 - ε) * (t - d * C / 2) ^ 2 := by
  have h1 : M2 ≤ (1 - d) ^ 2 * C ^ 2 / 8 := by nlinarith [hM2]
  have hK0 : 0 ≤ C * (1 - d) / 2 := by nlinarith [hd, hC]
  have hKle : C * (1 - d) / 2 ≤ t - d * C / 2 := by nlinarith [ht, hd0]
  have hsq : (C * (1 - d) / 2) ^ 2 ≤ (t - d * C / 2) ^ 2 := pow_le_pow_left₀ hK0 hKle 2
  have h2 : (1 - d) ^ 2 * C ^ 2 / 8 ≤ (1 / 2) * (C * (1 - d) / 2) ^ 2 :=
    le_of_eq (by ring)
  have h8 : (1 : ℝ) / 2 ≤ 1 - ε := by linarith
  have h3 : (1 / 2) * (C * (1 - d) / 2) ^ 2 ≤ (1 - ε) * (C * (1 - d) / 2) ^ 2 :=
    mul_le_mul_of_nonneg_right h8 (sq_nonneg _)
  have h4 : (1 - ε) * (C * (1 - d) / 2) ^ 2 ≤ (1 - ε) * (t - d * C / 2) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (by linarith)
  linarith [h1, h2, h3, h4]

/-! ## 5. The theorem -/

theorem symA_fsKinCoeff_mix {C d ε β : ℝ} (hC : 0 < C) (hd0 : 0 ≤ d) (hd : d ≤ 1 / 2)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hnear : ∀ ρ : EuclideanSpace ℝ (Fin 3),
      Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff C) ρ
        ≤ Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff (C - ‖ρ‖)) 0)
    (hM1 : ((2 * Real.pi) ^ 3)⁻¹ * ∫ t : EuclideanSpace ℝ (Fin 3),
        (Work.OneBodyKin.profHat t) ^ 2 * ‖t‖ ≤ C)
    (hM2 : 8 * (((2 * Real.pi) ^ 3)⁻¹ * ∫ t : EuclideanSpace ℝ (Fin 3),
        (Work.OneBodyKin.profHat t) ^ 2 * ‖t‖ ^ 2) ≤ (1 - d) ^ 2 * C ^ 2)
    (htail : Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff (C / 2)) 0 ≤ β) :
    ∀ ρ : EuclideanSpace ℝ (Fin 3),
      Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff C) ρ
        ≤ (1 - ε) * Submission.BoseGases.fsKinCoeff (d * C / 2) ‖ρ‖
          + ε * Submission.BoseGases.fsKinCoeff (C / 2) ‖ρ‖ + β := by
  have hM2' : 8 * M2 ≤ (1 - d) ^ 2 * C ^ 2 := hM2
  have hC0 : 0 ≤ C := le_of_lt hC
  have hd1 : d ≤ 1 := by linarith
  have hβ : 0 ≤ β :=
    le_trans (Work.OneBodyKin.symA_nonneg
      (fun r => Submission.BoseGases.fsKinCoeff_nonneg (C / 2) r) 1 0) htail
  intro ρ
  rcases le_total ‖ρ‖ (C / 2) with ht | ht
  · -- region 1: `‖ρ‖ ≤ C/2`
    have hA : Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff C) ρ ≤ β := by
      refine le_trans (hnear ρ) (le_trans (symA_zero_anti (by linarith) ?_) htail)
      linarith
    have h1 : 0 ≤ (1 - ε) * Submission.BoseGases.fsKinCoeff (d * C / 2) ‖ρ‖ :=
      mul_nonneg (by linarith) (Submission.BoseGases.fsKinCoeff_nonneg _ _)
    have h2 : 0 ≤ ε * Submission.BoseGases.fsKinCoeff (C / 2) ‖ρ‖ :=
      mul_nonneg hε0 (Submission.BoseGases.fsKinCoeff_nonneg _ _)
    linarith
  · rcases le_total ‖ρ‖ C with ht2 | ht2
    · -- region 2: `C/2 ≤ ‖ρ‖ ≤ C`
      have hA : Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff C) ρ ≤ M2 :=
        le_trans (hnear ρ) (symA_zero_le_M2 (by linarith))
      have hfs : Submission.BoseGases.fsKinCoeff (d * C / 2) ‖ρ‖
          = (‖ρ‖ - d * C / 2) ^ 2 :=
        fsKinCoeff_eq_of_le (by nlinarith [hd1, hC0, ht])
      have hM : M2 ≤ (1 - ε) * (‖ρ‖ - d * C / 2) ^ 2 :=
        M2_le_region2 hC hd0 hd hε0 hε ht hM2'
      have hrest : 0 ≤ ε * Submission.BoseGases.fsKinCoeff (C / 2) ‖ρ‖ + β := by
        have := mul_nonneg hε0 (Submission.BoseGases.fsKinCoeff_nonneg (C / 2) ‖ρ‖)
        linarith
      rw [hfs]
      linarith
    · -- region 3: `C ≤ ‖ρ‖`
      have ht3 : C ≤ ‖ρ‖ := ht2
      have hfar := Work.OneBodyKin.symA_fsKinCoeff_far_le (C := C) ρ ht3
      have hfar' : Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff C) ρ
          ≤ (‖ρ‖ - C) ^ 2 + 2 * (‖ρ‖ - C) * M1 + M2 := hfar
      have hfs1 : Submission.BoseGases.fsKinCoeff (d * C / 2) ‖ρ‖
          = (‖ρ‖ - d * C / 2) ^ 2 :=
        fsKinCoeff_eq_of_le (by nlinarith [hd1, hC0, ht3])
      have hfs2 : Submission.BoseGases.fsKinCoeff (C / 2) ‖ρ‖ = (‖ρ‖ - C / 2) ^ 2 :=
        fsKinCoeff_eq_of_le (by linarith)
      have hm1 := M1_le_mix hC hd0 hd hε0 hε hM2'
      have hm2 := M2_le_mix hC hd0 hd hε0 hε hβ hM2'
      have hL : 0 ≤ ‖ρ‖ - C := by linarith
      have e1 : ‖ρ‖ - d * C / 2 = (‖ρ‖ - C) + (C - d * C / 2) := by ring
      have e2 : ‖ρ‖ - C / 2 = (‖ρ‖ - C) + C / 2 := by ring
      have hprod : 2 * (‖ρ‖ - C) * M1
          ≤ 2 * (‖ρ‖ - C) * ((1 - ε) * (C - d * C / 2) + ε * (C / 2)) :=
        mul_le_mul_of_nonneg_left hm1 (by linarith)
      rw [hfs1, hfs2, e1, e2]
      nlinarith [hfar', hprod, hm2]

end

end Work.BoseFixB1
