import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxFrameAux
import Submission.Work.BoseFixB1.boxTauGen_mode_bound_meas
import Submission.Work.BoseFixB1B.pairMass_pos
import Submission.Work.BoseFixB1S.D1InputsB1
import Submission.Work.BoseFixB1S.boxPairIdSlidingB1
import Submission.Work.BoseFixB1S.chainIntegralQdep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.pairRung.modeBoundPointwise`

The **per-mode Bogoliubov bound** at the two genuine windowed modes
`boxWinModeReGen volA Ac χ q` and `boxWinModeImGen volA Ac χ q`, in the exact form in which
`Work.BoseFixB1S.chainIntegralQdep` consumes it (its hypothesis `hmod`).

The analytic content is entirely in the corpus lemma
`Work.BoseFixB1.boxTauGen_mode_bound_measurable`, which gives, for a *measurable* weight `g`
vanishing off `Ac` and bounded by `Cg`,

  `- ((A - √(A² - B²))/2)·((∫_Ac g²)·S) ≤ A·boxModePGen g + B·boxModeRGen g`,
  `S = boxFlatCount volA a Ac Ψ`.

Applying it to the two real/imaginary windowed modes and adding gives the statement, because
`boxWinModePGen` and `boxWinModeRGen` are *defined* as the sums of the corresponding `boxMode…Gen`
contents.  What has to be supplied here is precisely the three hypotheses of that lemma for the
two modes:

* measurability (the indicator `1_{Ac}` times a continuous function),
* vanishing off `Ac` (`1_{Ac}`-factor),
* the uniform bound `|boxWinModeRe/ImGen| ≤ 2κ` — the *mean-free* part is estimated by the box mean
  of `|χ|`, using `|χ| ≤ κ` and `volA = |Ac|`.

The file is `sorry`-free.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.BoseFixB1B.pairRung

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The box mean of a bounded function is bounded by the bound -/

/-- **The box mean estimate.**  If `|f| ≤ C` on the measurable box `Ac` of finite measure
`volA = |Ac|`, then the normalised box integral `volA⁻¹ ∫_Ac f` is bounded by `C`. -/
private lemma fullMean_abs_le {a volA C : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set E3} (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (volume Ac).toReal) {f : E3 → ℝ} (hf : ∀ z ∈ Ac, |f z| ≤ C) :
    |volA⁻¹ * ∫ w in Ac, f w| ≤ C := by
  have hfin : (volume : Measure E3) Ac < ⊤ :=
    lt_of_le_of_lt (measure_mono hAc) (Submission.BoseGases.acube_compact ha).measure_lt_top
  have hb : ∀ w ∈ Ac, ‖f w‖ ≤ C := fun w hw => by
    rw [Real.norm_eq_abs]; exact hf w hw
  have h1 : ‖∫ w in Ac, f w‖ ≤ C * (volume : Measure E3).real Ac :=
    norm_setIntegral_le_of_norm_le_const hfin hb
  have h2 : |∫ w in Ac, f w| ≤ C * volA := by
    rw [Real.norm_eq_abs, Measure.real_def, ← hvol] at h1
    exact h1
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hvolpos.le)]
  calc volA⁻¹ * |∫ w in Ac, f w| ≤ volA⁻¹ * (C * volA) :=
        mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hvolpos.le)
    _ = C := by rw [mul_comm C volA, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hvolpos), one_mul]

/-! ## 2. The two windowed modes are bounded by `2κ` -/

/-- The real windowed mode is bounded by `2κ`. -/
private lemma abs_boxWinModeReGen_le {a volA κ : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set E3} (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (volume Ac).toReal) (hκ0 : 0 ≤ κ) {χ : E3 → ℝ}
    (hκ : ∀ z, |χ z| ≤ κ) (q z : E3) :
    |Work.BoseFixB1.boxWinModeReGen volA Ac χ q z| ≤ 2 * κ := by
  have hcs : ∀ w ∈ Ac, |χ w * Real.cos (inner ℝ q w)| ≤ κ := fun w _ => by
    rw [abs_mul]
    calc |χ w| * |Real.cos (inner ℝ q w)| ≤ κ * 1 :=
          mul_le_mul (hκ w) (Real.abs_cos_le_one _) (abs_nonneg _) hκ0
      _ = κ := mul_one κ
  have hmean : |volA⁻¹ * ∫ w in Ac, χ w * Real.cos (inner ℝ q w)| ≤ κ :=
    fullMean_abs_le ha hvolpos hAc hvol hcs
  unfold Work.BoseFixB1.boxWinModeReGen
  by_cases hz : z ∈ Ac
  · rw [Set.indicator_of_mem hz, one_mul]
    calc |χ z * Real.cos (inner ℝ q z) - volA⁻¹ * ∫ w in Ac, χ w * Real.cos (inner ℝ q w)|
        ≤ |χ z * Real.cos (inner ℝ q z)|
            + |volA⁻¹ * ∫ w in Ac, χ w * Real.cos (inner ℝ q w)| := abs_sub _ _
      _ ≤ κ + κ := add_le_add (hcs z hz) hmean
      _ = 2 * κ := by ring
  · rw [Set.indicator_of_notMem hz, zero_mul, abs_zero]
    linarith

/-- The imaginary windowed mode is bounded by `2κ`. -/
private lemma abs_boxWinModeImGen_le {a volA κ : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set E3} (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (volume Ac).toReal) (hκ0 : 0 ≤ κ) {χ : E3 → ℝ}
    (hκ : ∀ z, |χ z| ≤ κ) (q z : E3) :
    |Work.BoseFixB1.boxWinModeImGen volA Ac χ q z| ≤ 2 * κ := by
  have hcs : ∀ w ∈ Ac, |χ w * Real.sin (inner ℝ q w)| ≤ κ := fun w _ => by
    rw [abs_mul]
    calc |χ w| * |Real.sin (inner ℝ q w)| ≤ κ * 1 :=
          mul_le_mul (hκ w) (Real.abs_sin_le_one _) (abs_nonneg _) hκ0
      _ = κ := mul_one κ
  have hmean : |volA⁻¹ * ∫ w in Ac, χ w * Real.sin (inner ℝ q w)| ≤ κ :=
    fullMean_abs_le ha hvolpos hAc hvol hcs
  unfold Work.BoseFixB1.boxWinModeImGen
  rw [abs_neg]
  by_cases hz : z ∈ Ac
  · rw [Set.indicator_of_mem hz, one_mul]
    calc |χ z * Real.sin (inner ℝ q z) - volA⁻¹ * ∫ w in Ac, χ w * Real.sin (inner ℝ q w)|
        ≤ |χ z * Real.sin (inner ℝ q z)|
            + |volA⁻¹ * ∫ w in Ac, χ w * Real.sin (inner ℝ q w)| := abs_sub _ _
      _ ≤ κ + κ := add_le_add (hcs z hz) hmean
      _ = 2 * κ := by ring
  · rw [Set.indicator_of_notMem hz, zero_mul, abs_zero]
    linarith

/-! ## 3. The arithmetic combining the two modes -/

/-- Adding the two per-mode bounds.  The `boxWinMode…Gen` contents are the *sums* of the two
`boxMode…Gen` contents, so the two `(A - √(A² - B²))/2`-weighted terms combine into a single
term with the *sum* of the two window masses inside. -/
private lemma add_mode_bounds {F Y Z S A B PRe PIm RRe RIm : ℝ}
    (h1 : -F * (Y * S) ≤ A * PRe + B * RRe)
    (h2 : -F * (Z * S) ≤ A * PIm + B * RIm) :
    -((F * (Y + Z)) * S) ≤ A * (PRe + PIm) + B * (RRe + RIm) := by
  have hL : -((F * (Y + Z)) * S) = -F * (Y * S) + -F * (Z * S) := by ring
  have hR : A * (PRe + PIm) + B * (RRe + RIm)
      = A * PRe + B * RRe + (A * PIm + B * RIm) := by ring
  rw [hL, hR]
  exact add_le_add h1 h2

/-! ## 4. The target -/

theorem modeBoundPointwise {n : ℕ} {a Acoef B volA κ : ℝ}
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} {χ : EuclideanSpace ℝ (Fin 3) → ℝ}
    {Ψ : Submission.BoseGases.X (n + 1) → ℝ} (q : EuclideanSpace ℝ (Fin 3))
    (ha : 0 < a) (hAcm : MeasurableSet Ac) (hAcsub : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχsupp : ∀ z, z ∉ Ac → χ z = 0)
    (hκ : ∀ z, |χ z| ≤ κ) (hκ0 : 0 ≤ κ)
    (hΨc : Continuous Ψ) (hA : 0 < Acoef) (hB : |B| ≤ Acoef) :
    -(((Acoef - Real.sqrt (Acoef ^ 2 - B ^ 2)) / 2) *
        ((∫ z in Ac, (Work.BoseFixB1.boxWinModeReGen volA Ac χ q z) ^ 2)
          + (∫ z in Ac, (Work.BoseFixB1.boxWinModeImGen volA Ac χ q z) ^ 2))
        * Work.BoseFixB1S.boxFlatCount volA a Ac Ψ)
      ≤ Acoef * Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q
        + B * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q := by
  -- the three hypotheses of `boxTauGen_mode_bound_measurable` for each of the two modes
  have hRe_meas : Measurable (Work.BoseFixB1.boxWinModeReGen volA Ac χ q) := by
    unfold Work.BoseFixB1.boxWinModeReGen; fun_prop
  have hIm_meas : Measurable (Work.BoseFixB1.boxWinModeImGen volA Ac χ q) := by
    unfold Work.BoseFixB1.boxWinModeImGen; fun_prop
  have hRe0 : ∀ z, z ∉ Ac → Work.BoseFixB1.boxWinModeReGen volA Ac χ q z = 0 := by
    intro z hz; unfold Work.BoseFixB1.boxWinModeReGen
    rw [Set.indicator_of_notMem hz, zero_mul]
  have hIm0 : ∀ z, z ∉ Ac → Work.BoseFixB1.boxWinModeImGen volA Ac χ q z = 0 := by
    intro z hz; unfold Work.BoseFixB1.boxWinModeImGen
    rw [Set.indicator_of_notMem hz, zero_mul, neg_zero]
  have hReC : ∀ z, |Work.BoseFixB1.boxWinModeReGen volA Ac χ q z| ≤ 2 * κ :=
    abs_boxWinModeReGen_le ha hvolpos hAcsub hvol hκ0 hκ q
  have hImC : ∀ z, |Work.BoseFixB1.boxWinModeImGen volA Ac χ q z| ≤ 2 * κ :=
    abs_boxWinModeImGen_le ha hvolpos hAcsub hvol hκ0 hκ q
  -- the per-mode Bogoliubov bound at the two windowed modes
  have h1 := Work.BoseFixB1.boxTauGen_mode_bound_measurable (N := n)
    (g := Work.BoseFixB1.boxWinModeReGen volA Ac χ q) (Cg := 2 * κ)
    ha hAcm hAcsub hvol hvolpos hRe_meas hRe0 hReC hΨc hA hB
  have h2 := Work.BoseFixB1.boxTauGen_mode_bound_measurable (N := n)
    (g := Work.BoseFixB1.boxWinModeImGen volA Ac χ q) (Cg := 2 * κ)
    ha hAcm hAcsub hvol hvolpos hIm_meas hIm0 hImC hΨc hA hB
  -- `boxWinModePGen`/`boxWinModeRGen` are definitionally the sums of the two contents
  rw [Work.BoseFixB1.boxWinModePGen, Work.BoseFixB1.boxWinModeRGen]
  exact add_mode_bounds h1 h2

end Work.BoseFixB1B.pairRung
