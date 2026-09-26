import Mathlib
import Submission.Work.Drive.needleArcZoneMono
import Submission.Work.Drive.arcPointDeviationBound
import Submission.Work.Drive.needleChart

/-!
# Vocabulary for the shifted needle's single-ray condition

The shifted needle `Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε` (`shiftedNeedleChart.lean`) traverses,
in the chart `(nCoord, nHeight)` of the chord of its `σ`-blurred endpoints, a thin lens made of

* an *arc side* (the `σ`-blur of the retained arc, fraction `lam` to `1 - lam`),
* a *head chamfer* (from the arc's fraction `1 - lam` to the chord's fraction `1 - lam`),
* a *chord side* (the chord's fraction from `1 - lam` back to `lam`),
* a *tail chamfer* (from the chord's fraction `lam` to the arc's fraction `lam`).

Two objects make that picture formal.

* `Work.Drive.needleFrac lam τ` — the **branch fraction** of the loop parameter `τ`: for every
  sweep parameter `σ`, the loop point `sweepLoopChamfer r D lam σ τ` sits at fraction
  `needleFrac lam τ` of the retained arc (on the arc branch) or of the chord (on the chord branch);
  on the two chamfer branches it is a convex combination of the arc's and the chord's point at the
  chamfer's fraction.  It is the exact piecewise-affine companion of `sweepLoopChamfer`'s
  `if`-tree.
* `Work.Drive.loopBlur r D lam δ₂ σ τ` — the **`σ`-blurred loop point**: the average of the loop
  points at loop parameter `τ` over the sweep window `[σ - δ₂, σ + δ₂]`.  This is the quantity
  which the deviation estimates (`arcPointDeviationBound.lean`) control: the frame of the blurred
  loop cancels the mismatch terms, so `loopBlur` stays within `ℓ/8` of the chord model
  `chordEndA + needleFrac • (chordEndB - chordEndA)`.

The double blur of the needle is the `δ₁`-average of `loopBlur` (`Work.Drive.needleFam_eq_blur_loop`),
which is how every statement about the shifted needle is reduced to statements about the loop
parameter alone.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

/-- **The branch fraction of the loop parameter.**  For every `σ` the loop point
`sweepLoopChamfer r D lam σ τ` lies at fraction `needleFrac lam τ` of the retained arc (on the arc
branch) or of the chord (on the chord branch); on the two chamfers it is the convex combination of
the arc's and the chord's point at that fraction. -/
def needleFrac (lam τ : ℝ) : ℝ :=
  if sweepParam τ ≤ 1 / 2 then lam + (1 - 2 * lam) * (2 * sweepParam τ)
  else if sweepParam τ ≤ 1 / 2 + lam / 2 then 1 - lam
  else if sweepParam τ ≤ 1 - lam / 2 then sweepChordParam lam (sweepParam τ)
  else lam

/-- **The `σ`-blurred loop point** at loop parameter `τ`. -/
def loopBlur (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam δ₂ σ : ℝ) (τ : ℝ) : Space :=
  ∫ v in (-1 : ℝ)..1, sweepBump v • sweepLoopChamfer r D lam (σ - δ₂ * v) τ

/-! ## The four branch formulas -/

lemma needleFrac_arc {lam τ : ℝ} (h : sweepParam τ ≤ 1 / 2) :
    needleFrac lam τ = lam + (1 - 2 * lam) * (2 * sweepParam τ) := by
  rw [needleFrac, if_pos h]

lemma needleFrac_head {lam τ : ℝ} (h1 : ¬ sweepParam τ ≤ 1 / 2)
    (h2 : sweepParam τ ≤ 1 / 2 + lam / 2) : needleFrac lam τ = 1 - lam := by
  rw [needleFrac, if_neg h1, if_pos h2]

lemma needleFrac_chord {lam τ : ℝ} (h1 : ¬ sweepParam τ ≤ 1 / 2)
    (h2 : ¬ sweepParam τ ≤ 1 / 2 + lam / 2) (h3 : sweepParam τ ≤ 1 - lam / 2) :
    needleFrac lam τ = sweepChordParam lam (sweepParam τ) := by
  rw [needleFrac, if_neg h1, if_neg h2, if_pos h3]

lemma needleFrac_tail {lam τ : ℝ} (h1 : ¬ sweepParam τ ≤ 1 / 2)
    (h2 : ¬ sweepParam τ ≤ 1 / 2 + lam / 2) (h3 : ¬ sweepParam τ ≤ 1 - lam / 2) :
    needleFrac lam τ = lam := by
  rw [needleFrac, if_neg h1, if_neg h2, if_neg h3]

/-! ## The range of the branch fraction -/

/-- **The chord fraction of the chamfered loop is monotone.**  For `0 < lam < 1/2` the map
`u ↦ sweepChordParam lam u` is affine with slope `-(1 - 2 lam)/(1/2 - lam) < 0`. -/
lemma sweepChordParam_anti {lam u v : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 2) (huv : u ≤ v) :
    sweepChordParam lam v ≤ sweepChordParam lam u := by
  have hden : (0 : ℝ) < 1 / 2 - lam := by linarith
  have hnum : (0 : ℝ) < 1 - 2 * lam := by linarith
  have hdiff : sweepChordParam lam v - sweepChordParam lam u
      = -(((v - u) / (1 / 2 - lam)) * (1 - 2 * lam)) := by
    rw [sweepChordParam, sweepChordParam]
    field_simp
    ring
  have hq : 0 ≤ (v - u) / (1 / 2 - lam) := div_nonneg (by linarith) hden.le
  have hprod : 0 ≤ ((v - u) / (1 / 2 - lam)) * (1 - 2 * lam) := mul_nonneg hq hnum.le
  linarith [hdiff, hprod]

lemma sweepChordParam_le_one_sub {lam u : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 2)
    (h2 : 1 / 2 + lam / 2 ≤ u) : sweepChordParam lam u ≤ 1 - lam := by
  have h := sweepChordParam_anti h0 h1 h2
  have hden : (1 / 2 : ℝ) - lam ≠ 0 := ne_of_gt (by linarith)
  have hc : sweepChordParam lam (1 / 2 + lam / 2) = 1 - lam := by
    rw [sweepChordParam]
    have hnum : (1 / 2 + lam / 2) - (1 / 2 + lam / 2) = 0 := by ring
    rw [hnum, zero_div]
    ring
  rw [hc] at h; exact h

lemma one_sub_le_sweepChordParam {lam u : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 2)
    (h2 : u ≤ 1 - lam / 2) : lam ≤ sweepChordParam lam u := by
  have h := sweepChordParam_anti h0 h1 h2
  have hden : (1 / 2 : ℝ) - lam ≠ 0 := ne_of_gt (by linarith)
  have hc : sweepChordParam lam (1 - lam / 2) = lam := by
    rw [sweepChordParam]
    have hnum : (1 - lam / 2) - (1 / 2 + lam / 2) = 1 / 2 - lam := by ring
    rw [hnum, div_self hden, one_mul]
    ring
  rw [hc] at h; exact h

/-- **The branch fraction lies between `lam` and `1 - lam`.** -/
theorem needleFrac_mem {lam τ : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 2) :
    lam ≤ needleFrac lam τ ∧ needleFrac lam τ ≤ 1 - lam := by
  have hu : sweepParam τ ∈ Set.Ico (0 : ℝ) 1 := sweepParam_mem τ
  rcases le_or_gt (sweepParam τ) (1 / 2) with h | h
  · rw [needleFrac_arc h]
    constructor <;> nlinarith [hu.1, h, h0, h1]
  · rcases le_or_gt (sweepParam τ) (1 / 2 + lam / 2) with h2 | h2
    · rw [needleFrac_head (not_le.mpr h) h2]; constructor <;> linarith
    · rcases le_or_gt (sweepParam τ) (1 - lam / 2) with h3 | h3
      · rw [needleFrac_chord (not_le.mpr h) (not_le.mpr h2) h3]
        exact ⟨one_sub_le_sweepChordParam h0 h1 h3,
          sweepChordParam_le_one_sub h0 h1 (le_of_lt h2)⟩
      · rw [needleFrac_tail (not_le.mpr h) (not_le.mpr h2) (not_le.mpr h3)]
        constructor <;> linarith

/-- The branch fraction takes values in `[0,1]`. -/
lemma needleFrac_unit {lam τ : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 2) :
    0 ≤ needleFrac lam τ ∧ needleFrac lam τ ≤ 1 := by
  obtain ⟨h2, h3⟩ := needleFrac_mem h0 h1
  exact ⟨le_trans h0.le h2, by linarith⟩

/-- **The branch fraction is `period`-periodic.** -/
lemma needleFrac_add_period (lam τ : ℝ) : needleFrac lam (τ + period) = needleFrac lam τ := by
  simp only [needleFrac, sweepParam_add_period]

/-- **The `σ`-blurred loop point is `period`-periodic in the loop parameter.** -/
lemma loopBlur_add_period (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam δ₂ σ : ℝ)
    (τ : ℝ) : loopBlur r D lam δ₂ σ (τ + period) = loopBlur r D lam δ₂ σ τ := by
  simp only [loopBlur]
  refine intervalIntegral.integral_congr (fun v _ => ?_)
  simp only [sweepLoopChamfer_isPeriodic r D lam (σ - δ₂ * v) τ]

/-- **The needle is `period`-periodic in its parameter.** -/
lemma needleFam_add_period (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam δ₁ δ₂ ε τ : ℝ) :
    needleFam r D lam δ₁ δ₂ ε (τ + period) = needleFam r D lam δ₁ δ₂ ε τ := by
  simp only [needleFam, sweepFam, sweepSmoothT]
  refine intervalIntegral.integral_congr (fun v _ => ?_)
  congr 1
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  congr 1
  rw [show τ + period - δ₁ * u = (τ - δ₁ * u) + period by ring]
  exact sweepLoopChamfer_isPeriodic r D lam (ε - δ₂ * v) (τ - δ₁ * u)

/-! ## Measurability -/

/-- The loop parameter is Borel measurable. -/
lemma measurable_sweepParam' : Measurable (sweepParam : ℝ → ℝ) := by
  unfold sweepParam
  refine Measurable.sub ?_ ?_
  · exact measurable_id.div_const period
  · fun_prop

/-- The branch fraction is Borel measurable in the loop parameter. -/
lemma measurable_needleFrac (lam : ℝ) : Measurable (fun τ : ℝ => needleFrac lam τ) := by
  unfold needleFrac
  have hsp : Measurable (fun τ : ℝ => sweepParam τ) := measurable_sweepParam'
  have hden : Measurable (fun τ : ℝ => sweepChordParam lam (sweepParam τ)) := by
    simp only [sweepChordParam]
    fun_prop
  refine Measurable.ite (measurableSet_le hsp measurable_const) ?_ ?_
  · fun_prop
  refine Measurable.ite (measurableSet_le hsp measurable_const) ?_ ?_
  · exact measurable_const
  refine Measurable.ite (measurableSet_le hsp measurable_const) ?_ ?_
  · exact hden
  · exact measurable_const

/-! ## The window facts of the linear parameter

On the interval `[0, period)` the loop parameter is `τ / period`, and on `[period, 2 * period)` it is
`τ / period - 1`. -/

lemma sweepParam_of_mem_Ico {t : ℝ} (h : t ∈ Set.Ico (0 : ℝ) period) :
    sweepParam t = t / period :=
  sweepParam_eq_div h

lemma sweepParam_of_mem_Ico_period {t : ℝ} (h : t ∈ Set.Ico period (2 * period)) :
    sweepParam t = t / period - 1 := by
  have h' : t - period ∈ Set.Ico (0 : ℝ) period := ⟨by linarith [h.1], by linarith [h.2]⟩
  have h2 : t = (t - period) + period := by ring
  have h3 : (t - period) / period = t / period - 1 := by
    rw [sub_div, div_self (ne_of_gt period_pos)]
  rw [h2, sweepParam_add_period, sweepParam_eq_div h', h3]
  rw [show t - period + period = t from by ring]

end Work.Drive
