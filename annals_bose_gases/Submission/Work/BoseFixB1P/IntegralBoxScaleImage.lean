import Mathlib
import Submission.Work.BoseFixB1P.DiagScaleVolume
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The change of variables identifying a box with the rescaled cube

`Work.BoseFixB1P.boxScale a p q` maps the cube `acube a` onto the axis-parallel box `Box3 p q`
(its `j`-th coordinate is `p_j + (y_j + a/2)·(q_j - p_j)/a`).  This module proves

    `∫_{Box3 p q} F = (∏_j (q_j - p_j)/a) · ∫_{acube a} F ∘ boxScale a p q`

for continuous `F` and nonnegative side lengths `q_j - p_j ≥ 0` (degenerate boxes, where some
`q_j = p_j`, are null sets and both sides vanish).

The proof pushes the Lebesgue measure forward along `boxScale a p q = diagScale c + τ`
(`Work.BoseFixB1P.map_diagScale_volume` plus translation invariance) and evaluates the resulting
set integral with `MeasureTheory.setIntegral_map`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators
open Submission.BoseGases

namespace Work.BoseFixB1P

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The diagonal scaling is measurable. -/
lemma measurable_diagScale (c : Fin 3 → ℝ) : Measurable (diagScale c) := by
  refine cgEuc3.measurable.comp (Measurable.of_eval (fun j => ?_))
  exact (measurable_const_mul (c j)).comp ((measurable_pi_apply j).comp cgEuc3.symm.measurable)

/-- **The pushforward of Lebesgue measure under the box rescaling.** -/
lemma map_boxScale_volume {a : ℝ} (ha : 0 < a) {p q : Fin 3 → ℝ}
    (hL : ∀ j, 0 < q j - p j) :
    Measure.map (boxScale a p q) (volume : Measure E3)
      = (∏ j, ENNReal.ofReal (a / (q j - p j))) • (volume : Measure E3) := by
  set c : Fin 3 → ℝ := fun j => (q j - p j) / a with hc
  set τ : E3 := cgEuc3 (fun j => p j + (a / 2) * ((q j - p j) / a)) with hτ
  have hcne : ∀ j, c j ≠ 0 := fun j => ne_of_gt (div_pos (hL j) ha)
  have hbs : Measure.map (boxScale a p q) (volume : Measure E3)
      = Measure.map (fun y : E3 => diagScale c y + τ) (volume : Measure E3) := by
    congr 1
    funext y
    exact boxScale_eq_diagScale_add a p q y
  have htrans : Measure.map (fun z : E3 => z + τ) (volume : Measure E3)
      = (volume : Measure E3) := by
    have h := (measurePreserving_add_left (volume : Measure E3) τ).map_eq
    rw [show (fun z : E3 => z + τ) = (fun z : E3 => τ + z) from
      funext (fun z => add_comm z τ)]
    exact h
  have hstep : Measure.map (fun y : E3 => diagScale c y + τ) (volume : Measure E3)
      = Measure.map (fun z : E3 => z + τ)
          (Measure.map (diagScale c) (volume : Measure E3)) :=
    (Measure.map_map (measurable_add_const τ) (measurable_diagScale c)).symm
  have hconst : (∏ j, ENNReal.ofReal |c j|⁻¹) = (∏ j, ENNReal.ofReal (a / (q j - p j))) := by
    refine Finset.prod_congr rfl (fun j _ => ?_)
    have hpos : 0 < c j := by
      rw [show c j = (q j - p j) / a from rfl]
      exact div_pos (hL j) ha
    rw [abs_of_pos hpos, show c j = (q j - p j) / a from rfl, inv_div]
  rw [hbs, hstep, map_diagScale_volume hcne, Measure.map_smul, htrans, hconst]
  all_goals first | fun_prop | (apply Continuous.aestronglyMeasurable; fun_prop) | (apply Continuous.aemeasurable; fun_prop) | (apply Continuous.measurable; fun_prop) | measurability

/-- **The image of the cube under the box rescaling** (all sides positive). -/
lemma boxScale_image {a : ℝ} (ha : 0 < a) {p q : Fin 3 → ℝ}
    (hL : ∀ j, 0 < q j - p j) :
    boxScale a p q '' acube a = Box3 p q := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    intro j
    have hyj : y j ∈ Set.Icc (-a / 2) (a / 2) := hy j
    have hc : 0 ≤ (q j - p j) / a := (div_pos (hL j) ha).le
    have h1 : 0 ≤ y j + a / 2 := by linarith [hyj.1]
    have h2 : y j + a / 2 ≤ a := by linarith [hyj.2]
    simp only [boxScale_apply, Set.mem_Icc]
    constructor
    · nlinarith
    · have h3 : (y j + a / 2) * ((q j - p j) / a) ≤ a * ((q j - p j) / a) :=
        mul_le_mul_of_nonneg_right h2 hc
      have h4 : a * ((q j - p j) / a) = q j - p j := by field_simp
      linarith
  · intro hz
    refine ⟨cgEuc3 (fun j => (z j - p j) * a / (q j - p j) - a / 2), ?_, ?_⟩
    · intro j
      have hzj : z j ∈ Set.Icc (p j) (q j) := hz j
      have hpos : 0 < q j - p j := hL j
      have h0 : 0 ≤ (z j - p j) * a / (q j - p j) :=
        div_nonneg (mul_nonneg (by linarith [hzj.1]) ha.le) hpos.le
      have h1 : (z j - p j) * a / (q j - p j) ≤ a := by
        rw [div_le_iff₀ hpos]
        nlinarith [hzj.2]
      simp only [cgEuc3_apply, Set.mem_Icc]
      constructor <;> linarith
    · ext j
      have hpos : 0 < q j - p j := hL j
      have hane : a ≠ 0 := ne_of_gt ha
      have hqne : q j - p j ≠ 0 := ne_of_gt hpos
      simp only [boxScale_cgEuc3_apply]
      field_simp
      ring

/-- **Injectivity of the box rescaling** (all sides positive). -/
lemma injective_boxScale {a : ℝ} (ha : 0 < a) {p q : Fin 3 → ℝ}
    (hL : ∀ j, 0 < q j - p j) : Function.Injective (boxScale a p q) := by
  intro x y hxy
  ext j
  have hcoe : (boxScale a p q x) j = (boxScale a p q y) j := by rw [hxy]
  simp only [boxScale_apply] at hcoe
  have hc : (0 : ℝ) < (q j - p j) / a := div_pos (hL j) ha
  have h2 : (x j + a / 2) * ((q j - p j) / a) = (y j + a / 2) * ((q j - p j) / a) := by
    linarith
  have h3 : x j + a / 2 = y j + a / 2 := mul_right_cancel₀ (ne_of_gt hc) h2
  linarith

/-- **A degenerate box is a null set**: if some side length vanishes, `Box3 p q` has measure `0`. -/
lemma volume_Box3_eq_zero {p q : Fin 3 → ℝ} (h : ∃ j, q j = p j) :
    (volume : Measure E3) (Box3 p q) = 0 := by
  obtain ⟨j, hj⟩ := h
  have hpre : cgEuc3 ⁻¹' Box3 p q
      = Set.pi Set.univ (fun j : Fin 3 => Set.Icc (p j) (q j)) := by
    ext x
    simp only [Set.mem_preimage, mem_Box3, cgEuc3_apply, Set.mem_pi, Set.mem_univ,
      Set.mem_Icc, true_implies]
  have h1 : (volume : Measure E3) (Box3 p q)
      = (volume : Measure (Fin 3 → ℝ)) (cgEuc3 ⁻¹' Box3 p q) := by
    rw [← cgEuc3_mp.map_eq, Measure.map_apply cgEuc3.measurable (measurableSet_Box3 p q)]
  rw [h1, hpre, volume_pi, Measure.pi_pi]
  refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
  rw [hj, Real.volume_Icc]
  simp

/-- **Change of variables for the box rescaling.**  For `a > 0`, an axis-parallel box `Box3 p q`
with nonnegative side lengths and a continuous `F`,

    `∫_{Box3 p q} F = (∏_j (q_j - p_j)/a) · ∫_{acube a} F ∘ boxScale a p q`. -/
theorem integralBoxScaleImage {a : ℝ} (ha : 0 < a) {p q : Fin 3 → ℝ}
    (hL : ∀ j : Fin 3, 0 ≤ q j - p j) {F : E3 → ℝ} (hF : Continuous F) :
    (∫ x in Box3 p q, F x)
      = (∏ j : Fin 3, (q j - p j) / a)
        * ∫ y in acube a, F (boxScale a p q y) := by
  by_cases hdeg : ∃ j : Fin 3, q j - p j = 0
  · obtain ⟨j, hj⟩ := hdeg
    have hnull : (volume : Measure E3) (Box3 p q) = 0 :=
      volume_Box3_eq_zero ⟨j, by linarith [hL j, hj]⟩
    rw [setIntegral_measure_zero F hnull,
      Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj]; ring)]
    ring
  · have hpos : ∀ j : Fin 3, 0 < q j - p j := fun j =>
      lt_of_le_of_ne (hL j) (fun h => hdeg ⟨j, h.symm⟩)
    have himg : boxScale a p q '' acube a = Box3 p q := boxScale_image ha hpos
    have hinj : Function.Injective (boxScale a p q) := injective_boxScale ha hpos
    have hpush : Measure.map (boxScale a p q) (volume : Measure E3)
        = (∏ j, ENNReal.ofReal (a / (q j - p j))) • (volume : Measure E3) :=
      map_boxScale_volume ha hpos
    have hpre : (boxScale a p q) ⁻¹' Box3 p q = acube a := by
      rw [← himg, Set.preimage_image_eq _ hinj]
    have h1 : (∫ x in Box3 p q, F x ∂Measure.map (boxScale a p q) (volume : Measure E3))
        = ∫ y in acube a, F (boxScale a p q y) := by
      rw [setIntegral_map (measurableSet_Box3 p q) hF.measurable.aestronglyMeasurable
        (measurable_boxScale a p q).aemeasurable, hpre]
    have hγ : (∏ j, ENNReal.ofReal (a / (q j - p j))).toReal
        = ∏ j, a / (q j - p j) := by
      rw [ENNReal.toReal_prod]
      exact Finset.prod_congr rfl (fun j _ =>
        ENNReal.toReal_ofReal (div_nonneg ha.le (hL j)))
    have h2 : (∫ x in Box3 p q, F x ∂Measure.map (boxScale a p q) (volume : Measure E3))
        = (∏ j, a / (q j - p j)) * ∫ x in Box3 p q, F x := by
      rw [hpush, Measure.restrict_smul, integral_smul_measure, smul_eq_mul, hγ]
    have h3 : (∏ j, a / (q j - p j)) * (∫ x in Box3 p q, F x)
        = ∫ y in acube a, F (boxScale a p q y) := h2.symm.trans h1
    have hPne : (∏ j : Fin 3, a / (q j - p j)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j _ => div_ne_zero (ne_of_gt ha) (ne_of_gt (hpos j)))
    have h4 : ∫ x in Box3 p q, F x
        = (∏ j : Fin 3, a / (q j - p j))⁻¹ * ∫ y in acube a, F (boxScale a p q y) := by
      rw [eq_inv_mul_iff_mul_eq₀ hPne]
      exact h3
    have hprod : (∏ j : Fin 3, (a / (q j - p j))⁻¹) = ∏ j : Fin 3, (q j - p j) / a :=
      Finset.prod_congr rfl (fun j _ => inv_div (a : ℝ) (q j - p j))
    rw [h4, ← Finset.prod_inv_distrib, hprod]

end Work.BoseFixB1P
