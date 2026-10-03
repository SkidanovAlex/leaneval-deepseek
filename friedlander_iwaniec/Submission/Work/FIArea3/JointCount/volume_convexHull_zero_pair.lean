import Mathlib

/-!
# The area of the triangle spanned by `0`, `u`, `v` in `ℂ`

We prove that the convex hull of `{0, u, v} ⊂ ℂ` has Lebesgue measure
`|u.re * v.im - u.im * v.re| / 2`.

The proof transports the standard unit triangle with vertices `0, 1, I` (whose measure is `1/2`)
along the real-linear map `z ↦ z.re • u + z.im • v`, whose determinant in the real basis
`{1, I}` of `ℂ` is exactly `u.re * v.im - u.im * v.re`.
-/

namespace Work.FIArea3.JointCount

open MeasureTheory

/-! ## The linear map `z ↦ z.re • u + z.im • v` -/

/-- The real-linear map `z ↦ z.re • u + z.im • v` on `ℂ`. -/
noncomputable def zeroPairLinMap (u v : ℂ) : ℂ →ₗ[ℝ] ℂ :=
  (Complex.reCLM : ℂ →ₗ[ℝ] ℝ).smulRight u + (Complex.imCLM : ℂ →ₗ[ℝ] ℝ).smulRight v

@[simp]
theorem zeroPairLinMap_apply (u v z : ℂ) : zeroPairLinMap u v z = z.re • u + z.im • v := rfl

@[simp]
theorem zeroPairLinMap_apply_one (u v : ℂ) : zeroPairLinMap u v 1 = u := by simp

@[simp]
theorem zeroPairLinMap_apply_I (u v : ℂ) : zeroPairLinMap u v Complex.I = v := by simp

@[simp]
theorem zeroPairLinMap_apply_zero (u v : ℂ) : zeroPairLinMap u v 0 = 0 := by simp

theorem zeroPairLinMap_image_singleton (u v : ℂ) :
    zeroPairLinMap u v '' ({(0 : ℂ), 1, Complex.I} : Set ℂ) = ({(0 : ℂ), u, v} : Set ℂ) := by
  ext z
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases hw with rfl | rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by simp, by simp⟩
    · exact ⟨1, by simp, by simp⟩
    · exact ⟨Complex.I, by simp, by simp⟩

/-- The convex hull of `{0, u, v}` is the image of the unit triangle `convexHull {0, 1, I}`
under the linear map `z ↦ z.re • u + z.im • v`. -/
theorem zeroPairLinMap_image_convexHull (u v : ℂ) :
    convexHull ℝ ({(0 : ℂ), u, v} : Set ℂ) =
      zeroPairLinMap u v '' convexHull ℝ ({(0 : ℂ), 1, Complex.I} : Set ℂ) := by
  rw [LinearMap.image_convexHull, zeroPairLinMap_image_singleton]

/-- The determinant of `z ↦ z.re • u + z.im • v` in the real basis `{1, I}` of `ℂ`. -/
theorem zeroPairLinMap_det (u v : ℂ) :
    LinearMap.det (zeroPairLinMap u v) = u.re * v.im - v.re * u.im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI]
  have h : LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (zeroPairLinMap u v)
      = !![u.re, v.re; u.im, v.im] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI,
        zeroPairLinMap]
  rw [h, Matrix.det_fin_two_of]

/-! ## The unit triangle `convexHull {0, 1, I}` -/

/-- `convexHull ℝ {0, 1, I} ⊂ ℂ` is the closed triangle `{re ≥ 0, im ≥ 0, re + im ≤ 1}`. -/
theorem convexHull_zero_one_I :
    convexHull ℝ ({(0 : ℂ), 1, Complex.I} : Set ℂ)
      = {z : ℂ | 0 ≤ z.re ∧ 0 ≤ z.im ∧ z.re + z.im ≤ 1} := by
  apply le_antisymm
  · apply convexHull_min ?_ ?_
    · intro z hz
      rcases hz with rfl | rfl | rfl <;> norm_num [Complex.I_re, Complex.I_im]
    · intro x hx y hy a b ha hb hab
      obtain ⟨hxre, hxim, hxsum⟩ := hx
      obtain ⟨hyre, hyim, hysum⟩ := hy
      refine ⟨?_, ?_, ?_⟩
      · rw [Complex.add_re, Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul]
        exact add_nonneg (mul_nonneg ha hxre) (mul_nonneg hb hyre)
      · rw [Complex.add_im, Complex.smul_im, Complex.smul_im, smul_eq_mul, smul_eq_mul]
        exact add_nonneg (mul_nonneg ha hxim) (mul_nonneg hb hyim)
      · rw [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, Complex.smul_re,
          Complex.smul_im, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
        nlinarith [hxsum, hysum]
  · intro z hz
    obtain ⟨hre, him, hsum⟩ := hz
    have hH : Convex ℝ (convexHull ℝ ({(0 : ℂ), 1, Complex.I} : Set ℂ)) :=
      convex_convexHull ℝ _
    have h0 : (0 : ℂ) ∈ convexHull ℝ ({(0 : ℂ), 1, Complex.I} : Set ℂ) :=
      subset_convexHull ℝ _ (by simp)
    have h1 : (1 : ℂ) ∈ convexHull ℝ ({(0 : ℂ), 1, Complex.I} : Set ℂ) :=
      subset_convexHull ℝ _ (by simp)
    have hI : Complex.I ∈ convexHull ℝ ({(0 : ℂ), 1, Complex.I} : Set ℂ) :=
      subset_convexHull ℝ _ (by simp)
    have key : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b ≤ 1 →
        a • (1 : ℂ) + b • Complex.I ∈ convexHull ℝ ({(0 : ℂ), 1, Complex.I} : Set ℂ) := by
      intro a b ha hb hab
      rcases lt_or_eq_of_le (add_nonneg ha hb) with hlt | heq
      · have hsne : a + b ≠ 0 := ne_of_gt hlt
        have hp : (a / (a + b)) • (1 : ℂ) + (b / (a + b)) • Complex.I ∈
            convexHull ℝ ({(0 : ℂ), 1, Complex.I} : Set ℂ) := by
          refine hH h1 hI (div_nonneg ha (le_of_lt hlt)) (div_nonneg hb (le_of_lt hlt)) ?_
          rw [← add_div, div_self hsne]
        have h2 := hH h0 hp (show (0 : ℝ) ≤ 1 - (a + b) by linarith) (le_of_lt hlt)
          (show 1 - (a + b) + (a + b) = 1 by ring)
        have heq' : (1 - (a + b)) • (0 : ℂ) + (a + b) •
            ((a / (a + b)) • (1 : ℂ) + (b / (a + b)) • Complex.I)
              = a • (1 : ℂ) + b • Complex.I := by
          rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ a hsne, mul_div_cancel₀ b hsne,
            smul_zero, zero_add]
        rwa [heq'] at h2
      · have ha0 : a = 0 := le_antisymm (by linarith) ha
        have hb0 : b = 0 := le_antisymm (by linarith) hb
        simp [ha0, hb0, h0]
    have hz' : z = z.re • (1 : ℂ) + z.im • Complex.I := by
      rw [← Complex.re_add_im z]
      simp
    rw [hz']
    exact key z.re z.im hre him hsum

/-- The measure of the closed triangle `{x ≥ 0, y ≥ 0, x + y ≤ 1} ⊆ ℝ²` is `1/2`. -/
theorem volume_triangle_real_prod :
    (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}
      = ENNReal.ofReal (1 / 2) := by
  set S : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} with hS
  set N : Set (ℝ × ℝ) :=
    ({p : ℝ × ℝ | p.2 = 0} ∪ {p : ℝ × ℝ | p.2 = 1 - p.1}) ∪ {p : ℝ × ℝ | p.1 = 0} with hN
  set T : Set (ℝ × ℝ) :=
    regionBetween (fun _ : ℝ => (0 : ℝ)) (fun x : ℝ => 1 - x) (Set.Ioc (0 : ℝ) 1) with hT
  have hint1 : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Set.Ioc (0 : ℝ) 1) volume :=
    (continuousOn_const.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hint2 : IntegrableOn (fun x : ℝ => 1 - x) (Set.Ioc (0 : ℝ) 1) volume := by
    have hcont : Continuous (fun x : ℝ => 1 - x) := continuous_const.sub continuous_id
    exact (hcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hTval : (volume : Measure (ℝ × ℝ)) T = ENNReal.ofReal (1 / 2) := by
    have hreg := volume_regionBetween_eq_integral hint1 hint2 measurableSet_Ioc
      (fun x hx => by obtain ⟨hx0, hx1⟩ := hx; linarith)
    rw [hT, MeasureTheory.Measure.volume_eq_prod, hreg]
    congr 1
    simp only [Pi.sub_apply, sub_zero]
    rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    have h2 : IntervalIntegrable (fun x : ℝ => x) volume 0 1 :=
      (continuous_id : Continuous fun x : ℝ => x).intervalIntegrable 0 1
    rw [intervalIntegral.integral_sub
      (intervalIntegrable_const (c := (1 : ℝ)) (a := 0) (b := 1)) h2]
    rw [integral_id, intervalIntegral.integral_const]
    norm_num
  have hTS : T ⊆ S := by
    intro p hp
    rw [hT] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [hS]
    obtain ⟨hp1a, hp1b⟩ := hp1
    obtain ⟨hp2a, hp2b⟩ := hp2
    exact ⟨le_of_lt hp1a, le_of_lt hp2a, by linarith⟩
  have hnullA : (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | p.2 = 0} = 0 := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    have h : {p : ℝ × ℝ | p.2 = 0} = Set.univ ×ˢ ({0} : Set ℝ) := by ext p; simp
    rw [h, MeasureTheory.Measure.prod_prod]
    simp
  have hnullB : (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | p.2 = 1 - p.1} = 0 := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    rw [MeasureTheory.Measure.prod_apply (measurableSet_graph (by fun_prop))]
    simp
  have hnullC : (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | p.1 = 0} = 0 := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    have h : {p : ℝ × ℝ | p.1 = 0} = ({0} : Set ℝ) ×ˢ Set.univ := by ext p; simp
    rw [h, MeasureTheory.Measure.prod_prod]
    simp
  have hnull : (volume : Measure (ℝ × ℝ)) N = 0 := by
    rw [hN]
    exact measure_union_null (measure_union_null hnullA hnullB) hnullC
  have hsub : S ⊆ T ∪ N := by
    intro p hp
    rw [hS] at hp
    obtain ⟨hx, hy, hxy⟩ := hp
    by_cases hx0 : p.1 = 0
    · exact Or.inr (Or.inr hx0)
    · have hxpos : 0 < p.1 := lt_of_le_of_ne hx (Ne.symm hx0)
      have hx1 : p.1 ≤ 1 := by linarith
      by_cases hy0 : p.2 = 0
      · exact Or.inr (Or.inl (Or.inl hy0))
      · have hypos : 0 < p.2 := lt_of_le_of_ne hy (Ne.symm hy0)
        by_cases hyeq : p.2 = 1 - p.1
        · exact Or.inr (Or.inl (Or.inr hyeq))
        · have hlt : p.2 < 1 - p.1 := lt_of_le_of_ne (by linarith) hyeq
          exact Or.inl ⟨⟨hxpos, hx1⟩, ⟨hypos, hlt⟩⟩
  have hle1 : (volume : Measure (ℝ × ℝ)) S ≤ (volume : Measure (ℝ × ℝ)) T :=
    calc (volume : Measure (ℝ × ℝ)) S
        ≤ (volume : Measure (ℝ × ℝ)) (T ∪ N) := measure_mono hsub
      _ ≤ (volume : Measure (ℝ × ℝ)) T + (volume : Measure (ℝ × ℝ)) N := measure_union_le _ _
      _ = (volume : Measure (ℝ × ℝ)) T := by rw [hnull, add_zero]
  rw [le_antisymm hle1 (measure_mono hTS), hTval]

/-- The standard unit triangle in `ℂ` has measure `1/2`. -/
theorem volume_convexHull_unit_triangle_aux :
    (MeasureTheory.volume (convexHull ℝ ({(0 : ℂ), 1, Complex.I} : Set ℂ)))
      = ENNReal.ofReal (1 / 2) := by
  rw [convexHull_zero_one_I]
  have hSm : MeasurableSet ({p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}) := by
    measurability
  have hmap : Complex.measurableEquivRealProd ⁻¹'
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}
      = {z : ℂ | 0 ≤ z.re ∧ 0 ≤ z.im ∧ z.re + z.im ≤ 1} := by
    ext z
    simp [Complex.measurableEquivRealProd_apply]
  rw [← hmap]
  rw [(Complex.volume_preserving_equiv_real_prod).measure_preimage hSm.nullMeasurableSet]
  exact volume_triangle_real_prod

/-- **Main lemma.** The convex hull in `ℂ` of `{0, u, v}` has area
`|u.re * v.im - u.im * v.re| / 2`. -/
theorem volume_convexHull_zero_pair (u v : ℂ) :
    (MeasureTheory.volume (convexHull ℝ ({(0 : ℂ), u, v} : Set ℂ))).toReal
      = |u.re * v.im - u.im * v.re| / 2 := by
  have hdet : LinearMap.det (zeroPairLinMap u v) = u.re * v.im - u.im * v.re := by
    rw [zeroPairLinMap_det]; ring
  rw [zeroPairLinMap_image_convexHull, MeasureTheory.Measure.addHaar_image_linearMap, hdet,
    volume_convexHull_unit_triangle_aux]
  rw [← ENNReal.ofReal_mul (abs_nonneg _),
    ENNReal.toReal_ofReal (by positivity)]
  ring

end Work.FIArea3.JointCount
