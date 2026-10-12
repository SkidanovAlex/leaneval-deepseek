import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.Core.bulkEst
import Submission.Work.BoseFixB1.Core.clipLeft
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The one-dimensional sliding-box mean-square bound

`Work.BoseFixB1B.MeanSqPiece.meanSq1d_holds`: for `0 < h ≤ ℓ` and an a.e.-measurable
`F : ℝ → ℝ≥0∞`,

  `∫_u ((∫_{x ∈ I(u)} F)/|I(u)|)² du ≤ (9/h) ∫_{x ∈ [-ℓ/2,ℓ/2]} F(x)² dx`,

where `I(u) = [max(-ℓ/2, h u - h/2), min(ℓ/2, h u + h/2)]`
`= [-ℓ/2,ℓ/2] ∩ [h u - h/2, h u + h/2]` (`= Work.BoseFixB1S.slI ℓ h u`) is the sliding interval of
length `h` centred at `h u`, clipped to the large interval.

The `u`-axis splits into

* the bulk `(-(ℓ-h)/2h, (ℓ-h)/2h]` (window unclipped, constant `1/h`),
* the left clipped region `(-(ℓ+h)/2h, -(ℓ-h)/2h]` (constant `4/h`),
* the right clipped region `((ℓ-h)/2h, (ℓ+h)/2h]` (constant `4/h`),
* the complement, where the window is empty and the integrand vanishes,

and `1 + 4 + 4 = 9`.  The three estimates are `Work.BoseFixB1.Core.bulkEst`,
`Work.BoseFixB1.Core.clipLeft`, and `clipRight_reflect` below, which obtains the right-clipped
region by reflecting (`x ↦ -x`) the left-clipped estimate applied to `F (-·)`.  The reflection
maps the right-clipped window range onto the left-clipped one and `slI ℓ h (-u) = - slI ℓ h u`; it
uses the fact that `x ↦ -x` preserves Lebesgue measure and maps the `L²` mass on `[-ℓ/2,ℓ/2]` to
itself.
-/

namespace Work.BoseFixB1B.MeanSqPiece

open MeasureTheory
open scoped ENNReal

noncomputable section

/-! ## The reflection `x ↦ -x` -/

/-- `Neg.neg` preserves Lebesgue measure on `ℝ`. -/
lemma measurePreserving_neg_volume :
    MeasurePreserving (Neg.neg : ℝ → ℝ) (volume : Measure ℝ) (volume : Measure ℝ) :=
  ⟨measurable_neg, Measure.map_neg_eq_self (volume : Measure ℝ)⟩

/-- Reflection of a set lintegral: `∫_{y ∈ s} f (-y) dy = ∫_{x ∈ -s} f x dx`. -/
lemma setLIntegral_neg (s : Set ℝ) (f : ℝ → ℝ≥0∞) :
    ∫⁻ y in s, f (-y) = ∫⁻ x in -s, f x := by
  have h := measurePreserving_neg_volume.setLIntegral_comp_emb
    (Homeomorph.neg ℝ).measurableEmbedding f s
  rwa [show Neg.neg '' s = -s from Set.image_neg_eq_neg] at h

/-- The Lebesgue integral of the constant `1` over `s` is the measure of `s`. -/
lemma setLIntegral_one_eq (s : Set ℝ) : ∫⁻ _x in s, (1 : ℝ≥0∞) = volume s := by
  rw [lintegral_one, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]

/-- The reflection preserves the Lebesgue measure of a set. -/
lemma volume_neg_image (s : Set ℝ) : volume (-s) = volume s := by
  have h := setLIntegral_neg s (fun _ : ℝ => (1 : ℝ≥0∞))
  rw [setLIntegral_one_eq, setLIntegral_one_eq] at h
  exact h.symm

/-- The reflection of the sliding interval: `slI ℓ h (-u) = - slI ℓ h u`. -/
lemma slI_neg (ℓ h u : ℝ) : Work.BoseFixB1S.slI ℓ h (-u) = - Work.BoseFixB1S.slI ℓ h u := by
  have h1 : h * (-u) = -(h * u) := by ring
  have e1 : -(min (ℓ / 2) (h * u + h / 2)) = max (-ℓ / 2) (-(h * u) - h / 2) := by
    rcases le_total (ℓ / 2) (h * u + h / 2) with hle | hle
    · rw [min_eq_left hle, max_eq_left (by linarith)]
      ring
    · rw [min_eq_right hle, max_eq_right (by linarith)]
      ring
  have e2 : -(max (-ℓ / 2) (h * u - h / 2)) = min (ℓ / 2) (-(h * u) + h / 2) := by
    rcases le_total (h * u - h / 2) (-ℓ / 2) with hle | hle
    · rw [max_eq_left hle, min_eq_left (by linarith)]
      ring
    · rw [max_eq_right hle, min_eq_right (by linarith)]
      ring
  rw [Work.BoseFixB1S.slI, Work.BoseFixB1S.slI, h1, Set.neg_Icc, e1, e2]

/-- Adding the (null) left endpoint to a half-open interval does not change a set lintegral. -/
lemma setLIntegral_Icc_eq_Ioc {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ≥0∞) :
    ∫⁻ x in Set.Icc a b, f x = ∫⁻ x in Set.Ioc a b, f x := by
  have hsub : Set.Ioc a b ∪ {a} = Set.Icc a b := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_singleton_iff, Set.mem_Icc]
    constructor
    · rintro (hx | rfl)
      · exact ⟨hx.1.le, hx.2⟩
      · exact ⟨le_rfl, hab⟩
    · intro hx
      rcases eq_or_lt_of_le hx.1 with h | h
      · exact Or.inr h.symm
      · exact Or.inl ⟨h, hx.2⟩
  rw [← hsub, lintegral_union (measurableSet_singleton a) (by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      simp only [Set.mem_singleton_iff] at hx2
      linarith [hx1.1]),
    setLIntegral_measure_zero _ _ Real.volume_singleton, add_zero]

/-! ## Window-range bookkeeping: outside the window range the integrand vanishes -/

/-- If `u` is at or left of the window range then the sliding interval is contained in the single
point `-ℓ/2`. -/
lemma slI_subset_singleton_left {ℓ h : ℝ} (hh : 0 < h) (_hhℓ : h ≤ ℓ)
    {u : ℝ} (hu : u ≤ -((ℓ + h) / (2 * h))) : Work.BoseFixB1S.slI ℓ h u ⊆ {-ℓ / 2} := by
  intro x hx
  rw [Work.BoseFixB1S.slI_eq] at hx
  simp only [Set.mem_inter_iff, Set.mem_Icc] at hx
  simp only [Set.mem_singleton_iff]
  have h1 : h * u + h / 2 ≤ -ℓ / 2 := by
    have h2 : h * u ≤ h * (-((ℓ + h) / (2 * h))) := mul_le_mul_of_nonneg_left hu hh.le
    have h3 : h * (-((ℓ + h) / (2 * h))) = -((ℓ + h) / 2) := by
      field_simp
    rw [h3] at h2
    linarith
  linarith [hx.1.1, hx.1.2, hx.2.1, hx.2.2, h1]

/-- If `u` is at or right of the window range then the sliding interval is the single point
`ℓ/2`. -/
lemma slI_subset_singleton_right {ℓ h : ℝ} (hh : 0 < h) (_hhℓ : h ≤ ℓ)
    {u : ℝ} (hu : ((ℓ + h) / (2 * h)) < u) : Work.BoseFixB1S.slI ℓ h u ⊆ {ℓ / 2} := by
  intro x hx
  rw [Work.BoseFixB1S.slI_eq] at hx
  simp only [Set.mem_inter_iff, Set.mem_Icc] at hx
  simp only [Set.mem_singleton_iff]
  have h1 : ℓ / 2 < h * u - h / 2 := by
    have h2 : h * ((ℓ + h) / (2 * h)) < h * u := mul_lt_mul_of_pos_left hu hh
    have h3 : h * ((ℓ + h) / (2 * h)) = (ℓ + h) / 2 := by field_simp
    rw [h3] at h2
    linarith
  exact absurd hx.1.2 (not_le.mpr (lt_of_lt_of_le h1 hx.2.1))

/-- Outside the window range the sliding interval has measure zero. -/
lemma volume_slI_eq_zero_of_notMem {ℓ h : ℝ} (hh : 0 < h) (hhℓ : h ≤ ℓ)
    {u : ℝ} (hu : u ∉ Set.Ioc (-((ℓ + h) / (2 * h))) ((ℓ + h) / (2 * h))) :
    volume (Work.BoseFixB1S.slI ℓ h u) = 0 := by
  rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hu
  rcases hu with hu | hu
  · refine measure_mono_null (slI_subset_singleton_left (ℓ := ℓ) hh hhℓ hu) ?_
    rw [Real.volume_singleton]
  · refine measure_mono_null (slI_subset_singleton_right (ℓ := ℓ) hh hhℓ hu) ?_
    rw [Real.volume_singleton]

/-! ## The right-clipped region, by reflection of the left one -/

/-- **The right boundary (clipped) part of the one-dimensional mean-square bound.**

For `0 < h ≤ ℓ` and a.e.-measurable `F : ℝ → ℝ≥0∞`,

  `∫_{u ∈ ((ℓ-h)/(2h), (ℓ+h)/(2h)]} ((∫_{x ∈ slI ℓ h u} F x)/|slI ℓ h u|)² ≤ (4/h) ∫_{[-ℓ/2,ℓ/2]} F²`.

This is the reflection `x ↦ -x` of the left-clipped estimate `Work.BoseFixB1.Core.clipLeft`
applied to the reflected function `x ↦ F (-x)`: the reflection maps the right-clipped window range
onto the left-clipped one and `slI ℓ h (-u) = - slI ℓ h u`. -/
theorem clipRight_reflect {ℓ h : ℝ} (hh : 0 < h) (hhℓ : h ≤ ℓ) {F : ℝ → ℝ≥0∞}
    (hF : AEMeasurable F (volume : Measure ℝ)) :
    ∫⁻ u in Set.Ioc ((ℓ - h) / (2 * h)) ((ℓ + h) / (2 * h)),
        ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x) / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2
      ≤ ENNReal.ofReal (4 / h) * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F x) ^ 2 := by
  set B : ℝ := (ℓ - h) / (2 * h) with hBdef
  set R : ℝ := (ℓ + h) / (2 * h) with hRdef
  have hBR : B ≤ R := by
    rw [hBdef, hRdef, div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * h)]
    linarith
  set G : ℝ → ℝ≥0∞ := fun x => F (-x) with hGdef
  have hG : AEMeasurable G (volume : Measure ℝ) := by
    have hF' : AEMeasurable F (Measure.map (Neg.neg : ℝ → ℝ) (volume : Measure ℝ)) := by
      rw [Measure.map_neg_eq_self]
      exact hF
    have h := hF'.comp_measurable (f := (Neg.neg : ℝ → ℝ)) (by fun_prop)
    simpa [Function.comp_def, hGdef] using h
  -- the pointwise reflection identity for the window mean-square
  have hpt : ∀ u : ℝ, ((∫⁻ x in Work.BoseFixB1S.slI ℓ h (-u), F x)
        / (volume (Work.BoseFixB1S.slI ℓ h (-u)))) ^ 2
      = ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, G x)
        / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2 := by
    intro u
    have hnum : ∫⁻ x in -Work.BoseFixB1S.slI ℓ h u, F x
        = ∫⁻ x in Work.BoseFixB1S.slI ℓ h u, G x := by
      have h := setLIntegral_neg (Work.BoseFixB1S.slI ℓ h u) F
      simpa [hGdef, Function.comp_def] using h.symm
    rw [slI_neg, hnum, volume_neg_image]
  -- the reflected mass equals the original mass
  have hmass : ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), G x ^ 2
      = ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F x) ^ 2 := by
    have h := setLIntegral_neg (Set.Icc (-ℓ / 2) (ℓ / 2)) (fun x => (F x) ^ 2)
    have himg : -Set.Icc (-ℓ / 2) (ℓ / 2) = Set.Icc (-ℓ / 2) (ℓ / 2) := by
      ext x
      simp only [Set.mem_neg, Set.mem_Icc]
      constructor <;> intro h <;> exact ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [himg] at h
    simpa [hGdef, Function.comp_def] using h
  have hleft := Work.BoseFixB1.Core.clipLeft (ℓ := ℓ) (h := h) hh hhℓ hG
  rw [hmass] at hleft
  have hleft' : ∫⁻ u in Set.Ioc (-R) (-B),
        ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, G x) / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2
      ≤ ENNReal.ofReal (4 / h) * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F x) ^ 2 := by
    rw [hRdef, hBdef]
    exact hleft
  -- the reflection of the closed right interval is the closed left interval
  have himgR : -Set.Icc (-R) (-B) = Set.Icc B R := by
    rw [Set.neg_Icc, neg_neg, neg_neg]
  calc ∫⁻ u in Set.Ioc ((ℓ - h) / (2 * h)) ((ℓ + h) / (2 * h)),
        ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x) / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2
      = ∫⁻ u in Set.Ioc B R,
        ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x) / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2 := by
        rw [hBdef, hRdef]
    _ ≤ ∫⁻ u in Set.Icc B R,
        ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x) / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2 :=
        lintegral_mono_set Set.Ioc_subset_Icc_self
    _ = ∫⁻ u in Set.Icc (-R) (-B), ((∫⁻ x in Work.BoseFixB1S.slI ℓ h (-u), F x)
          / (volume (Work.BoseFixB1S.slI ℓ h (-u)))) ^ 2 := by
        have h := setLIntegral_neg (Set.Icc (-R) (-B))
          (fun u => ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x)
            / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2)
        rw [himgR] at h
        exact h.symm
    _ = ∫⁻ u in Set.Icc (-R) (-B), ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, G x)
          / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2 := by
        refine setLIntegral_congr_fun measurableSet_Icc ?_
        intro u _
        exact hpt u
    _ = ∫⁻ u in Set.Ioc (-R) (-B), ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, G x)
          / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2 :=
        setLIntegral_Icc_eq_Ioc (neg_le_neg hBR) _
    _ ≤ ENNReal.ofReal (4 / h) * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F x) ^ 2 := hleft'

/-! ## Assembly with the constant `9 = 1 + 4 + 4` -/

/-- **The one-dimensional sliding-box mean-square bound**, in terms of `slI`. -/
theorem meanSq1d_slI {ℓ h : ℝ} (hh : 0 < h) (hhℓ : h ≤ ℓ) {F : ℝ → ℝ≥0∞}
    (hF : AEMeasurable F (volume : Measure ℝ)) :
    ∫⁻ u : ℝ, ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x)
        / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2
      ≤ ENNReal.ofReal (9 / h) * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F x) ^ 2 := by
  set B : ℝ := (ℓ - h) / (2 * h) with hBdef
  set R : ℝ := (ℓ + h) / (2 * h) with hRdef
  set I : ℝ≥0∞ := ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F x) ^ 2 with hIdef
  set Φ : ℝ → ℝ≥0∞ := fun u => ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x)
      / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2 with hΦdef
  have hR0 : 0 < R := by
    rw [hRdef]; exact div_pos (by linarith) (by positivity)
  have hB0 : 0 ≤ B := by
    rw [hBdef]; exact div_nonneg (by linarith) (by positivity)
  have hBR : B ≤ R := by
    rw [hBdef, hRdef, div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * h)]
    linarith
  have hzero : ∀ u ∉ Set.Ioc (-R) R, Φ u = 0 := by
    intro u hu
    have hvol : volume (Work.BoseFixB1S.slI ℓ h u) = 0 :=
      volume_slI_eq_zero_of_notMem (ℓ := ℓ) hh hhℓ (by simpa [hRdef] using hu)
    have hint : ∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x = 0 :=
      setLIntegral_measure_zero _ _ hvol
    rw [hΦdef]
    simp only [hint, hvol]
    rw [ENNReal.div_eq_inv_mul, ENNReal.inv_zero, mul_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have h1 : ∫⁻ u : ℝ, Φ u = ∫⁻ u in Set.Ioc (-R) R, Φ u := by
    rw [show (∫⁻ u in Set.Ioc (-R) R, Φ u) = ∫⁻ u, (Set.Ioc (-R) R).indicator Φ u from
      (lintegral_indicator measurableSet_Ioc Φ).symm]
    refine lintegral_congr fun u => ?_
    by_cases hu : u ∈ Set.Ioc (-R) R
    · rw [Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu, hzero u hu]
  have hsplit1 : Set.Ioc (-R) (-B) ∪ Set.Ioc (-B) B = Set.Ioc (-R) B :=
    Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)
  have hsplit2 : Set.Ioc (-R) B ∪ Set.Ioc B R = Set.Ioc (-R) R :=
    Set.Ioc_union_Ioc_eq_Ioc (by linarith) hBR
  have hsplit : Set.Ioc (-R) R
      = (Set.Ioc (-R) (-B) ∪ Set.Ioc (-B) B) ∪ Set.Ioc B R := by
    rw [hsplit1, hsplit2]
  have hd1 : Disjoint (Set.Ioc (-R) (-B)) (Set.Ioc (-B) B) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    exact absurd hx1.2 (not_le.mpr hx2.1)
  have hd2 : Disjoint (Set.Ioc (-R) (-B) ∪ Set.Ioc (-B) B) (Set.Ioc B R) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rcases hx1 with hx1 | hx1
    · exact absurd hx1.2 (not_le.mpr (lt_of_le_of_lt (by linarith) hx2.1))
    · exact absurd hx1.2 (not_le.mpr hx2.1)
  have h2 : ∫⁻ u in Set.Ioc (-R) R, Φ u
      = (∫⁻ u in Set.Ioc (-R) (-B), Φ u) + (∫⁻ u in Set.Ioc (-B) B, Φ u)
        + (∫⁻ u in Set.Ioc B R, Φ u) := by
    rw [hsplit, lintegral_union measurableSet_Ioc hd2,
      lintegral_union measurableSet_Ioc hd1]
  have hL := Work.BoseFixB1.Core.clipLeft (ℓ := ℓ) (h := h) hh hhℓ hF
  have hB' := Work.BoseFixB1.Core.bulkEst (ℓ := ℓ) (h := h) hh hhℓ hF
  have hR' := clipRight_reflect (ℓ := ℓ) (h := h) hh hhℓ hF
  have hL' : ∫⁻ u in Set.Ioc (-R) (-B), Φ u ≤ ENNReal.ofReal (4 / h) * I := by
    rw [hΦdef, hIdef]
    exact hL
  have hB'' : ∫⁻ u in Set.Ioc (-B) B, Φ u ≤ ENNReal.ofReal (1 / h) * I := by
    rw [hΦdef, hIdef]
    exact hB'
  have hR'' : ∫⁻ u in Set.Ioc B R, Φ u ≤ ENNReal.ofReal (4 / h) * I := by
    rw [hΦdef, hIdef]
    exact hR'
  have harith : ENNReal.ofReal (4 / h) * I + ENNReal.ofReal (1 / h) * I
      + ENNReal.ofReal (4 / h) * I = ENNReal.ofReal (9 / h) * I := by
    have h4 : (0 : ℝ) ≤ 4 / h := div_nonneg (by norm_num) hh.le
    have h1' : (0 : ℝ) ≤ 1 / h := div_nonneg (by norm_num) hh.le
    have hsum : ENNReal.ofReal (4 / h) + ENNReal.ofReal (1 / h) + ENNReal.ofReal (4 / h)
        = ENNReal.ofReal (9 / h) := by
      calc ENNReal.ofReal (4 / h) + ENNReal.ofReal (1 / h) + ENNReal.ofReal (4 / h)
          = ENNReal.ofReal (4 / h + 1 / h) + ENNReal.ofReal (4 / h) := by
            rw [ENNReal.ofReal_add h4 h1']
        _ = ENNReal.ofReal (4 / h + 1 / h + 4 / h) := by
            rw [ENNReal.ofReal_add (add_nonneg h4 h1') h4]
        _ = ENNReal.ofReal (9 / h) := by
            rw [show (4 : ℝ) / h + 1 / h + 4 / h = 9 / h by ring]
    calc ENNReal.ofReal (4 / h) * I + ENNReal.ofReal (1 / h) * I + ENNReal.ofReal (4 / h) * I
        = (ENNReal.ofReal (4 / h) + ENNReal.ofReal (1 / h) + ENNReal.ofReal (4 / h)) * I := by
          ring
      _ = ENNReal.ofReal (9 / h) * I := by rw [hsum]
  calc ∫⁻ u : ℝ, Φ u
      = ∫⁻ u in Set.Ioc (-R) R, Φ u := h1
    _ = (∫⁻ u in Set.Ioc (-R) (-B), Φ u) + (∫⁻ u in Set.Ioc (-B) B, Φ u)
          + (∫⁻ u in Set.Ioc B R, Φ u) := h2
    _ ≤ ENNReal.ofReal (4 / h) * I + ENNReal.ofReal (1 / h) * I + ENNReal.ofReal (4 / h) * I :=
        add_le_add (add_le_add hL' hB'') hR''
    _ = ENNReal.ofReal (9 / h) * I := harith
    _ = ENNReal.ofReal (9 / h) * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F x) ^ 2 := by rw [hIdef]

/-- **The one-dimensional sliding-box mean-square bound**, in the form of the target. -/
theorem meanSq1d_holds {ℓ h : ℝ} (hh : 0 < h) (hhℓ : h ≤ ℓ) {F : ℝ → ℝ≥0∞}
    (hF : AEMeasurable F (volume : Measure ℝ)) :
    ∫⁻ u : ℝ, ((∫⁻ x in Set.Icc (max (-ℓ / 2) (h * u - h / 2)) (min (ℓ / 2) (h * u + h / 2)), F x)
        / (volume (Set.Icc (max (-ℓ / 2) (h * u - h / 2)) (min (ℓ / 2) (h * u + h / 2))))) ^ 2
      ≤ ENNReal.ofReal (9 / h) * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F x) ^ 2 := by
  simpa only [Work.BoseFixB1S.slI] using meanSq1d_slI (ℓ := ℓ) (h := h) hh hhℓ hF

end

end Work.BoseFixB1B.MeanSqPiece
