import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.BoseFixB1S.MeanSq.Peel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory
open scoped ENNReal

namespace Work.BoseFixB1S

/-- The sliding interval of length `h` centred at `h*u`, intersected with `[-ℓ/2, ℓ/2]`. -/
def slI (ℓ h u : ℝ) : Set ℝ := Set.Icc (max (-ℓ/2) (h*u - h/2)) (min (ℓ/2) (h*u + h/2))

lemma slI_eq (ℓ h u : ℝ) :
    slI ℓ h u = Set.Icc (-ℓ/2) (ℓ/2) ∩ Set.Icc (h*u - h/2) (h*u + h/2) := by
  ext y
  simp only [slI, Set.mem_Icc, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨⟨le_trans (le_max_left _ _) h.1, le_trans h.2 (min_le_left _ _)⟩,
      ⟨le_trans (le_max_right _ _) h.1, le_trans h.2 (min_le_right _ _)⟩⟩
  · intro h
    exact ⟨max_le h.1.1 h.2.1, le_min h.1.2 h.2.2⟩

lemma slI_subset (ℓ h u : ℝ) : slI ℓ h u ⊆ Set.Icc (-ℓ/2) (ℓ/2) := by
  rw [slI_eq]; exact Set.inter_subset_left

lemma measurableSet_slI (ℓ h u : ℝ) : MeasurableSet (slI ℓ h u) := by
  rw [slI_eq]
  exact ((isClosed_Icc.preimage (by fun_prop : Continuous fun y : ℝ => y)).inter
    (isClosed_Icc.preimage (by fun_prop : Continuous fun y : ℝ => y))).measurableSet

lemma volume_slI_ne_top (ℓ h u : ℝ) : volume (slI ℓ h u) ≠ ⊤ := by
  have h1 : volume (slI ℓ h u) ≤ volume (Set.Icc (-ℓ/2) (ℓ/2)) := measure_mono (slI_subset ℓ h u)
  rw [Real.volume_Icc] at h1
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1

/-- The sliding box in `Fin 3 → ℝ`. -/
def slBox (ℓ h : ℝ) (u : Fin 3 → ℝ) : Set (Fin 3 → ℝ) := Set.pi Set.univ (fun j => slI ℓ h (u j))

/-- The large cube in `Fin 3 → ℝ`. -/
def slBig (ℓ : ℝ) : Set (Fin 3 → ℝ) := Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-ℓ/2) (ℓ/2))

lemma measurableSet_slBox (ℓ h : ℝ) (u : Fin 3 → ℝ) : MeasurableSet (slBox ℓ h u) :=
  MeasurableSet.pi Set.countable_univ (fun j _ => measurableSet_slI ℓ h (u j))

lemma measurableSet_slBig (ℓ : ℝ) : MeasurableSet (slBig ℓ) :=
  MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)

lemma mem_slBox {ℓ h : ℝ} {u y : Fin 3 → ℝ} : y ∈ slBox ℓ h u ↔ ∀ j, y j ∈ slI ℓ h (u j) := by
  simp [slBox]

lemma mem_slBig {ℓ : ℝ} {y : Fin 3 → ℝ} :
    y ∈ slBig ℓ ↔ ∀ j, y j ∈ Set.Icc (-ℓ/2) (ℓ/2) := by
  simp only [slBig, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, Pi.zero_apply]

/-- Volume of the sliding box: the product of the coordinate lengths. -/
lemma volume_slBox (ℓ h : ℝ) (u : Fin 3 → ℝ) :
    volume (slBox ℓ h u) = ∏ j, volume (slI ℓ h (u j)) := by
  rw [slBox, MeasureTheory.volume_pi]
  exact MeasureTheory.Measure.pi_pi (fun _ : Fin 3 => (volume : Measure ℝ)) _

/-- Indicator of the sliding box as a product of the coordinate indicators. -/
lemma indicator_slBox (ℓ h : ℝ) (u : Fin 3 → ℝ) (F : (Fin 3 → ℝ) → ℝ≥0∞) :
    (slBox ℓ h u).indicator F
      = fun y => (slI ℓ h (u 0)).indicator (fun _ => (1 : ℝ≥0∞)) (y 0) *
          ((slI ℓ h (u 1)).indicator (fun _ => (1 : ℝ≥0∞)) (y 1) *
            ((slI ℓ h (u 2)).indicator (fun _ => (1 : ℝ≥0∞)) (y 2) * F y)) := by
  funext y
  by_cases hmem : y ∈ slBox ℓ h u
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (mem_slBox.mp hmem 0),
      Set.indicator_of_mem (mem_slBox.mp hmem 1), Set.indicator_of_mem (mem_slBox.mp hmem 2)]
    simp
  · rw [Set.indicator_of_notMem hmem]
    by_cases h0 : y 0 ∈ slI ℓ h (u 0)
    · by_cases h1 : y 1 ∈ slI ℓ h (u 1)
      · have h2 : y 2 ∉ slI ℓ h (u 2) := by
          intro h2
          exact hmem (mem_slBox.mpr (by intro j; fin_cases j <;> assumption))
        rw [Set.indicator_of_mem h0, Set.indicator_of_mem h1, Set.indicator_of_notMem h2]
        ring
      · rw [Set.indicator_of_mem h0, Set.indicator_of_notMem h1]
        ring
    · rw [Set.indicator_of_notMem h0]
      ring

/-- Indicator of the cube as a product of the coordinate indicators. -/
lemma indicator_slBig (ℓ : ℝ) (F : (Fin 3 → ℝ) → ℝ≥0∞) :
    (slBig ℓ).indicator F
      = fun y => (Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) (y 0) *
          ((Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) (y 1) *
            ((Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) (y 2) * F y)) := by
  funext y
  by_cases hmem : y ∈ slBig ℓ
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (mem_slBig.mp hmem 0),
      Set.indicator_of_mem (mem_slBig.mp hmem 1), Set.indicator_of_mem (mem_slBig.mp hmem 2)]
    simp
  · rw [Set.indicator_of_notMem hmem]
    by_cases h0 : y 0 ∈ Set.Icc (-ℓ/2) (ℓ/2)
    · by_cases h1 : y 1 ∈ Set.Icc (-ℓ/2) (ℓ/2)
      · have h2 : y 2 ∉ Set.Icc (-ℓ/2) (ℓ/2) := by
          intro h2
          exact hmem (mem_slBig.mpr (by intro j; fin_cases j <;> assumption))
        rw [Set.indicator_of_mem h0, Set.indicator_of_mem h1, Set.indicator_of_notMem h2]
        ring
      · rw [Set.indicator_of_mem h0, Set.indicator_of_notMem h1]
        ring
    · rw [Set.indicator_of_notMem h0]
      ring

/-- An indicator times a function is the corresponding set integral. -/
lemma indicator_mul_setLintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s) (f : α → ℝ≥0∞) :
    ∫⁻ x, s.indicator (fun _ => (1 : ℝ≥0∞)) x * f x ∂μ = ∫⁻ x in s, f x ∂μ := by
  rw [← lintegral_indicator hs f]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]

/-- Pull a constant out of a set integral. -/
lemma setLintegral_const_mul' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s) (c : ℝ≥0∞) (hc : c ≠ ∞) (f : α → ℝ≥0∞) :
    ∫⁻ x in s, c * f x ∂μ = c * ∫⁻ x in s, f x ∂μ := by
  rw [← lintegral_indicator hs (fun x => c * f x), ← lintegral_indicator hs f]
  refine (lintegral_congr fun x => ?_).trans (lintegral_const_mul' c _ hc)
  by_cases hx : x ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- Peeling the box integral in coordinates. -/
lemma lintegral_slBox {ℓ h : ℝ} (u : Fin 3 → ℝ) {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ y in slBox ℓ h u, F y
      = ∫⁻ y₀ in slI ℓ h (u 0), ∫⁻ y₁ in slI ℓ h (u 1), ∫⁻ y₂ in slI ℓ h (u 2),
          F ![y₀, y₁, y₂] := by
  have hm1 : Measurable (fun y : Fin 3 → ℝ => y 1) := (continuous_apply 1).measurable
  have hm2 : Measurable (fun y : Fin 3 → ℝ => y 2) := (continuous_apply 2).measurable
  have hm0 : Measurable (fun y : Fin 3 → ℝ => y 0) := (continuous_apply 0).measurable
  have hG : Measurable (fun y : Fin 3 → ℝ =>
      (slI ℓ h (u 0)).indicator (fun _ => (1 : ℝ≥0∞)) (y 0) *
        ((slI ℓ h (u 1)).indicator (fun _ => (1 : ℝ≥0∞)) (y 1) *
          ((slI ℓ h (u 2)).indicator (fun _ => (1 : ℝ≥0∞)) (y 2) * F y))) :=
    ((measurable_const : Measurable (fun _ : ℝ => (1 : ℝ≥0∞))).indicator
        (measurableSet_slI ℓ h (u 0))).comp hm0 |>.mul
      (((measurable_const : Measurable (fun _ : ℝ => (1 : ℝ≥0∞))).indicator
        (measurableSet_slI ℓ h (u 1))).comp hm1 |>.mul
      (((measurable_const : Measurable (fun _ : ℝ => (1 : ℝ≥0∞))).indicator
        (measurableSet_slI ℓ h (u 2))).comp hm2 |>.mul hF))
  rw [← lintegral_indicator (measurableSet_slBox ℓ h u), indicator_slBox ℓ h u F]
  rw [lintegralPi3_peel _ hG]
  have e0 : ∀ a b c : ℝ, (![a, b, c] : Fin 3 → ℝ) 0 = a := fun a b c => by simp
  have e1 : ∀ a b c : ℝ, (![a, b, c] : Fin 3 → ℝ) 1 = b := fun a b c => by simp
  have e2 : ∀ a b c : ℝ, (![a, b, c] : Fin 3 → ℝ) 2 = c := fun a b c => by simp
  simp only [e0, e1, e2]
  have h1 : (∫⁻ y₀ : ℝ, ∫⁻ y₁ : ℝ, ∫⁻ y₂ : ℝ,
        (slI ℓ h (u 0)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ *
          ((slI ℓ h (u 1)).indicator (fun _ => (1 : ℝ≥0∞)) y₁ *
            ((slI ℓ h (u 2)).indicator (fun _ => (1 : ℝ≥0∞)) y₂ * F ![y₀, y₁, y₂])))
      = ∫⁻ y₀ : ℝ, ∫⁻ y₁ : ℝ, ∫⁻ y₂ in slI ℓ h (u 2),
          (slI ℓ h (u 0)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ *
            ((slI ℓ h (u 1)).indicator (fun _ => (1 : ℝ≥0∞)) y₁ * F ![y₀, y₁, y₂]) := by
    refine lintegral_congr fun y₀ => ?_
    refine lintegral_congr fun y₁ => ?_
    rw [show (∫⁻ y₂ : ℝ, (slI ℓ h (u 0)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ *
          ((slI ℓ h (u 1)).indicator (fun _ => (1 : ℝ≥0∞)) y₁ *
            ((slI ℓ h (u 2)).indicator (fun _ => (1 : ℝ≥0∞)) y₂ * F ![y₀, y₁, y₂])))
        = ∫⁻ y₂ : ℝ, (slI ℓ h (u 2)).indicator (fun _ => (1 : ℝ≥0∞)) y₂ *
            ((slI ℓ h (u 0)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ *
              ((slI ℓ h (u 1)).indicator (fun _ => (1 : ℝ≥0∞)) y₁ * F ![y₀, y₁, y₂]))
        from by
      refine lintegral_congr fun y₂ => ?_
      ring]
    exact indicator_mul_setLintegral (measurableSet_slI ℓ h (u 2)) _
  rw [h1]
  have h2 : (∫⁻ y₀ : ℝ, ∫⁻ y₁ : ℝ, ∫⁻ y₂ in slI ℓ h (u 2),
        (slI ℓ h (u 0)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ *
          ((slI ℓ h (u 1)).indicator (fun _ => (1 : ℝ≥0∞)) y₁ * F ![y₀, y₁, y₂]))
      = ∫⁻ y₀ : ℝ, ∫⁻ y₁ in slI ℓ h (u 1), ∫⁻ y₂ in slI ℓ h (u 2),
          (slI ℓ h (u 0)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ * F ![y₀, y₁, y₂] := by
    refine lintegral_congr fun y₀ => ?_
    have h2a : (∫⁻ y₁ : ℝ, ∫⁻ y₂ in slI ℓ h (u 2),
          (slI ℓ h (u 0)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ *
            ((slI ℓ h (u 1)).indicator (fun _ => (1 : ℝ≥0∞)) y₁ * F ![y₀, y₁, y₂]))
        = ∫⁻ y₁ : ℝ, (slI ℓ h (u 1)).indicator (fun _ => (1 : ℝ≥0∞)) y₁ *
            (∫⁻ y₂ in slI ℓ h (u 2),
              (slI ℓ h (u 0)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ * F ![y₀, y₁, y₂]) := by
      refine lintegral_congr fun y₁ => ?_
      rw [show (∫⁻ y₂ in slI ℓ h (u 2),
            (slI ℓ h (u 0)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ *
              ((slI ℓ h (u 1)).indicator (fun _ => (1 : ℝ≥0∞)) y₁ * F ![y₀, y₁, y₂]))
          = ∫⁻ y₂ in slI ℓ h (u 2),
              (slI ℓ h (u 1)).indicator (fun _ => (1 : ℝ≥0∞)) y₁ *
                ((slI ℓ h (u 0)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ * F ![y₀, y₁, y₂])
          from by
        refine lintegral_congr fun y₂ => ?_
        ring]
      exact setLintegral_const_mul' (measurableSet_slI ℓ h (u 2)) _
        (by by_cases hh : y₁ ∈ slI ℓ h (u 1) <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, hh]) _
    rw [h2a, indicator_mul_setLintegral (measurableSet_slI ℓ h (u 1)) _]
  rw [h2]
  have h3 : (∫⁻ y₀ : ℝ, ∫⁻ y₁ in slI ℓ h (u 1), ∫⁻ y₂ in slI ℓ h (u 2),
        (slI ℓ h (u 0)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ * F ![y₀, y₁, y₂])
      = ∫⁻ y₀ in slI ℓ h (u 0), ∫⁻ y₁ in slI ℓ h (u 1), ∫⁻ y₂ in slI ℓ h (u 2),
          F ![y₀, y₁, y₂] := by
    have h3a : (∫⁻ y₀ : ℝ, ∫⁻ y₁ in slI ℓ h (u 1), ∫⁻ y₂ in slI ℓ h (u 2),
          (slI ℓ h (u 0)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ * F ![y₀, y₁, y₂])
        = ∫⁻ y₀ : ℝ, (slI ℓ h (u 0)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ *
            (∫⁻ y₁ in slI ℓ h (u 1), ∫⁻ y₂ in slI ℓ h (u 2), F ![y₀, y₁, y₂]) := by
      refine lintegral_congr fun y₀ => ?_
      have h3b : (∫⁻ y₁ in slI ℓ h (u 1), ∫⁻ y₂ in slI ℓ h (u 2),
            (slI ℓ h (u 0)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ * F ![y₀, y₁, y₂])
          = (slI ℓ h (u 0)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ *
              (∫⁻ y₁ in slI ℓ h (u 1), ∫⁻ y₂ in slI ℓ h (u 2), F ![y₀, y₁, y₂]) := by
        rw [show (∫⁻ y₁ in slI ℓ h (u 1), ∫⁻ y₂ in slI ℓ h (u 2),
              (slI ℓ h (u 0)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ * F ![y₀, y₁, y₂])
            = ∫⁻ y₁ in slI ℓ h (u 1),
                (slI ℓ h (u 0)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ *
                  (∫⁻ y₂ in slI ℓ h (u 2), F ![y₀, y₁, y₂]) from by
          refine lintegral_congr fun y₁ => ?_
          exact setLintegral_const_mul' (measurableSet_slI ℓ h (u 2)) _
            (by by_cases hh : y₀ ∈ slI ℓ h (u 0) <;>
              simp [Set.indicator_of_mem, Set.indicator_of_notMem, hh]) _]
        exact setLintegral_const_mul' (measurableSet_slI ℓ h (u 1)) _
          (by by_cases hh : y₀ ∈ slI ℓ h (u 0) <;>
            simp [Set.indicator_of_mem, Set.indicator_of_notMem, hh]) _
      rw [h3b]
    rw [h3a, indicator_mul_setLintegral (measurableSet_slI ℓ h (u 0)) _]
  rw [h3]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- Peeling the cube integral in coordinates. -/
lemma lintegral_slBig {ℓ : ℝ} {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ y in slBig ℓ, F y
      = ∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2),
          ∫⁻ y₂ in Set.Icc (-ℓ/2) (ℓ/2), F ![y₀, y₁, y₂] := by
  have hm1 : Measurable (fun y : Fin 3 → ℝ => y 1) := (continuous_apply 1).measurable
  have hm2 : Measurable (fun y : Fin 3 → ℝ => y 2) := (continuous_apply 2).measurable
  have hm0 : Measurable (fun y : Fin 3 → ℝ => y 0) := (continuous_apply 0).measurable
  have hG : Measurable (fun y : Fin 3 → ℝ =>
      (Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) (y 0) *
        ((Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) (y 1) *
          ((Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) (y 2) * F y))) :=
    ((measurable_const : Measurable (fun _ : ℝ => (1 : ℝ≥0∞))).indicator
        measurableSet_Icc).comp hm0 |>.mul
      (((measurable_const : Measurable (fun _ : ℝ => (1 : ℝ≥0∞))).indicator
        measurableSet_Icc).comp hm1 |>.mul
      (((measurable_const : Measurable (fun _ : ℝ => (1 : ℝ≥0∞))).indicator
        measurableSet_Icc).comp hm2 |>.mul hF))
  rw [← lintegral_indicator (measurableSet_slBig ℓ), indicator_slBig ℓ F]
  rw [lintegralPi3_peel _ hG]
  have e0 : ∀ a b c : ℝ, (![a, b, c] : Fin 3 → ℝ) 0 = a := fun a b c => by simp
  have e1 : ∀ a b c : ℝ, (![a, b, c] : Fin 3 → ℝ) 1 = b := fun a b c => by simp
  have e2 : ∀ a b c : ℝ, (![a, b, c] : Fin 3 → ℝ) 2 = c := fun a b c => by simp
  simp only [e0, e1, e2]
  have h1 : (∫⁻ y₀ : ℝ, ∫⁻ y₁ : ℝ, ∫⁻ y₂ : ℝ,
        (Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ *
          ((Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₁ *
            ((Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₂ * F ![y₀, y₁, y₂])))
      = ∫⁻ y₀ : ℝ, ∫⁻ y₁ : ℝ, ∫⁻ y₂ in Set.Icc (-ℓ/2) (ℓ/2),
          (Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ *
            ((Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₁ * F ![y₀, y₁, y₂]) := by
    refine lintegral_congr fun y₀ => ?_
    refine lintegral_congr fun y₁ => ?_
    rw [show (∫⁻ y₂ : ℝ, (Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ *
          ((Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₁ *
            ((Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₂ * F ![y₀, y₁, y₂])))
        = ∫⁻ y₂ : ℝ, (Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₂ *
            ((Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ *
              ((Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₁ * F ![y₀, y₁, y₂]))
        from by
      refine lintegral_congr fun y₂ => ?_
      ring]
    exact indicator_mul_setLintegral (measurableSet_Icc) _
  rw [h1]
  have h2 : (∫⁻ y₀ : ℝ, ∫⁻ y₁ : ℝ, ∫⁻ y₂ in Set.Icc (-ℓ/2) (ℓ/2),
        (Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ *
          ((Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₁ * F ![y₀, y₁, y₂]))
      = ∫⁻ y₀ : ℝ, ∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ y₂ in Set.Icc (-ℓ/2) (ℓ/2),
          (Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ * F ![y₀, y₁, y₂] := by
    refine lintegral_congr fun y₀ => ?_
    have h2a : (∫⁻ y₁ : ℝ, ∫⁻ y₂ in Set.Icc (-ℓ/2) (ℓ/2),
          (Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ *
            ((Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₁ * F ![y₀, y₁, y₂]))
        = ∫⁻ y₁ : ℝ, (Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₁ *
            (∫⁻ y₂ in Set.Icc (-ℓ/2) (ℓ/2),
              (Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ * F ![y₀, y₁, y₂]) := by
      refine lintegral_congr fun y₁ => ?_
      rw [show (∫⁻ y₂ in Set.Icc (-ℓ/2) (ℓ/2),
            (Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ *
              ((Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₁ * F ![y₀, y₁, y₂]))
          = ∫⁻ y₂ in Set.Icc (-ℓ/2) (ℓ/2),
              (Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₁ *
                ((Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ * F ![y₀, y₁, y₂])
          from by
        refine lintegral_congr fun y₂ => ?_
        ring]
      exact setLintegral_const_mul' (measurableSet_Icc) _
        (by by_cases hh : y₁ ∈ Set.Icc (-ℓ/2) (ℓ/2) <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, hh]) _
    rw [h2a, indicator_mul_setLintegral (measurableSet_Icc) _]
  rw [h2]
  have h3 : (∫⁻ y₀ : ℝ, ∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ y₂ in Set.Icc (-ℓ/2) (ℓ/2),
        (Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ * F ![y₀, y₁, y₂])
      = ∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2),
          ∫⁻ y₂ in Set.Icc (-ℓ/2) (ℓ/2), F ![y₀, y₁, y₂] := by
    have h3a : (∫⁻ y₀ : ℝ, ∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ y₂ in Set.Icc (-ℓ/2) (ℓ/2),
          (Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ * F ![y₀, y₁, y₂])
        = ∫⁻ y₀ : ℝ, (Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ *
            (∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ y₂ in Set.Icc (-ℓ/2) (ℓ/2), F ![y₀, y₁, y₂]) := by
      refine lintegral_congr fun y₀ => ?_
      have h3b : (∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ y₂ in Set.Icc (-ℓ/2) (ℓ/2),
            (Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ * F ![y₀, y₁, y₂])
          = (Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ *
              (∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ y₂ in Set.Icc (-ℓ/2) (ℓ/2), F ![y₀, y₁, y₂]) := by
        rw [show (∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ y₂ in Set.Icc (-ℓ/2) (ℓ/2),
              (Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ * F ![y₀, y₁, y₂])
            = ∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2),
                (Set.Icc (-ℓ/2) (ℓ/2)).indicator (fun _ => (1 : ℝ≥0∞)) y₀ *
                  (∫⁻ y₂ in Set.Icc (-ℓ/2) (ℓ/2), F ![y₀, y₁, y₂]) from by
          refine lintegral_congr fun y₁ => ?_
          exact setLintegral_const_mul' (measurableSet_Icc) _
            (by by_cases hh : y₀ ∈ Set.Icc (-ℓ/2) (ℓ/2) <;>
              simp [Set.indicator_of_mem, Set.indicator_of_notMem, hh]) _]
        exact setLintegral_const_mul' (measurableSet_Icc) _
          (by by_cases hh : y₀ ∈ Set.Icc (-ℓ/2) (ℓ/2) <;>
            simp [Set.indicator_of_mem, Set.indicator_of_notMem, hh]) _
      rw [h3b]
    rw [h3a, indicator_mul_setLintegral (measurableSet_Icc) _]
  rw [h3]

end Work.BoseFixB1S
