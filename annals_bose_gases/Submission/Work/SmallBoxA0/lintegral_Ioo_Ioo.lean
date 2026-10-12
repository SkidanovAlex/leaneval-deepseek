import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory Set

/-- Pointwise identity behind the triangular change of order: for `0 < r`,
the indicator of `Ioo r R` agrees with the product of the indicator of
`Ioo 0 R` (in `t`) and the indicator of `Ioo 0 t` (in `r`). -/
private lemma indicator_Ioo_eq {R r : ℝ} {f : ℝ → ENNReal} (hr0 : 0 < r) :
    (Set.Ioo r R).indicator f =
      fun t => (Set.Ioo (0:ℝ) R).indicator f t
        * (Set.Ioo (0:ℝ) t).indicator (fun _ => (1:ENNReal)) r := by
  funext t
  rw [Set.indicator_apply, Set.indicator_apply, Set.indicator_apply]
  simp only [Set.mem_Ioo]
  by_cases ht : r < t
  · have h0t : 0 < t := lt_trans hr0 ht
    simp [ht, h0t, hr0]
  · simp [ht, hr0]

/-- For `r ∉ Ioo 0 R` the product-integrator vanishes identically. -/
private lemma indicator_mul_eq_zero_of_notMem {R r : ℝ} {f : ℝ → ENNReal}
    (hr : r ∉ Set.Ioo (0:ℝ) R) :
    ∀ t, (Set.Ioo (0:ℝ) R).indicator f t
        * (Set.Ioo (0:ℝ) t).indicator (fun _ => (1:ENNReal)) r = 0 := by
  intro t
  rw [Set.indicator_apply, Set.indicator_apply]
  simp only [Set.mem_Ioo]
  by_cases hr0 : 0 < r
  · have hRr : R ≤ r := not_lt.mp (fun h => hr ⟨hr0, h⟩)
    by_cases h : 0 < t ∧ t < R
    · have hnrt : ¬ (r < t) := by intro hrt; linarith [h.2, hRr, hrt]
      simp [h, hnrt]
    · simp [h]
  · simp [hr0]

/-- For `t ∉ Ioo 0 R` the product-integrator vanishes identically. -/
private lemma indicator_mul_eq_zero_of_notMem' {R t : ℝ} {f : ℝ → ENNReal}
    (ht : t ∉ Set.Ioo (0:ℝ) R) :
    ∀ r, (Set.Ioo (0:ℝ) R).indicator f t
        * (Set.Ioo (0:ℝ) t).indicator (fun _ => (1:ENNReal)) r = 0 := by
  intro r
  rw [Set.indicator_of_notMem ht]
  simp

/-- The product-integrator is almost everywhere measurable on the product measure. -/
private lemma aemeasurable_gfun {R : ℝ} {f : ℝ → ENNReal}
    (hf : AEMeasurable f (volume : Measure ℝ)) :
    AEMeasurable (fun p : ℝ × ℝ =>
      (Set.Ioo (0:ℝ) R).indicator f p.2
        * (Set.Ioo (0:ℝ) p.2).indicator (fun _ => (1:ENNReal)) p.1)
      ((volume : Measure ℝ).prod volume) := by
  have hA : AEMeasurable (fun p : ℝ × ℝ => (Set.Ioo (0:ℝ) R).indicator f p.2)
      ((volume : Measure ℝ).prod volume) := (hf.indicator measurableSet_Ioo).comp_snd
  have hD : MeasurableSet {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_snd)
  have hB : AEMeasurable
      (fun p : ℝ × ℝ => (Set.Ioo (0:ℝ) p.2).indicator (fun _ => (1:ENNReal)) p.1)
      ((volume : Measure ℝ).prod volume) := by
    have hfun : (fun p : ℝ × ℝ => (Set.Ioo (0:ℝ) p.2).indicator (fun _ => (1:ENNReal)) p.1)
        = ({p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} : Set (ℝ × ℝ)).indicator
            (fun _ => (1:ENNReal)) := by
      funext p
      rw [Set.indicator_apply, Set.indicator_apply]
      simp only [Set.mem_Ioo, Set.mem_ofPred_eq]
    rw [hfun]
    exact ((measurable_const : Measurable (fun _ : ℝ × ℝ => (1:ENNReal))).indicator
      hD).aemeasurable
  exact hA.mul hB

set_option linter.unusedVariables false in
theorem lintegral_Ioo_Ioo {R : ℝ} (hR : 0 < R) {f : ℝ → ENNReal}
    (hf : AEMeasurable f MeasureTheory.volume) :
    ∫⁻ r in Set.Ioo (0 : ℝ) R, (∫⁻ t in Set.Ioo r R, f t) =
      ∫⁻ t in Set.Ioo (0 : ℝ) R, f t * ENNReal.ofReal t := by
  set g : ℝ → ℝ → ENNReal := fun r t =>
    (Set.Ioo (0:ℝ) R).indicator f t
      * (Set.Ioo (0:ℝ) t).indicator (fun _ => (1:ENNReal)) r with hg
  have hgmeas : AEMeasurable (Function.uncurry g) ((volume:Measure ℝ).prod volume) := by
    rw [hg]
    exact aemeasurable_gfun hf
  have hswap : ∫⁻ r, ∫⁻ t, g r t = ∫⁻ t, ∫⁻ r, g r t := lintegral_lintegral_swap hgmeas
  have hL : ∫⁻ r in Set.Ioo (0:ℝ) R, (∫⁻ t in Set.Ioo r R, f t) = ∫⁻ r, ∫⁻ t, g r t := by
    rw [← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro r
    by_cases hr : r ∈ Set.Ioo (0:ℝ) R
    · rw [Set.indicator_of_mem hr,
        ← lintegral_indicator (s := Set.Ioo r R) measurableSet_Ioo (f := f)]
      apply lintegral_congr
      intro t
      rw [hg]
      exact congrFun (indicator_Ioo_eq (R := R) (f := f) hr.1) t
    · rw [Set.indicator_of_notMem hr]
      symm
      rw [show (∫⁻ t, g r t) = ∫⁻ t, (0:ENNReal) from
        lintegral_congr (fun t => by rw [hg]; exact indicator_mul_eq_zero_of_notMem hr t)]
      simp
  have hR' : ∫⁻ t in Set.Ioo (0:ℝ) R, f t * ENNReal.ofReal t = ∫⁻ t, ∫⁻ r, g r t := by
    rw [← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro t
    by_cases ht : t ∈ Set.Ioo (0:ℝ) R
    · rw [Set.indicator_of_mem ht, hg]
      rw [lintegral_const_mul _
        ((measurable_const : Measurable (fun _ : ℝ => (1:ENNReal))).indicator measurableSet_Ioo)]
      have hvol : (∫⁻ a : ℝ, (Set.Ioo (0:ℝ) t).indicator (fun _ => (1:ENNReal)) a)
          = volume (Set.Ioo (0:ℝ) t) :=
        lintegral_indicator_one measurableSet_Ioo
      rw [hvol, Real.volume_Ioo, Set.indicator_of_mem ht, sub_zero]
    · rw [Set.indicator_of_notMem ht]
      symm
      rw [show (∫⁻ r, g r t) = ∫⁻ r, (0:ENNReal) from
        lintegral_congr (fun r => by rw [hg]; exact indicator_mul_eq_zero_of_notMem' ht r)]
      simp
  rw [hL, hswap, ← hR']

end Work.SmallBoxA0
