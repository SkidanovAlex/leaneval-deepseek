import Mathlib
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.vocab

/-!
# The standard exponential law on `ℝ` (rate 1)

Elementary facts about a measure `μ` on `ℝ` with CDF `x ↦ 1 - exp(-x)`:
values on intervals and half-lines, `μ {0} = 0`, and the memorylessness (shift) identity
`(μ ↾ (c,∞)) shifted by -c = exp(-c) • μ`.
-/

open MeasureTheory
open scoped ENNReal

namespace Work.ChenPlan.LinearSieve.Selberg.Alt

/-- `HasExpLaw μ`: `μ` is the standard exponential law (rate `1`) on `ℝ`, described by its CDF. -/
def HasExpLaw (μ : Measure ℝ) : Prop :=
  ∀ x : ℝ, μ (Set.Iic x) = ENNReal.ofReal (1 - Real.exp (-x))

lemma HasExpLaw.Ioc {μ : Measure ℝ} (h : HasExpLaw μ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    μ (Set.Ioc a b) = ENNReal.ofReal (Real.exp (-a) - Real.exp (-b)) := by
  have hnonneg1 : 0 ≤ 1 - Real.exp (-a) := by
    have : Real.exp (-a) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    linarith
  have hnonneg2 : 0 ≤ Real.exp (-a) - Real.exp (-b) := by
    have : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hset : Set.Iic b = Set.Iic a ∪ Set.Ioc a b := by
    ext x
    simp only [Set.mem_Iic, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro hx
      by_cases h' : x ≤ a
      · exact Or.inl h'
      · exact Or.inr ⟨not_le.mp h', hx⟩
    · rintro (h' | ⟨h1, h2⟩)
      · exact le_trans h' hab
      · exact h2
  have hdisj : Disjoint (Set.Iic a) (Set.Ioc a b) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact absurd hy.1 (not_lt.mpr hx)
  have hunion : μ (Set.Iic b) = μ (Set.Iic a) + μ (Set.Ioc a b) := by
    rw [hset, measure_union hdisj measurableSet_Ioc]
  have key : μ (Set.Ioc a b) = μ (Set.Iic b) - μ (Set.Iic a) :=
    (ENNReal.sub_eq_of_eq_add (by rw [h a]; exact ENNReal.ofReal_ne_top)
      (by rw [add_comm]; exact hunion)).symm
  rw [key, h a, h b,
    show (1:ℝ) - Real.exp (-b) = (1 - Real.exp (-a)) + (Real.exp (-a) - Real.exp (-b)) from by ring,
    ENNReal.ofReal_add hnonneg1 hnonneg2, ENNReal.add_sub_cancel_left ENNReal.ofReal_ne_top]

lemma HasExpLaw.Ioi {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : HasExpLaw μ) {c : ℝ}
    (hc : 0 ≤ c) : μ (Set.Ioi c) = ENNReal.ofReal (Real.exp (-c)) := by
  have hnn : 0 ≤ 1 - Real.exp (-c) := by
    have : Real.exp (-c) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    linarith
  have hset : (Set.univ : Set ℝ) = Set.Iic c ∪ Set.Ioi c := by
    ext x; simp only [Set.mem_univ, Set.mem_union, Set.mem_Iic, Set.mem_Ioi, true_iff]
    exact le_or_gt x c
  have hdisj : Disjoint (Set.Iic c) (Set.Ioi c) := by
    rw [Set.disjoint_left]; intro x hx hy
    simp only [Set.mem_Ioi] at hy; exact absurd hy (not_lt.mpr hx)
  have hunion : μ (Set.Ioi c) + μ (Set.Iic c) = 1 := by
    have h2 : μ (Set.Iic c) + μ (Set.Ioi c) = 1 := by
      rw [← measure_union hdisj measurableSet_Ioi, ← hset, measure_univ]
    rw [add_comm]; exact h2
  have h1 : μ (Set.Ioi c) = 1 - μ (Set.Iic c) :=
    ENNReal.eq_sub_of_add_eq (by rw [h c]; exact ENNReal.ofReal_ne_top) hunion
  rw [h1, h c]
  have h2 : ENNReal.ofReal (Real.exp (-c)) = 1 - ENNReal.ofReal (1 - Real.exp (-c)) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hnn]
    congr 1; ring
  rw [h2]

lemma HasExpLaw.singleton_zero {μ : Measure ℝ} (h : HasExpLaw μ) : μ {0} = 0 := by
  have hsub : ({0} : Set ℝ) ⊆ Set.Iic 0 := by
    intro x hx; simp only [Set.mem_singleton_iff] at hx; subst hx
    show (0:ℝ) ≤ 0; exact le_refl 0
  have hle : μ {0} ≤ μ (Set.Iic (0:ℝ)) := measure_mono hsub
  have h0 : μ (Set.Iic (0:ℝ)) = 0 := by rw [h 0]; simp
  rw [h0] at hle
  exact le_antisymm hle (by simp)

lemma HasExpLaw.Ioi_zero {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : HasExpLaw μ) :
    μ (Set.Ioi 0) = 1 := by
  rw [h.Ioi le_rfl]; norm_num

/-- Memorylessness: the restriction of `μ` to `(c,∞)`, shifted by `-c`, is `exp(-c) • μ`. -/
lemma HasExpLaw.shift {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : HasExpLaw μ) {c : ℝ}
    (hc : 0 ≤ c) :
    (μ.restrict (Set.Ioi c)).map (fun u => u - c) = ENNReal.ofReal (Real.exp (-c)) • μ := by
  haveI : IsFiniteMeasure (μ.restrict (Set.Ioi c)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]; exact measure_lt_top μ _⟩
  refine Measure.ext_of_Iic _ _ fun x => ?_
  have hm : Measurable (fun u : ℝ => u - c) := by fun_prop
  rw [Measure.map_apply hm measurableSet_Iic, Measure.smul_apply, smul_eq_mul]
  rw [Measure.restrict_apply (measurableSet_Iic.preimage hm)]
  rcases le_or_gt 0 x with hx | hx
  · have hset2 : (fun u : ℝ => u - c) ⁻¹' Set.Iic x ∩ Set.Ioi c = Set.Ioc c (x + c) := by
      ext u; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ioi,
        Set.mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩
    rw [hset2, HasExpLaw.Ioc h hc (by linarith), h x, ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    congr 1
    rw [show -(x+c) = -c + -x by ring, Real.exp_add]; ring
  · have hset2 : (fun u : ℝ => u - c) ⁻¹' Set.Iic x ∩ Set.Ioi c = ∅ := by
      ext u; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ioi,
        Set.mem_empty_iff_false, iff_false, not_and]
      intro h1 h2; linarith
    rw [hset2, measure_empty, h x]
    have hneg : 1 - Real.exp (-x) ≤ 0 := by
      have : 1 ≤ Real.exp (-x) := by rw [Real.one_le_exp_iff]; linarith
      linarith
    rw [ENNReal.ofReal_of_nonpos hneg, mul_zero]

end Work.ChenPlan.LinearSieve.Selberg.Alt
