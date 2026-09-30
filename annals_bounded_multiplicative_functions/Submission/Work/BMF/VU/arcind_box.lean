import Mathlib
import Submission.Work.BMF.kdr_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Wrapped-arc indicators: the one-dimensional integral and the box-product integral

For `arcInd a δ t = 1_{∃ z : ℤ, |t - a - z| ≤ δ}` (`Submission.Work.BMF.kdr_defs`) we prove
`∫_0^1 arcInd a δ = min (2δ) 1` for every real `a` and `δ ≥ 0`, and the product form
`∫_{[0,1]^m} ∏_j arcInd (a j) (δ j) = ∏_j min (2 δ j) 1`.
-/

namespace Work.BMF

open MeasureTheory Finset Set
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The wrapped arc of radius `δ` around `a`, as a subset of `ℝ`. -/
def arcSet (a δ : ℝ) : Set ℝ := {t : ℝ | ∃ z : ℤ, |t - a - (z : ℝ)| ≤ δ}

@[simp] lemma mem_arcSet {a δ t : ℝ} :
    t ∈ arcSet a δ ↔ ∃ z : ℤ, |t - a - (z : ℝ)| ≤ δ := Iff.rfl

lemma arcInd_nonneg' (a δ t : ℝ) : 0 ≤ arcInd a δ t := by
  unfold arcInd; split_ifs <;> norm_num

lemma arcInd_le_one' (a δ t : ℝ) : arcInd a δ t ≤ 1 := by
  unfold arcInd; split_ifs <;> norm_num

lemma arcInd_eq_indicator' (a δ : ℝ) :
    arcInd a δ = (arcSet a δ).indicator (fun _ => (1 : ℝ)) := by
  funext t
  simp only [arcInd]
  split_ifs with h
  · exact (Set.indicator_of_mem h (fun _ => (1 : ℝ))).symm
  · exact (Set.indicator_of_notMem h (fun _ => (1 : ℝ))).symm

lemma measurableSet_arcSet' (a δ : ℝ) : MeasurableSet (arcSet a δ) := by
  have h : arcSet a δ = ⋃ z : ℤ, Set.Icc (a + (z : ℝ) - δ) (a + (z : ℝ) + δ) := by
    ext t
    simp only [mem_arcSet, Set.mem_iUnion, Set.mem_Icc, abs_le]
    constructor
    · rintro ⟨z, h1, h2⟩; exact ⟨z, by linarith, by linarith⟩
    · rintro ⟨z, h1, h2⟩; exact ⟨z, by linarith, by linarith⟩
  rw [h]
  exact MeasurableSet.iUnion fun z => measurableSet_Icc

lemma measurable_arcInd' (a δ : ℝ) : Measurable (arcInd a δ) := by
  rw [arcInd_eq_indicator']
  exact measurable_const.indicator (measurableSet_arcSet' a δ)

lemma arcInd_shift' (a δ t : ℝ) : arcInd a δ t = arcInd 0 δ (t - a) := by
  have h : (∃ z : ℤ, |t - a - (z : ℝ)| ≤ δ) ↔ (∃ z : ℤ, |t - a - 0 - (z : ℝ)| ≤ δ) := by
    constructor <;> rintro ⟨z, hz⟩ <;> exact ⟨z, by simpa using hz⟩
  unfold arcInd
  by_cases hp : ∃ z : ℤ, |t - a - (z : ℝ)| ≤ δ
  · rw [if_pos hp, if_pos (h.mp hp)]
  · rw [if_neg hp, if_neg (fun hq => hp (h.mpr hq))]

lemma arcInd_zero_periodic' (δ : ℝ) : Function.Periodic (arcInd 0 δ) 1 := by
  intro x
  have h : (∃ z : ℤ, |x + 1 - 0 - (z : ℝ)| ≤ δ) ↔ (∃ z : ℤ, |x - 0 - (z : ℝ)| ≤ δ) := by
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z - 1, ?_⟩
      rw [abs_le] at hz ⊢
      push_cast
      constructor <;> linarith [hz.1, hz.2]
    · rintro ⟨z, hz⟩
      refine ⟨z + 1, ?_⟩
      rw [abs_le] at hz ⊢
      push_cast
      constructor <;> linarith [hz.1, hz.2]
  unfold arcInd
  by_cases hp : ∃ z : ℤ, |x + 1 - 0 - (z : ℝ)| ≤ δ
  · rw [if_pos hp, if_pos (h.mp hp)]
  · rw [if_neg hp, if_neg (fun hq => hp (h.mpr hq))]

/-- The volume of the wrapped arc of radius `δ` inside the fundamental domain `(0,1]`. -/
lemma volume_arcSet_zero (δ : ℝ) (hδ : 0 ≤ δ) :
    volume (arcSet 0 δ ∩ Set.Ioc (0 : ℝ) 1) = ENNReal.ofReal (min (2 * δ) 1) := by
  rcases le_or_gt (1 / 2 : ℝ) δ with hhalf | hhalf
  · have hset : arcSet 0 δ ∩ Set.Ioc (0 : ℝ) 1 = Set.Ioc (0 : ℝ) 1 := by
      ext t
      refine ⟨fun h => h.2, fun ht => ⟨?_, ht⟩⟩
      rw [Set.mem_Ioc] at ht
      rcases le_or_gt t (1 / 2) with ht2 | ht2
      · refine ⟨0, ?_⟩
        rw [abs_le]
        push_cast
        constructor <;> linarith [ht.1, ht2, hhalf]
      · refine ⟨1, ?_⟩
        rw [abs_le]
        push_cast
        constructor <;> linarith [ht.1, ht.2, ht2, hhalf]
    rw [hset, Real.volume_Ioc, sub_zero, min_eq_right (by linarith), ENNReal.ofReal_one]
  · have hset : arcSet 0 δ ∩ Set.Ioc (0 : ℝ) 1 = Set.Ioc (0 : ℝ) δ ∪ Set.Icc (1 - δ) 1 := by
      ext t
      refine ⟨?_, ?_⟩
      · rintro ⟨hz, ht⟩
        rw [Set.mem_Ioc] at ht
        obtain ⟨z, hz⟩ := hz
        have hz' : |t - (z : ℝ)| ≤ δ := by simpa using hz
        rw [abs_le] at hz'
        have hzlo : (-1 : ℝ) < (z : ℝ) := by linarith [hz'.1, hz'.2, ht.1, hhalf]
        have hzhi : (z : ℝ) < 2 := by linarith [hz'.1, hz'.2, ht.2, hhalf]
        have hzz : z = 0 ∨ z = 1 := by
          have h1 : (-1 : ℤ) < z := by exact_mod_cast hzlo
          have h2 : z < (2 : ℤ) := by exact_mod_cast hzhi
          omega
        rcases hzz with rfl | rfl
        · left
          rw [Set.mem_Ioc]
          push_cast at hz'
          exact ⟨ht.1, by linarith [hz'.2]⟩
        · right
          rw [Set.mem_Icc]
          push_cast at hz'
          exact ⟨by linarith [hz'.1], ht.2⟩
      · rintro (ht | ht)
        · rw [Set.mem_Ioc] at ht
          refine ⟨?_, ?_⟩
          · refine ⟨0, ?_⟩
            rw [abs_le]
            push_cast
            constructor <;> linarith [ht.1, ht.2]
          · exact ⟨ht.1, by linarith [ht.2, hhalf]⟩
        · rw [Set.mem_Icc] at ht
          refine ⟨?_, ?_⟩
          · refine ⟨1, ?_⟩
            rw [abs_le]
            push_cast
            constructor <;> linarith [ht.1, ht.2]
          · exact ⟨by linarith [ht.1], ht.2⟩
    rw [hset]
    have hdisj : Disjoint (Set.Ioc (0 : ℝ) δ) (Set.Icc (1 - δ) 1) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      rw [Set.mem_Ioc] at hx
      rw [Set.mem_Icc] at hx'
      linarith [hx.2, hx'.1, hhalf]
    rw [measure_union hdisj measurableSet_Icc, Real.volume_Ioc, Real.volume_Icc,
      show δ - (0 : ℝ) = δ by ring, show (1 : ℝ) - (1 - δ) = δ by ring,
      ← ENNReal.ofReal_add hδ hδ, show δ + δ = 2 * δ by ring, min_eq_left (by linarith)]

/-- The one-dimensional wrapped-arc integral over `(0,1]`. -/
lemma integral_arcInd_zero_Ioc (δ : ℝ) (hδ : 0 ≤ δ) :
    (∫ t in Set.Ioc (0 : ℝ) 1, arcInd 0 δ t) = min (2 * δ) 1 := by
  have hS : MeasurableSet (arcSet 0 δ) := measurableSet_arcSet' 0 δ
  rw [arcInd_eq_indicator' 0 δ, MeasureTheory.setIntegral_indicator hS]
  rw [MeasureTheory.setIntegral_const, measureReal_def, smul_eq_mul, mul_one, Set.inter_comm,
    volume_arcSet_zero δ hδ,
    ENNReal.toReal_ofReal (le_min (by linarith) zero_le_one)]

/-- The one-dimensional wrapped-arc integral: `∫_0^1 arcInd a δ = min (2δ) 1` for `δ ≥ 0`,
for **every** real centre `a`. -/
theorem integral_arcInd_one (a : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫ t in (0 : ℝ)..1, arcInd a δ t) = min (2 * δ) 1 := by
  set g : ℝ → ℝ := fun s => arcInd 0 δ s with hg
  have hgp : Function.Periodic g 1 := arcInd_zero_periodic' δ
  have hgoal : (∫ t in (0 : ℝ)..1, arcInd a δ t) = ∫ t in (0 : ℝ)..1, g (t - a) :=
    intervalIntegral.integral_congr fun t _ => by
      rw [hg]
      exact arcInd_shift' a δ t
  rw [hgoal, intervalIntegral.integral_comp_sub_right (f := g) a,
    show (0 : ℝ) - a = -a by ring, show (1 : ℝ) - a = -a + 1 by ring,
    Function.Periodic.intervalIntegral_add_eq hgp (-a) 0, zero_add, hg,
    intervalIntegral.integral_of_le zero_le_one]
  exact integral_arcInd_zero_Ioc δ hδ

/-- The one-dimensional wrapped-arc integral over the closed unit interval. -/
lemma integral_arcInd_one_Icc (a : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫ t in Set.Icc (0 : ℝ) 1, arcInd a δ t) = min (2 * δ) 1 := by
  rw [← MeasureTheory.restrict_Ioc_eq_restrict_Icc, ← intervalIntegral.integral_of_le zero_le_one]
  exact integral_arcInd_one a hδ

/-- **Box-product integral.**  Over the unit box, a product of wrapped-arc indicators factors into
the product of the one-dimensional integrals. -/
theorem box_product_arcInd_integral (m : ℕ) (a δ : Fin m → ℝ) (hδ : ∀ j, 0 ≤ δ j) :
    (∫ α in unitBox m, ∏ j : Fin m, arcInd (a j) (δ j) (α j))
      = ∏ j : Fin m, min (2 * δ j) 1 := by
  have hmp : (volume : Measure (Fin m → ℝ)).restrict (unitBox m)
      = Measure.pi (fun _ : Fin m => volume.restrict (Set.Icc (0:ℝ) 1)) := by
    rw [unitBox, volume_pi]
    exact Measure.restrict_pi_pi (fun _ : Fin m => volume) (fun _ : Fin m => Set.Icc (0:ℝ) 1)
  have hF := MeasureTheory.integral_fintype_prod_eq_prod
    (𝕜 := ℝ) (μ := fun _ : Fin m => volume.restrict (Set.Icc (0:ℝ) 1))
    (f := fun j : Fin m => arcInd (a j) (δ j))
  rw [hmp, hF]
  exact Finset.prod_congr rfl fun j _ => integral_arcInd_one_Icc (a j) (hδ j)

end Work.BMF
