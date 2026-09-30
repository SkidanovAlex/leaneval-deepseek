import Mathlib
import Submission.Work.BMF.kdr_defs
import Submission.Work.BMF.VU.arcind_box

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The counting function `ν` and its first two moments

For `δ : Fin m → ℝ` and centres `a i : Fin m → ℝ`, the counting function is
`ν α = Σ_i ∏_j arcInd (a i j) (δ j) (α j)` on the unit box `[0,1]^m`. We prove
`∫ ν = n · ∏_j min (2 δ j) 1` and the second-moment bound
`∫ ν² ≤ (∏_j min (2 δ j) 1) · #{pairs (i,i') whose `2δ`-distance conditions all hold}`.
-/

namespace Work.BMF

open MeasureTheory Finset Set
open scoped BigOperators

attribute [local instance] Classical.propDecidable

lemma measurableSet_unitBox (m : ℕ) : MeasurableSet (unitBox m) :=
  MeasurableSet.pi (Set.Finite.countable Set.finite_univ) fun _ _ => measurableSet_Icc

lemma volume_unitBox (m : ℕ) : volume (unitBox m) = 1 := by
  rw [unitBox, volume_pi, Measure.pi_pi]
  simp

lemma isFiniteMeasure_restrict_unitBox (m : ℕ) : IsFiniteMeasure (volume.restrict (unitBox m)) := by
  refine isFiniteMeasure_restrict.mpr ?_
  rw [volume_unitBox m]
  exact ENNReal.one_ne_top

/-- A product of wrapped-arc indicators, as a function on the box, is measurable. -/
lemma measurable_prod_arcInd (m : ℕ) (a δ : Fin m → ℝ) :
    Measurable fun α : Fin m → ℝ => ∏ j : Fin m, arcInd (a j) (δ j) (α j) :=
  Finset.measurable_fun_prod Finset.univ fun j _ =>
    (measurable_arcInd' (a j) (δ j)).comp (measurable_pi_apply j)

/-- A product of factors in `[0,1]` is at most `1` (proved by induction, to avoid the
`MulLeftMono ℝ` typeclass). -/
lemma finset_prod_le_one_of_mem_Icc {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 := by
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.prod_insert hi]
      have h1i : f i ≤ 1 := h1 i (Finset.mem_insert_self i s)
      have h0s : ∀ x ∈ s, 0 ≤ f x := fun x hx => h0 x (Finset.mem_insert_of_mem hx)
      have h1s : ∀ x ∈ s, f x ≤ 1 := fun x hx => h1 x (Finset.mem_insert_of_mem hx)
      have ihs : ∏ x ∈ s, f x ≤ 1 := ih h0s h1s
      have hps : 0 ≤ ∏ x ∈ s, f x := Finset.prod_nonneg h0s
      calc f i * ∏ x ∈ s, f x ≤ 1 * ∏ x ∈ s, f x := mul_le_mul_of_nonneg_right h1i hps
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left ihs zero_le_one
        _ = 1 := by ring

/-- A product of wrapped-arc indicators is a nonnegative function bounded by `1`. -/
lemma prod_arcInd_mem_Icc (m : ℕ) (a δ : Fin m → ℝ) (α : Fin m → ℝ) :
    (∏ j : Fin m, arcInd (a j) (δ j) (α j)) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Finset.prod_nonneg fun j _ => arcInd_nonneg' _ _ _,
    finset_prod_le_one_of_mem_Icc Finset.univ _
      (fun j _ => arcInd_nonneg' _ _ _) (fun j _ => arcInd_le_one' _ _ _)⟩

lemma integrable_prod_arcInd (m : ℕ) (a δ : Fin m → ℝ) :
    Integrable (fun α : Fin m → ℝ => ∏ j : Fin m, arcInd (a j) (δ j) (α j))
      (volume.restrict (unitBox m)) := by
  haveI := isFiniteMeasure_restrict_unitBox m
  refine Integrable.of_bound (measurable_prod_arcInd m a δ).aestronglyMeasurable 1 ?_
  filter_upwards with α
  rw [Real.norm_of_nonneg (Finset.prod_nonneg fun j _ => arcInd_nonneg' _ _ _)]
  exact (prod_arcInd_mem_Icc m a δ α).2

lemma integrable_mul_prod_arcInd (m : ℕ) (a a' δ : Fin m → ℝ) :
    Integrable (fun α : Fin m → ℝ =>
      (∏ j : Fin m, arcInd (a j) (δ j) (α j)) * (∏ j : Fin m, arcInd (a' j) (δ j) (α j)))
      (volume.restrict (unitBox m)) := by
  haveI := isFiniteMeasure_restrict_unitBox m
  refine Integrable.of_bound ((measurable_prod_arcInd m a δ).mul
    (measurable_prod_arcInd m a' δ)).aestronglyMeasurable 1 ?_
  filter_upwards with α
  have h1 := (prod_arcInd_mem_Icc m a δ α).1
  have h2 := (prod_arcInd_mem_Icc m a δ α).2
  have h3 := (prod_arcInd_mem_Icc m a' δ α).1
  have h4 := (prod_arcInd_mem_Icc m a' δ α).2
  rw [Real.norm_of_nonneg (mul_nonneg h1 h3)]
  nlinarith

/-- **First moment of `ν`.** -/
theorem integral_nu_eq_fin (m n : ℕ) (δ : Fin m → ℝ) (hδ : ∀ j, 0 ≤ δ j)
    (a : Fin n → (Fin m → ℝ)) :
    (∫ α in unitBox m, ∑ i : Fin n, ∏ j : Fin m, arcInd (a i j) (δ j) (α j))
      = (n : ℝ) * ∏ j : Fin m, min (2 * δ j) 1 := by
  rw [MeasureTheory.integral_finsetSum (s := Finset.univ)
    (f := fun i (α : Fin m → ℝ) => ∏ j : Fin m, arcInd (a i j) (δ j) (α j))
    (fun i _ => integrable_prod_arcInd m (a i) δ)]
  rw [Finset.sum_congr rfl (fun i _ => box_product_arcInd_integral m (a i) δ hδ),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- A pair of indicators centred at `x` and `y` (same radius `δ`) vanishes identically on the box
as soon as the two wrapped arcs of radius `2δ` do not meet. -/
lemma arcInd_mul_eq_zero (x y δ : ℝ) (α : ℝ)
    (h : ¬ ∃ z : ℤ, |x - y - (z : ℝ)| ≤ 2 * δ) :
    arcInd x δ α * arcInd y δ α = 0 := by
  by_contra hne
  have h1 : arcInd x δ α ≠ 0 := fun hh => hne (by rw [hh, zero_mul])
  have h2 : arcInd y δ α ≠ 0 := fun hh => hne (by rw [hh, mul_zero])
  have hw1 : ∃ z : ℤ, |α - x - (z : ℝ)| ≤ δ := by
    by_contra hc
    exact h1 (by unfold arcInd; rw [if_neg hc])
  have hw2 : ∃ z : ℤ, |α - y - (z : ℝ)| ≤ δ := by
    by_contra hc
    exact h2 (by unfold arcInd; rw [if_neg hc])
  obtain ⟨z₁, hz₁⟩ := hw1
  obtain ⟨z₂, hz₂⟩ := hw2
  apply h
  refine ⟨z₂ - z₁, ?_⟩
  push_cast
  have hkey : x - y - ((z₂ : ℝ) - (z₁ : ℝ)) = (α - y - (z₂ : ℝ)) - (α - x - (z₁ : ℝ)) := by
    ring
  rw [hkey]
  exact (abs_sub _ _).trans (by linarith)

/-- Swapping a finite sum with the box integral, for a family `g` of integrable functions. -/
lemma swap_sum_integral {m n : ℕ} (g : Fin n × Fin n → (Fin m → ℝ) → ℝ)
    (hg : ∀ p, Integrable (g p) (volume.restrict (unitBox m))) :
    (∫ α in unitBox m, ∑ p : Fin n × Fin n, g p α)
      = ∑ p : Fin n × Fin n, ∫ α in unitBox m, g p α :=
  MeasureTheory.integral_finsetSum (s := Finset.univ) (f := g) (fun p _ => hg p)

/-- Swapping a finite sum with the box integral, for a family indexed by `Fin n`. -/
lemma swap_sum_integral' {m n : ℕ} (g : Fin n → (Fin m → ℝ) → ℝ)
    (hg : ∀ p, Integrable (g p) (volume.restrict (unitBox m))) :
    (∫ α in unitBox m, ∑ p : Fin n, g p α)
      = ∑ p : Fin n, ∫ α in unitBox m, g p α :=
  MeasureTheory.integral_finsetSum (s := Finset.univ) (f := g) (fun p _ => hg p)

/-- A pair term of the second moment is bounded by `V` when the `2δ`-conditions all hold, and
vanishes identically otherwise. -/
lemma pair_term_le {m : ℕ} (δ : Fin m → ℝ) (hδ : ∀ j, 0 ≤ δ j) (x y : Fin m → ℝ) :
    (∫ α in unitBox m, (∏ j : Fin m, arcInd (x j) (δ j) (α j)) *
        (∏ j : Fin m, arcInd (y j) (δ j) (α j)))
      ≤ (∏ j : Fin m, min (2 * δ j) 1) *
        (if (∀ j : Fin m, ∃ z : ℤ, |x j - y j - (z : ℝ)| ≤ 2 * δ j) then (1 : ℝ) else 0) := by
  have hVnn : 0 ≤ ∏ j : Fin m, min (2 * δ j) 1 :=
    Finset.prod_nonneg fun j _ => le_min (by linarith [hδ j]) zero_le_one
  by_cases hp : ∀ j : Fin m, ∃ z : ℤ, |x j - y j - (z : ℝ)| ≤ 2 * δ j
  · rw [if_pos hp]
    have hb : (∫ α in unitBox m, (∏ j : Fin m, arcInd (x j) (δ j) (α j)) *
          (∏ j : Fin m, arcInd (y j) (δ j) (α j))) ≤ ∫ α in unitBox m, ∏ j : Fin m, arcInd (x j) (δ j) (α j) := by
      refine integral_mono (integrable_mul_prod_arcInd m x y δ) (integrable_prod_arcInd m x δ) ?_
      intro α
      exact mul_le_of_le_one_right (prod_arcInd_mem_Icc m x δ α).1 (prod_arcInd_mem_Icc m y δ α).2
    calc (∫ α in unitBox m, (∏ j : Fin m, arcInd (x j) (δ j) (α j)) *
          (∏ j : Fin m, arcInd (y j) (δ j) (α j)))
        ≤ ∫ α in unitBox m, ∏ j : Fin m, arcInd (x j) (δ j) (α j) := hb
      _ = (∏ j : Fin m, min (2 * δ j) 1) := box_product_arcInd_integral m x δ hδ
      _ = (∏ j : Fin m, min (2 * δ j) 1) * 1 := by ring
  · rw [if_neg hp]
    have hzero : ∀ α : Fin m → ℝ, (∏ j : Fin m, arcInd (x j) (δ j) (α j)) *
        (∏ j : Fin m, arcInd (y j) (δ j) (α j)) = 0 := by
      intro α
      obtain ⟨j, hj⟩ := not_forall.mp hp
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (arcInd_mul_eq_zero (x j) (y j) (δ j) (α j) hj)
    rw [show (∫ α in unitBox m, (∏ j : Fin m, arcInd (x j) (δ j) (α j)) *
        (∏ j : Fin m, arcInd (y j) (δ j) (α j))) = ∫ α in unitBox m, (0 : ℝ) from
      setIntegral_congr_fun (measurableSet_unitBox m) fun α _ => hzero α, mul_zero]
    simp

set_option maxHeartbeats 1000000 in
/-- **Second moment of `ν`.** -/
theorem integral_nu_sq_le_fin (m n : ℕ) (δ : Fin m → ℝ) (hδ : ∀ j, 0 ≤ δ j)
    (a : Fin n → (Fin m → ℝ)) :
    (∫ α in unitBox m, (∑ i : Fin n, ∏ j : Fin m, arcInd (a i j) (δ j) (α j)) ^ 2)
      ≤ (∏ j : Fin m, min (2 * δ j) 1) *
        ((Finset.univ.filter (fun p : Fin n × Fin n => ∀ j : Fin m, ∃ z : ℤ,
            |a p.1 j - a p.2 j - z| ≤ 2 * δ j)).card : ℝ) := by
  have hsq : ∀ α : Fin m → ℝ, (∑ i : Fin n, ∏ j : Fin m, arcInd (a i j) (δ j) (α j)) ^ 2
      = ∑ p : Fin n × Fin n, (∏ j : Fin m, arcInd (a p.1 j) (δ j) (α j)) *
          (∏ j : Fin m, arcInd (a p.2 j) (δ j) (α j)) := by
    intro α
    rw [pow_two, Fintype.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
  rw [show (∫ α in unitBox m, (∑ i : Fin n, ∏ j : Fin m, arcInd (a i j) (δ j) (α j)) ^ 2)
      = ∫ α in unitBox m, ∑ p : Fin n × Fin n, (∏ j : Fin m, arcInd (a p.1 j) (δ j) (α j)) *
          (∏ j : Fin m, arcInd (a p.2 j) (δ j) (α j)) from
        setIntegral_congr_fun (measurableSet_unitBox m) fun α _ => hsq α]
  rw [swap_sum_integral (fun p α => (∏ j : Fin m, arcInd (a p.1 j) (δ j) (α j)) *
      (∏ j : Fin m, arcInd (a p.2 j) (δ j) (α j))) (fun p => integrable_mul_prod_arcInd m (a p.1) (a p.2) δ)]
  refine (Finset.sum_le_sum fun p _ => pair_term_le δ hδ (a p.1) (a p.2)).trans ?_
  rw [← Finset.mul_sum]
  have hcard : (∑ p : Fin n × Fin n,
      (if (∀ j : Fin m, ∃ z : ℤ, |a p.1 j - a p.2 j - z| ≤ 2 * δ j) then (1 : ℝ) else 0))
      = ((Finset.univ.filter (fun p : Fin n × Fin n => ∀ j : Fin m, ∃ z : ℤ,
            |a p.1 j - a p.2 j - z| ≤ 2 * δ j)).card : ℝ) := by
    simp
  rw [hcard]

end Work.BMF
