import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MeasureTheory Set
open scoped ENNReal

theorem sliceIntegralEven {n : ℕ} (C : Set (Fin (n+1) → ℝ)) (k : Fin (n+1))
    (hsym : C = -C) (hcl : IsClosed C) (h : Fin n → ℝ → ℝ)
    (hh_even : ∀ i x, h i (-x) = h i x) (hh_meas : ∀ i, Measurable (h i)) :
    ∀ s : ℝ, ∫ y in {x : Fin n → ℝ | Fin.insertNth k (-s) x ∈ C}, ∏ i, h i (y i)
        = ∫ y in {x : Fin n → ℝ | Fin.insertNth k s x ∈ C}, ∏ i, h i (y i) := by
  intro s
  have hmp : MeasurePreserving (fun x : Fin n → ℝ => -x) volume volume :=
    Measure.measurePreserving_neg (volume : Measure (Fin n → ℝ))
  have hemb : MeasurableEmbedding (fun x : Fin n → ℝ => -x) :=
    measurableEmbedding_neg (α := Fin n → ℝ)
  have hneg : ∀ y : Fin n → ℝ,
      (Fin.insertNth k (-s) (-y) : Fin (n+1) → ℝ) = -(Fin.insertNth k s y : Fin (n+1) → ℝ) := by
    intro y
    exact Fin.insertNth_binop (α := fun _ => ℝ) (fun _ (a : ℝ) _ => -a) k s s y (0 : Fin n → ℝ)
  have hmem : ∀ z : Fin (n+1) → ℝ, -z ∈ C ↔ z ∈ C := by
    intro z
    have h1 : -z ∈ -C ↔ z ∈ C := by rw [Set.mem_neg, neg_neg]
    rw [← hsym] at h1
    exact h1
  have hpre : (fun x : Fin n → ℝ => -x) ⁻¹' {x : Fin n → ℝ | Fin.insertNth k (-s) x ∈ C}
      = {x : Fin n → ℝ | Fin.insertNth k s x ∈ C} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [hneg x]
    exact hmem (Fin.insertNth k s x)
  have hg_even : ∀ x : Fin n → ℝ, (∏ i, h i ((-x) i)) = ∏ i, h i (x i) := by
    intro x
    simp only [Pi.neg_apply]
    exact Finset.prod_congr rfl (fun i _ => hh_even i (x i))
  have key := hmp.setIntegral_preimage_emb hemb (fun y : Fin n → ℝ => ∏ i, h i (y i))
      {x : Fin n → ℝ | Fin.insertNth k (-s) x ∈ C}
  rw [hpre] at key
  rw [← key]
  exact integral_congr_ae (Filter.Eventually.of_forall hg_even)

end Work.BW
