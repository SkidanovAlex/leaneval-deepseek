import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.PairBlockCore
import Submission.Work.BoseFixB1S.BoxPotOper
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

/-- Integrability of a five-term real combination, from integrability of each term. -/
private lemma integrableOn_five {α : Type*} [MeasureSpace α] {s : Set α}
    {f0 f1 f2 f3 f4 : α → ℝ}
    (h0 : IntegrableOn f0 s volume) (h1 : IntegrableOn f1 s volume)
    (h2 : IntegrableOn f2 s volume) (h3 : IntegrableOn f3 s volume)
    (h4 : IntegrableOn f4 s volume) :
    IntegrableOn (fun x => 2 * f0 x + f1 x + f2 x + 2 * f3 x + (1 / 2) * f4 x) s volume :=
  ((((h0.const_mul 2).add h1).add h2).add (h3.const_mul 2)).add (h4.const_mul (1 / 2))

/-- Integral of a five-term real combination, from integrability of each term. -/
private lemma integral_five {α : Type*} [MeasureSpace α] {s : Set α}
    {f0 f1 f2 f3 f4 : α → ℝ}
    (h0 : IntegrableOn f0 s volume) (h1 : IntegrableOn f1 s volume)
    (h2 : IntegrableOn f2 s volume) (h3 : IntegrableOn f3 s volume)
    (h4 : IntegrableOn f4 s volume) :
    (∫ x in s, (2 * f0 x + f1 x + f2 x + 2 * f3 x + (1 / 2) * f4 x))
      = 2 * (∫ x in s, f0 x) + (∫ x in s, f1 x) + (∫ x in s, f2 x)
        + 2 * (∫ x in s, f3 x) + (1 / 2) * (∫ x in s, f4 x) := by
  have h0' : Integrable (fun x => (2 : ℝ) * f0 x) (volume.restrict s) := h0.const_mul 2
  have h3' : Integrable (fun x => (2 : ℝ) * f3 x) (volume.restrict s) := h3.const_mul 2
  have h4' : Integrable (fun x => (1 / 2 : ℝ) * f4 x) (volume.restrict s) := h4.const_mul (1 / 2)
  have hA : Integrable (fun x => 2 * f0 x + f1 x + f2 x + 2 * f3 x) (volume.restrict s) :=
    ((h0'.add h1).add h2).add h3'
  have hB : Integrable (fun x => 2 * f0 x + f1 x + f2 x) (volume.restrict s) := (h0'.add h1).add h2
  have hC : Integrable (fun x => 2 * f0 x + f1 x) (volume.restrict s) := h0'.add h1
  calc (∫ x in s, (2 * f0 x + f1 x + f2 x + 2 * f3 x + (1 / 2) * f4 x))
      = (∫ x in s, (2 * f0 x + f1 x + f2 x + 2 * f3 x)) + (∫ x in s, ((1 / 2) * f4 x)) := by
        exact integral_add hA h4'
    _ = ((∫ x in s, (2 * f0 x + f1 x + f2 x)) + (∫ x in s, (2 * f3 x)))
          + (∫ x in s, ((1 / 2) * f4 x)) := by
        rw [integral_add hB h3']
    _ = (((∫ x in s, (2 * f0 x + f1 x)) + (∫ x in s, f2 x)) + (∫ x in s, (2 * f3 x)))
          + (∫ x in s, ((1 / 2) * f4 x)) := by
        rw [integral_add hC h2]
    _ = ((((∫ x in s, (2 * f0 x)) + (∫ x in s, f1 x)) + (∫ x in s, f2 x))
          + (∫ x in s, (2 * f3 x))) + (∫ x in s, ((1 / 2) * f4 x)) := by
        rw [integral_add h0' h1]
    _ = 2 * (∫ x in s, f0 x) + (∫ x in s, f1 x) + (∫ x in s, f2 x)
        + 2 * (∫ x in s, f3 x) + (1 / 2) * (∫ x in s, f4 x) := by
        rw [integral_const_mul, integral_const_mul, integral_const_mul]

theorem pairFive_integrableOn_and_integral {N : ℕ} {ℓ volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))}
    {w w₁ w₂ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    {Φ : Submission.BoseGases.X N → ℝ}
    (hint0 : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
          * w₂ (x p.1) (x p.2)) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hint1 : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * w₂ (x p.1) (x p.2)) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hint2 : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
          * w₂ (x p.1) (x p.2)) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hint3 : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * w₁ (x p.1) (x p.2)) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hint4 : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.BoseFixB1S.boxQ4B volA A om Φ p x) ^ 2 * w (x p.1) (x p.2))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume) :
    ∀ p ∈ Submission.BoseGases.pairSet N,
      MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X N =>
          Work.BoseFixB1.pairFive volA A w w₁ w₂ om Φ p x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
      ∧ (∫ x in Submission.BoseGases.abox N ℓ,
            Work.BoseFixB1.pairFive volA A w w₁ w₂ om Φ p x)
        = 2 * (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
                * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
                * w₂ (x p.1) (x p.2))
          + (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
                * (Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
                * w₂ (x p.1) (x p.2))
          + (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
                * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
                * w₂ (x p.1) (x p.2))
          + 2 * (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
                * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
                * w₁ (x p.1) (x p.2))
          + (1 / 2) * (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.BoseFixB1S.boxQ4B volA A om Φ p x) ^ 2 * w (x p.1) (x p.2)) := by
  intro p hp
  have h0 := hint0 p hp
  have h1 := hint1 p hp
  have h2 := hint2 p hp
  have h3 := hint3 p hp
  have h4 := hint4 p hp
  set F0 : Submission.BoseGases.X N → ℝ := (fun x =>
      (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
        * w₂ (x p.1) (x p.2)) with hF0
  set F1 : Submission.BoseGases.X N → ℝ := (fun x =>
      (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
        * w₂ (x p.1) (x p.2)) with hF1
  set F2 : Submission.BoseGases.X N → ℝ := (fun x =>
      (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
        * w₂ (x p.1) (x p.2)) with hF2
  set F3 : Submission.BoseGases.X N → ℝ := (fun x =>
      (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
        * w₁ (x p.1) (x p.2)) with hF3
  set F4 : Submission.BoseGases.X N → ℝ := (fun x =>
      (Work.BoseFixB1S.boxQ4B volA A om Φ p x) ^ 2 * w (x p.1) (x p.2)) with hF4
  have h0' : MeasureTheory.IntegrableOn F0 (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
    rw [hF0]; exact h0
  have h1' : MeasureTheory.IntegrableOn F1 (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
    rw [hF1]; exact h1
  have h2' : MeasureTheory.IntegrableOn F2 (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
    rw [hF2]; exact h2
  have h3' : MeasureTheory.IntegrableOn F3 (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
    rw [hF3]; exact h3
  have h4' : MeasureTheory.IntegrableOn F4 (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
    rw [hF4]; exact h4
  have hpoint : ∀ x : Submission.BoseGases.X N,
      Work.BoseFixB1.pairFive volA A w w₁ w₂ om Φ p x
        = 2 * F0 x + F1 x + F2 x + 2 * F3 x + (1 / 2) * F4 x := by
    intro x
    simp only [Work.BoseFixB1.pairFive, hF0, hF1, hF2, hF3, hF4]
    ring
  refine ⟨?_, ?_⟩
  · exact (integrableOn_five h0' h1' h2' h3' h4').congr
      (Filter.Eventually.of_forall (fun x => (hpoint x).symm))
  · have hcongr : (∫ x in Submission.BoseGases.abox N ℓ,
          Work.BoseFixB1.pairFive volA A w w₁ w₂ om Φ p x)
        = (∫ x in Submission.BoseGases.abox N ℓ,
            (2 * F0 x + F1 x + F2 x + 2 * F3 x + (1 / 2) * F4 x)) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => hpoint x))
    rw [hcongr]
    exact integral_five h0' h1' h2' h3' h4'

end Work.BoseFixB1S
