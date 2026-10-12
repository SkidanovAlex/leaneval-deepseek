import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.a0A2QPaymentB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 4000000

namespace Work.BoseFixB1S

open MeasureTheory

theorem boxQSum_sub_boxA2_blockSum {N : ℕ} {ℓ volA μ : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {w w₁ w₂ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (hw1 : ∀ x y : EuclideanSpace ℝ (Fin 3), w₁ x y = w x y * (1 - om x y))
    (hw2 : ∀ x y : EuclideanSpace ℝ (Fin 3), w₂ x y = w x y * (1 - om x y ^ 2))
    (hwsym : ∀ x y : EuclideanSpace ℝ (Fin 3), w x y = w y x)
    (homsym : ∀ x y : EuclideanSpace ℝ (Fin 3), om x y = om y x)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
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
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hint5 : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => Work.BoseFixB1.pairBlock volA A w om Φ p x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume) :
    Work.BoseFixB1S.boxQSum volA ℓ μ A w w₁ w₂ om Φ
        - Work.BoseFixB1.boxA2 ℓ volA A w₁ Φ
        + 2 * μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x)
              * (Work.UBBInputs8.boxPInd volA A i Φ x)
              * Submission.BoseGases.w1Fibre ℓ w₁ (x i))
        + μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2
              * Submission.BoseGases.w1Fibre ℓ w₁ (x i))
      = Work.BoseFixB1S.boxQ0 volA ℓ μ A w₁ w₂ Φ
        + (1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ,
              Work.BoseFixB1.pairBlock volA A w om Φ p x := by
  -- The per-pair split of the five integrands of `pairFive`.
  have hsplit := fun p (hp : p ∈ Submission.BoseGases.pairSet N) =>
    (pairFive_integrableOn_and_integral (N := N) (ℓ := ℓ) (volA := volA) (A := A)
      (w := w) (w₁ := w₁) (w₂ := w₂) (om := om) (Φ := Φ)
      hint0 hint1 hint2 hint3 hint4 p hp).2
  -- Summing the split over the ordered pairs.
  have hsum :
      (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
          Work.BoseFixB1.pairFive volA A w w₁ w₂ om Φ p x)
        = 2 * (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
                * (Work.UBBInputs8.boxPInd volA A p.1
                    (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
                * w₂ (x p.1) (x p.2))
          + (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
                * (Work.UBBInputs8.boxPInd volA A p.2
                    (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
                * w₂ (x p.1) (x p.2))
          + (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
                * (Work.UBBInputs8.boxQInd volA A p.2
                    (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
                * w₂ (x p.1) (x p.2))
          + 2 * (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
                * (Work.UBBInputs8.boxQInd volA A p.2
                    (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
                * w₁ (x p.1) (x p.2))
          + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
              ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.BoseFixB1S.boxQ4B volA A om Φ p x) ^ 2 * w (x p.1) (x p.2)) := by
    rw [Finset.sum_congr rfl hsplit]
    simp only [Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  -- The algebraic regrouping (μ-cancellation, `boxA2`-cancellation) of the five words.
  have hG : Work.BoseFixB1S.boxQSum volA ℓ μ A w w₁ w₂ om Φ
        - Work.BoseFixB1.boxA2 ℓ volA A w₁ Φ
        + 2 * μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x)
              * (Work.UBBInputs8.boxPInd volA A i Φ x)
              * Submission.BoseGases.w1Fibre ℓ w₁ (x i))
        + μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2
              * Submission.BoseGases.w1Fibre ℓ w₁ (x i))
      = Work.BoseFixB1S.boxQ0 volA ℓ μ A w₁ w₂ Φ
        + (2 * (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
                * (Work.UBBInputs8.boxPInd volA A p.1
                    (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
                * w₂ (x p.1) (x p.2))
          + (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
                * (Work.UBBInputs8.boxPInd volA A p.2
                    (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
                * w₂ (x p.1) (x p.2))
          + (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
                * (Work.UBBInputs8.boxQInd volA A p.2
                    (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
                * w₂ (x p.1) (x p.2))
          + 2 * (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
                * (Work.UBBInputs8.boxQInd volA A p.2
                    (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
                * w₁ (x p.1) (x p.2))
          + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
              ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.BoseFixB1S.boxQ4B volA A om Φ p x) ^ 2 * w (x p.1) (x p.2))) := by
    unfold Work.BoseFixB1S.boxQSum Work.BoseFixB1S.boxQ0 Work.BoseFixB1S.boxQ1
      Work.BoseFixB1S.boxQ2 Work.BoseFixB1S.boxQ3 Work.BoseFixB1S.boxQ4 Work.BoseFixB1.boxA2
    ring
  -- Combining: the goal's left side is `boxQ0` plus the sum of the `pairFive` integrals.
  have h1 : Work.BoseFixB1S.boxQSum volA ℓ μ A w w₁ w₂ om Φ
        - Work.BoseFixB1.boxA2 ℓ volA A w₁ Φ
        + 2 * μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x)
              * (Work.UBBInputs8.boxPInd volA A i Φ x)
              * Submission.BoseGases.w1Fibre ℓ w₁ (x i))
        + μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2
              * Submission.BoseGases.w1Fibre ℓ w₁ (x i))
      = Work.BoseFixB1S.boxQ0 volA ℓ μ A w₁ w₂ Φ
        + (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
            Work.BoseFixB1.pairFive volA A w w₁ w₂ om Φ p x) := by
    rw [hG, ← hsum]
  -- Per-pair a.e. identity: the block is the sum of the two orientations.
  have hPB : ∀ p ∈ Submission.BoseGases.pairSet N,
      (∫ x in Submission.BoseGases.abox N ℓ, Work.BoseFixB1.pairBlock volA A w om Φ p x)
        = (∫ x in Submission.BoseGases.abox N ℓ,
              Work.BoseFixB1.pairFive volA A w w₁ w₂ om Φ p x)
          + (∫ x in Submission.BoseGases.abox N ℓ,
              Work.BoseFixB1.pairFive volA A w w₁ w₂ om Φ (p.2, p.1) x) := by
    intro p hp
    have hne : p.1 ≠ p.2 := by
      have hp' := hp
      simp only [Submission.BoseGases.pairSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp'
      exact hp'
    have hsp : (p.2, p.1) ∈ Submission.BoseGases.pairSet N := by
      simp only [Submission.BoseGases.pairSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact fun h => hp h.symm
    have hae : (fun x : Submission.BoseGases.X N =>
          Work.BoseFixB1.pairBlock volA A w om Φ (p.1, p.2) x)
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
        (fun x : Submission.BoseGases.X N =>
          Work.BoseFixB1.pairFive volA A w w₁ w₂ om Φ (p.1, p.2) x
            + Work.BoseFixB1.pairFive volA A w w₁ w₂ om Φ (p.2, p.1) x) :=
      pairBlock_ae_pairFive (A := A) hℓ hvol hA hvolA hAc om hw1 hw2 hwsym homsym hΦc hne
    have hfp : MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X N =>
          Work.BoseFixB1.pairFive volA A w w₁ w₂ om Φ p x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
      (pairFive_integrableOn_and_integral (N := N) (ℓ := ℓ) (volA := volA) (A := A)
        (w := w) (w₁ := w₁) (w₂ := w₂) (om := om) (Φ := Φ)
        hint0 hint1 hint2 hint3 hint4 p hp).1
    have hfs : MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X N =>
          Work.BoseFixB1.pairFive volA A w w₁ w₂ om Φ (p.2, p.1) x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
      (pairFive_integrableOn_and_integral (N := N) (ℓ := ℓ) (volA := volA) (A := A)
        (w := w) (w₁ := w₁) (w₂ := w₂) (om := om) (Φ := Φ)
        hint0 hint1 hint2 hint3 hint4 (p.2, p.1) hsp).1
    rw [MeasureTheory.integral_congr_ae hae]
    rw [MeasureTheory.integral_add hfp hfs]
  -- Reindexing the swapped sum back.
  have hreindex :
      (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
          Work.BoseFixB1.pairFive volA A w w₁ w₂ om Φ (p.2, p.1) x)
        = ∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
            Work.BoseFixB1.pairFive volA A w w₁ w₂ om Φ p x := by
    refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Submission.BoseGases.pairSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact fun h => hp h.symm
    · intro p hp q hq heq
      simp only [Prod.mk.injEq] at heq
      exact Prod.ext heq.2 heq.1
    · intro b hb
      refine ⟨(b.2, b.1), ?_, Prod.ext rfl rfl⟩
      simp only [Submission.BoseGases.pairSet, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact fun h => hb h.symm
    · intro a ha
      rfl
  -- Summing the per-pair identity.
  have hPBsum :
      (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
          Work.BoseFixB1.pairBlock volA A w om Φ p x)
        = 2 * (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
            Work.BoseFixB1.pairFive volA A w w₁ w₂ om Φ p x) := by
    rw [Finset.sum_congr rfl hPB]
    rw [Finset.sum_add_distrib, hreindex]
    ring
  have h2 :
      (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
          Work.BoseFixB1.pairFive volA A w w₁ w₂ om Φ p x)
        = (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ,
              Work.BoseFixB1.pairBlock volA A w om Φ p x) := by
    rw [hPBsum]
    ring
  rw [h1, h2]

end Work.BoseFixB1S
