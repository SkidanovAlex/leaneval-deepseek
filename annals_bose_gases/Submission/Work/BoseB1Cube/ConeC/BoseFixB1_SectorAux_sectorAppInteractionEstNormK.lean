import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_boxCountsScaleB1
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_crossJointSteps
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1_SectorAux_jointCoreGoodState
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1_sectorPieceStructure
import Submission.Work.BoseFixB1.SectorAux.boxFragmentsIntegrableGood
import Submission.Work.BoseFixB1.SectorAux.boxPairBlockIntegrableGood
import Submission.Work.BoseFixB1.SectorAux.boxQ0_valueGood
import Submission.Work.BoseFixB1.SectorAux.boxWords_eq_zero_of_ae_eq_zero
import Submission.Work.BoseFixB1.SectorAux.one_le_mu_boxMassGood
import Submission.Work.BoseFixB1.pairMassData
import Submission.Work.BoseFixB1S.boxA2ScaleB1
import Submission.Work.BoseFixB1S.boxQSumScaleB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.SectorAux

open MeasureTheory
open scoped Real BigOperators ENNReal
open Work.BoseFixB1B Work.SmallBoxSliding

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Helper lemmas for `sectorAppInteractionEstNormK`

(Skeleton stage 1: the `GoodState` regularity of the sector piece, the `GoodState` per-pair
a.e. identity, and the `GoodState` version of the sum-level reduction `(R1)`.) -/

/-- **A sector piece of a `GoodState` is a `GoodState`.** -/
theorem goodState_sectorPiece {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A) (k : ℕ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Work.BoseFixB1S.GoodState ℓ Φ) :
    Work.BoseFixB1S.GoodState ℓ (Work.FockBridge.sectorPiece A k Φ) :=
  ⟨Work.BoseFixB1.sectorPiece_measurable hA k hΦ.1, hΦ.2.choose,
    Work.BoseFixB1.sectorPiece_bound hℓ k hΦ.2.choose_spec⟩

/-- **The per-pair a.e. identity at `GoodState` regularity**
(`Work.BoseFixB1S.pairBlock_ae_pairFive` with `Continuous Φ` replaced by `GoodState ℓ Φ`). -/
theorem pairBlock_ae_pairFiveGood {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {w w₁ w₂ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (hw1 : ∀ x y : EuclideanSpace ℝ (Fin 3), w₁ x y = w x y * (1 - om x y))
    (hw2 : ∀ x y : EuclideanSpace ℝ (Fin 3), w₂ x y = w x y * (1 - om x y ^ 2))
    (hwsym : ∀ x y : EuclideanSpace ℝ (Fin 3), w x y = w y x)
    (homsym : ∀ x y : EuclideanSpace ℝ (Fin 3), om x y = om y x)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦg : Work.BoseFixB1S.GoodState ℓ Φ)
    {i j : Fin N} (hij : i ≠ j) :
    (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1.pairBlock volA A w om Φ (i, j) x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
    (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1.pairFive volA A w w₁ w₂ om Φ (i, j) x
        + Work.BoseFixB1.pairFive volA A w w₁ w₂ om Φ (j, i) x) := by
  filter_upwards [MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.abox_measurable N ℓ)]
    with x hx
  exact (Work.BoseFixB1.pairFive_add_swap volA A w w₁ w₂ om x hw1 hw2 hwsym homsym
    (Work.BoseFixB1S.boxPInd_boxPInd_comm_good hℓ hvol hA hvolA hAc hij hΦg x hx)
    (Work.BoseFixB1S.boxQInd_boxQInd_comm_good hℓ hvol hA hvolA hAc hij hΦg x hx).symm
    (Work.BoseFixB1S.boxPInd_boxQInd_comm_good hℓ hvol hA hvolA hAc hij hΦg x hx)
    (Work.BoseFixB1S.boxPInd_boxQInd_comm_good hℓ hvol hA hvolA hAc hij.symm hΦg x hx).symm).symm

theorem boxQSum_sub_boxA2_blockSumGS {N : ℕ} {ℓ volA μ : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {w w₁ w₂ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (hw1 : ∀ x y : EuclideanSpace ℝ (Fin 3), w₁ x y = w x y * (1 - om x y))
    (hw2 : ∀ x y : EuclideanSpace ℝ (Fin 3), w₂ x y = w x y * (1 - om x y ^ 2))
    (hwsym : ∀ x y : EuclideanSpace ℝ (Fin 3), w x y = w y x)
    (homsym : ∀ x y : EuclideanSpace ℝ (Fin 3), om x y = om y x)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦg : Work.BoseFixB1S.GoodState ℓ Φ)
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
    (Work.BoseFixB1S.pairFive_integrableOn_and_integral (N := N) (ℓ := ℓ) (volA := volA) (A := A)
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
      pairBlock_ae_pairFiveGood (A := A) hℓ hvol hA hvolA hAc om hw1 hw2 hwsym homsym hΦg hne
    have hfp : MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X N =>
          Work.BoseFixB1.pairFive volA A w w₁ w₂ om Φ p x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
      (Work.BoseFixB1S.pairFive_integrableOn_and_integral (N := N) (ℓ := ℓ) (volA := volA) (A := A)
        (w := w) (w₁ := w₁) (w₂ := w₂) (om := om) (Φ := Φ)
        hint0 hint1 hint2 hint3 hint4 p hp).1
    have hfs : MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X N =>
          Work.BoseFixB1.pairFive volA A w w₁ w₂ om Φ (p.2, p.1) x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
      (Work.BoseFixB1S.pairFive_integrableOn_and_integral (N := N) (ℓ := ℓ) (volA := volA) (A := A)
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



/-- **Jensen at mass one.**  `Work.BoseFixB1.boxFlatSqJensen_sectorPiece` gives
`S² − S·I ≤ I·Pc` with `I = ∫ ψ²`; at `I = 1` this is `S² − S ≤ Pc`. -/
theorem boxFlatSqJensen_massOne {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {k : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hm : Measurable Φ) {B : ℝ}
    (hb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ B)
    (hnorm : (∫ x in Submission.BoseGases.abox N ℓ,
      (Work.FockBridge.sectorPiece A k Φ x) ^ 2) = 1) :
    Work.BoseFixB1S.boxFlatCount V ℓ A (Work.FockBridge.sectorPiece A k Φ)
        * Work.BoseFixB1S.boxFlatCount V ℓ A (Work.FockBridge.sectorPiece A k Φ)
      - Work.BoseFixB1S.boxFlatCount V ℓ A (Work.FockBridge.sectorPiece A k Φ)
      ≤ Work.BoseFixB1S.boxPairCount V ℓ A (Work.FockBridge.sectorPiece A k Φ) := by
  have h := Work.BoseFixB1.boxFlatSqJensen_sectorPiece (N := N) (ℓ := ℓ) (V := V)
    (A := A) hℓ hV hA hVeq hAc (k := k) (Φ := Φ) hm hb
  rw [hnorm] at h
  linarith [h]


/-! ## Integrability of the five-word fragments at `GoodState` regularity -/

/-- The two-factor a.e. product bound. -/
private theorem abs_mul_le_aux {a b A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) hA

/-- **The four missing `IntegrableOn` families of `(R1)` at the sliding kernels**, at
`GoodState` regularity (`hint0` is `Work.BoseFixB1.SectorAux.boxFragmentsIntegrableGood`'s first
conjunct and `hint4`,`hint5` come from `boxPairBlockIntegrableGood`; these are the remaining
per-pair integrands of `pairFive`). -/
theorem boxPairHintsGS {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvolmass : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ}
    (hΦg : Work.BoseFixB1S.GoodState ℓ Φ) :
    (∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X N =>
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.1
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x)
            * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.1 Φ) x)
            * (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)
                (x p.1) (x p.2)))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    ∧ (∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X N =>
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.1
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x)
            * (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2
                (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.1 Φ) x)
            * (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)
                (x p.1) (x p.2)))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    ∧ (∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X N =>
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.1
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x)
            * (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.1 Φ) x)
            * (Submission.BoseGases.wSmall1Pair h M ℓ d u (x p.1) (x p.2)))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    ∧ (∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X N =>
          (Work.BoseFixB1S.boxQ4B (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.omC (Classical.choose h)) Φ p x) ^ 2
            * (Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume) := by
  classical
  obtain ⟨hΦm, C, hΦb⟩ := hΦg
  set A : Set (EuclideanSpace ℝ (Fin 3)) := Submission.BoseGases.dlBox ℓ d u with hAdef
  set volA : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hvoldef
  have hAms : MeasurableSet A := by
    rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hvol : 0 < volA := by rw [hvoldef]; exact hvolmass
  have hvol0 : 0 ≤ volA := le_of_lt hvol
  have hvolA : volA = (MeasureTheory.volume A).toReal := by
    rw [hvoldef, hAdef, Work.SmallBoxSliding.boxMass_eq_measureReal,
      MeasureTheory.measureReal_def]
  have hAc : A ⊆ Submission.BoseGases.acube ℓ := by
    rw [hAdef]; exact Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (Φ 0))
    (hΦb 0 (Submission.BoseGases.zero_mem_abox (N := N) (ℓ := ℓ) hℓ.le))
  have h2C : (0 : ℝ) ≤ 2 * C := by linarith
  have hQΦ : ∀ k : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd volA A k Φ x| ≤ 2 * C :=
    fun k => Work.BoseFixB1.Clean.abs_boxQInd_le_nonneg hℓ hvol0 hAms hvolA hAc k hC0 hΦb
  have hPΦ : ∀ k : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A k Φ x| ≤ C :=
    fun k => Work.BoseFixB1.Clean.abs_boxPInd_le_nonneg hℓ hvol0 hAms hvolA hAc k hC0 hΦb
  have hg2int : MeasureTheory.Integrable (Submission.BoseGases.g2 v h) :=
    Submission.BoseGases.g2_integrable hR0 hv hvrad hv_supp h
  have hg2supp : ∀ z : EuclideanSpace ℝ (Fin 3), R0 ≤ ‖z‖ →
      Submission.BoseGases.g2 v h z = 0 :=
    fun z hz => Submission.BoseGases.g2_zero_of_norm_ge hv_supp hz h
  have hvint : MeasureTheory.Integrable v := Submission.BoseGases.v_integrable hv1
  have hvsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R0 ≤ ‖z‖ → v z = 0 :=
    fun z hz => Submission.BoseGases.v_eq_zero_of_norm_ge hv_supp hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- family 1: `P_iQ_j · P_jQ_i · w₂`
    intro p hp
    have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have hQm : Measurable (Work.UBBInputs8.boxQInd volA A p.2 Φ) :=
      Work.BoseFixB1.Clean.measurable_boxQIndAux volA A hAms p.2 hΦm
    have hQm1 : Measurable (Work.UBBInputs8.boxQInd volA A p.1 Φ) :=
      Work.BoseFixB1.Clean.measurable_boxQIndAux volA A hAms p.1 hΦm
    have hPm1 : Measurable (Work.UBBInputs8.boxPInd volA A p.1 Φ) :=
      Work.BoseFixB1S.measurable_boxPInd volA A hAms p.1 hΦm
    have hPm2 : Measurable (Work.UBBInputs8.boxPInd volA A p.2 Φ) :=
      Work.BoseFixB1S.measurable_boxPInd volA A hAms p.2 hΦm
    have hS1m : Measurable (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x) :=
      Work.BoseFixB1S.measurable_boxPInd volA A hAms p.1 hQm
    have hS2m : Measurable (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x) :=
      Work.BoseFixB1S.measurable_boxPInd volA A hAms p.2 hQm1
    have hS1b : ∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x| ≤ 2 * C :=
      Work.BoseFixB1.Clean.abs_boxPInd_le_nonneg (C := 2 * C) hℓ hvol0 hAms hvolA hAc p.1 h2C
        (hQΦ p.2)
    have hS2b : ∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x| ≤ 2 * C :=
      Work.BoseFixB1.Clean.abs_boxPInd_le_nonneg (C := 2 * C) hℓ hvol0 hAms hvolA hAc p.2 h2C
        (hQΦ p.1)
    have hSm : MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X N =>
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x))
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
      (hS1m.mul hS2m).aestronglyMeasurable
    have hSb : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
        |(Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)|
          ≤ (2 * C) * (2 * C) := by
      rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
      exact Filter.Eventually.of_forall (fun x hx =>
        abs_mul_le_aux h2C h2C (hS1b x hx) (hS2b x hx))
    exact Work.BoseFixB1.integrableOn_slot_wSmallPair (N := N) (ℓ := ℓ) (d := d) (R := R0)
      (f := Submission.BoseGases.g2 v h)
      (S := fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x))
      (B := (2 * C) * (2 * C)) hℓ hd hg2int hg2supp hM hR hRχ u hpne hSm (by positivity) hSb
  · -- family 2: `P_iQ_j · Q_jP_i · w₂`
    intro p hp
    have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have hQm : Measurable (Work.UBBInputs8.boxQInd volA A p.2 Φ) :=
      Work.BoseFixB1.Clean.measurable_boxQIndAux volA A hAms p.2 hΦm
    have hPm1 : Measurable (Work.UBBInputs8.boxPInd volA A p.1 Φ) :=
      Work.BoseFixB1S.measurable_boxPInd volA A hAms p.1 hΦm
    have hS1m : Measurable (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x) :=
      Work.BoseFixB1S.measurable_boxPInd volA A hAms p.1 hQm
    have hS2m : Measurable (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x) :=
      Work.BoseFixB1.Clean.measurable_boxQIndAux volA A hAms p.2 hPm1
    have hS1b : ∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x| ≤ 2 * C :=
      Work.BoseFixB1.Clean.abs_boxPInd_le_nonneg (C := 2 * C) hℓ hvol0 hAms hvolA hAc p.1 h2C
        (hQΦ p.2)
    have hS2b : ∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x| ≤ 2 * C :=
      Work.BoseFixB1.Clean.abs_boxQInd_le_nonneg hℓ hvol0 hAms hvolA hAc p.2 hC0 (hPΦ p.1)
    have hSm : MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X N =>
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x))
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
      (hS1m.mul hS2m).aestronglyMeasurable
    have hSb : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
        |(Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)|
          ≤ (2 * C) * (2 * C) := by
      rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
      exact Filter.Eventually.of_forall (fun x hx =>
        abs_mul_le_aux h2C h2C (hS1b x hx) (hS2b x hx))
    exact Work.BoseFixB1.integrableOn_slot_wSmallPair (N := N) (ℓ := ℓ) (d := d) (R := R0)
      (f := Submission.BoseGases.g2 v h)
      (S := fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x))
      (B := (2 * C) * (2 * C)) hℓ hd hg2int hg2supp hM hR hRχ u hpne hSm (by positivity) hSb
  · -- family 3: `P_iQ_j · Q_jQ_i · w₁`, with the `1 − ω` factor folded into `S`
    intro p hp
    have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have hom := Submission.BoseGases.w0_abs_le_one_box_ae (N := N) (ℓ := ℓ) hℓ hR0 hv hvrad
      hv_supp h hpne
    have homx : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
        |1 - Classical.choose h (x p.1 - x p.2)| ≤ 2 := by
      filter_upwards [hom] with x hx
      have ha := abs_le.mp hx
      rw [abs_le]
      constructor <;> linarith [ha.1, ha.2]
    have homm : MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X N => 1 - Classical.choose h (x p.1 - x p.2))
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
      (aestronglyMeasurable_const.sub
        (Submission.BoseGases.w0_diff_aem (N := N) (ℓ := ℓ) hℓ hpne
          (w0 := Classical.choose h) (Classical.choose_spec h).2.lhs_integrable))
    have hQm : Measurable (Work.UBBInputs8.boxQInd volA A p.2 Φ) :=
      Work.BoseFixB1.Clean.measurable_boxQIndAux volA A hAms p.2 hΦm
    have hQm1 : Measurable (Work.UBBInputs8.boxQInd volA A p.1 Φ) :=
      Work.BoseFixB1.Clean.measurable_boxQIndAux volA A hAms p.1 hΦm
    have hS1m : Measurable (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x) :=
      Work.BoseFixB1S.measurable_boxPInd volA A hAms p.1 hQm
    have hS2m : Measurable (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x) :=
      Work.BoseFixB1.Clean.measurable_boxQIndAux volA A hAms p.2 hQm1
    have hS1b : ∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x| ≤ 2 * C :=
      Work.BoseFixB1.Clean.abs_boxPInd_le_nonneg (C := 2 * C) hℓ hvol0 hAms hvolA hAc p.1 h2C
        (hQΦ p.2)
    have hS2b : ∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x|
          ≤ 2 * (2 * C) :=
      Work.BoseFixB1.Clean.abs_boxQInd_le_nonneg hℓ hvol0 hAms hvolA hAc p.2 h2C (hQΦ p.1)
    have h4C : (0:ℝ) ≤ 2 * (2 * C) := by positivity
    have hSm : MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X N =>
          ((Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x))
            * (1 - Classical.choose h (x p.1 - x p.2)))
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
      ((hS1m.mul hS2m).aestronglyMeasurable).mul homm
    have hSb : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
        |((Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x))
            * (1 - Classical.choose h (x p.1 - x p.2))|
          ≤ ((2 * C) * (2 * (2 * C))) * 2 := by
      filter_upwards [homx,
        MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.abox_measurable N ℓ)]
        with x hx hbx
      refine abs_mul_le_aux (mul_nonneg h2C h4C) (by norm_num) ?_ hx
      exact abs_mul_le_aux h2C h4C (hS1b x hbx) (hS2b x hbx)
    have hmain := Work.BoseFixB1.integrableOn_slot_wSmallPair (N := N) (ℓ := ℓ) (d := d)
      (R := R0) (f := v) (M := M)
      (S := fun x : Submission.BoseGases.X N =>
        ((Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x))
          * (1 - Classical.choose h (x p.1 - x p.2)))
      (B := ((2 * C) * (2 * (2 * C))) * 2) hℓ hd hvint hvsupp hM hR hRχ u hpne hSm
      (by positivity) hSb
    refine hmain.congr ?_
    filter_upwards with x
    rw [Work.BoseFixB1.wSmall1Pair_eq_mul h u (x p.1) (x p.2)]
    ring
  · -- family 4: `(boxQ4B)² · w` with `w = wSmallPair M ℓ d u v`
    intro p hp
    have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have hom := Submission.BoseGases.w0_abs_le_one_box_ae (N := N) (ℓ := ℓ) hℓ hR0 hv hvrad
      hv_supp h hpne
    have hQm : Measurable (Work.UBBInputs8.boxQInd volA A p.2 Φ) :=
      Work.BoseFixB1.Clean.measurable_boxQIndAux volA A hAms p.2 hΦm
    have hQm1 : Measurable (Work.UBBInputs8.boxQInd volA A p.1 Φ) :=
      Work.BoseFixB1.Clean.measurable_boxQIndAux volA A hAms p.1 hΦm
    have hPm1 : Measurable (Work.UBBInputs8.boxPInd volA A p.1 Φ) :=
      Work.BoseFixB1S.measurable_boxPInd volA A hAms p.1 hΦm
    have hPm2 : Measurable (Work.UBBInputs8.boxPInd volA A p.2 Φ) :=
      Work.BoseFixB1S.measurable_boxPInd volA A hAms p.2 hΦm
    have hQQm : Measurable (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x) :=
      Work.BoseFixB1.Clean.measurable_boxQIndAux volA A hAms p.2 hQm1
    have hPPm : Measurable (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x) :=
      Work.BoseFixB1S.measurable_boxPInd volA A hAms p.2 hPm1
    have hPQm : Measurable (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x) :=
      Work.BoseFixB1S.measurable_boxPInd volA A hAms p.2 hQm1
    have hQPm : Measurable (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x) :=
      Work.BoseFixB1.Clean.measurable_boxQIndAux volA A hAms p.2 hPm1
    have homT : MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X N =>
          Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2))
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := by
      have hd0 := Submission.BoseGases.w0_diff_aem (N := N) (ℓ := ℓ) hℓ hpne
        (w0 := Classical.choose h) (Classical.choose_spec h).2.lhs_integrable
      simpa only [Submission.BoseGases.omC] using hd0
    have hBm : MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X N =>
          Work.BoseFixB1S.boxQ4B volA A (Submission.BoseGases.omC (Classical.choose h)) Φ p x)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := by
      unfold Work.BoseFixB1S.boxQ4B
      exact hQQm.aestronglyMeasurable.add (homT.mul ((hPPm.aestronglyMeasurable.add
        hPQm.aestronglyMeasurable).add hQPm.aestronglyMeasurable))
    have homx : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
        |Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2)| ≤ 1 := by
      filter_upwards [hom] with x hx
      simpa only [Submission.BoseGases.omC] using hx
    have hSm : MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X N =>
          (Work.BoseFixB1S.boxQ4B volA A (Submission.BoseGases.omC (Classical.choose h)) Φ p x) ^ 2)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
      hBm.pow 2
    have hSb : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
        |(Work.BoseFixB1S.boxQ4B volA A (Submission.BoseGases.omC (Classical.choose h)) Φ p x) ^ 2|
          ≤ (9 * C) ^ 2 := by
      filter_upwards [homx,
        MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.abox_measurable N ℓ)]
        with x hx hbx
      have hQQb : |Work.UBBInputs8.boxQInd volA A p.2
          (Work.UBBInputs8.boxQInd volA A p.1 Φ) x| ≤ 2 * (2 * C) :=
        Work.BoseFixB1.Clean.abs_boxQInd_le_nonneg hℓ hvol0 hAms hvolA hAc p.2 h2C (hQΦ p.1) x hbx
      have hPPb : |Work.UBBInputs8.boxPInd volA A p.2
          (Work.UBBInputs8.boxPInd volA A p.1 Φ) x| ≤ C :=
        Work.BoseFixB1.Clean.abs_boxPInd_le_nonneg hℓ hvol0 hAms hvolA hAc p.2 hC0 (hPΦ p.1) x hbx
      have hPQb : |Work.UBBInputs8.boxPInd volA A p.2
          (Work.UBBInputs8.boxQInd volA A p.1 Φ) x| ≤ 2 * C :=
        Work.BoseFixB1.Clean.abs_boxPInd_le_nonneg (C := 2 * C) hℓ hvol0 hAms hvolA hAc p.2 h2C
          (hQΦ p.1) x hbx
      have hQPb : |Work.UBBInputs8.boxQInd volA A p.2
          (Work.UBBInputs8.boxPInd volA A p.1 Φ) x| ≤ 2 * C :=
        Work.BoseFixB1.Clean.abs_boxQInd_le_nonneg hℓ hvol0 hAms hvolA hAc p.2 hC0 (hPΦ p.1) x hbx
      have hsum : |((Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x
            + Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
            + Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)|
          ≤ 5 * C := by
        have h1 : |Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x
            + Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x|
            ≤ C + 2 * C := le_trans (abs_add_le _ _) (add_le_add hPPb hPQb)
        have h2 := abs_add_le (Work.UBBInputs8.boxPInd volA A p.2
            (Work.UBBInputs8.boxPInd volA A p.1 Φ) x
            + Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
        linarith
      have hmul : |Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2)
            * ((Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x
              + Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
              + Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)|
          ≤ 1 * (5 * C) := by
        rw [abs_mul]
        exact mul_le_mul hx hsum (abs_nonneg _) (by norm_num)
      have hq : |Work.BoseFixB1S.boxQ4B volA A (Submission.BoseGases.omC (Classical.choose h))
          Φ p x| ≤ 9 * C := by
        have h := abs_add_le (Work.UBBInputs8.boxQInd volA A p.2
            (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          (Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2)
            * ((Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x
              + Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
              + Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x))
        simp only [Work.BoseFixB1S.boxQ4B] at h ⊢
        linarith
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hq 2
    exact Work.BoseFixB1.integrableOn_slot_wSmallPair (N := N) (ℓ := ℓ) (d := d) (R := R0)
      (f := v)
      (S := fun x : Submission.BoseGases.X N =>
        (Work.BoseFixB1S.boxQ4B volA A (Submission.BoseGases.omC (Classical.choose h)) Φ p x) ^ 2)
      (B := (9 * C) ^ 2) hℓ hd hvint hvsupp hM hR hRχ u hpne hSm (by positivity) hSb

/-- **The `A₀`-slack identity at `GoodState` regularity** (`Work.BoseFixB1.boxQ0_sub_a0MainLocBox_eq`
with `Continuous Φ` replaced by `GoodState ℓ Φ`). -/
theorem boxQ0_sub_a0MainLocBox_eq_good {N : ℕ} {ℓ volA μ : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {w1 w2 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw2i : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      w2 p.1 p.2) ((MeasureTheory.volume : MeasureTheory.Measure
        (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))).restrict (A ×ˢ A)))
    (hfib : MeasureTheory.IntegrableOn
      (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.w1Fibre ℓ w1 z) A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦg : Work.BoseFixB1S.GoodState ℓ Φ) :
    Work.BoseFixB1S.boxQ0 volA ℓ μ A w1 w2 Φ
        - Work.BoseFixB1.a0MainLocBox volA μ (Work.BoseFixB1S.boxM1 ℓ A w1)
          (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ)
      = Work.BoseFixB1S.boxM1 ℓ A w1
            * ((1 / 4) * (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ / volA - μ) ^ 2
                + (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ / volA + μ) / (2 * volA)
                + 1 / (4 * volA ^ 2))
          + (1 / 2) * (Work.BoseFixB1S.boxM2 volA A w2 / volA ^ 2)
              * Work.BoseFixB1S.boxPairCount volA ℓ A Φ
          - (1 / 2) * (Work.BoseFixB1S.boxM1 ℓ A w1 / volA ^ 2)
              * (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ ^ 2
                - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ) := by
  have hval := Work.BoseFixB1.SectorAux.boxQ0_valueGood (ℓ := ℓ) (volA := volA) (μ := μ) (A := A)
    hℓ hvol hA hvolA hAc (w1 := w1) (w2 := w2) hw2i hfib (Φ := Φ) hΦg
  rw [hval]
  unfold Work.BoseFixB1.a0MainLocBox
  ring


theorem sectorAppInteractionEstNormK {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseFixB1B.PBℓ v μ))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ →
        ∀ k ∈ Finset.range (n + 1),
          let V : ℝ := Work.SmallBoxSliding.boxMass (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u
          let Ψ : Submission.BoseGases.X n → ℝ :=
            Work.FockBridge.sectorPiece (Work.BoseFixB1B.PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ)
          let m : ℝ := Work.FockBridge.sectorMass (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u)
            (Φ : Submission.BoseGases.X n → ℝ) k
          let S : ℝ := Work.BoseFixB1S.boxFlatCount V (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u) Ψ
          let nq : ℝ := Work.BoseFixB1S.boxQCount V (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u) Ψ
          let w₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ :=
            Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u
          (1 / 2) * (Work.BoseFixB1S.boxM1 (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u) w₁ / V ^ 2)
              * (S ^ 2 / m - S)
            - μ * (Work.BoseFixB1S.boxM1 (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u) w₁ / V) * S
            - Work.BoseFixB1S.boxM1 (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u) w₁
              * (m * ((1 / 4) * (S / (m * V) - μ) ^ 2 + (S / (m * V) + μ) / (2 * V)
                  + 1 / (4 * V ^ 2)))
            + Work.BoseFixB1.boxA2 (Work.BoseFixB1B.PBℓ v μ) V (Work.BoseFixB1B.PBB v μ u) w₁ Ψ
            - C * (_root_.BoseGases.a v) * (μ + (k : ℝ) / V) * nq
          ≤ Work.BoseFixB1S.boxQSum V (Work.BoseFixB1B.PBℓ v μ) μ (Work.BoseFixB1B.PBB v μ u)
              (Submission.BoseGases.wSmallPair (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u v)
              w₁
              (Submission.BoseGases.wSmallPair (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u
                (Submission.BoseGases.g2 v h))
              (Submission.BoseGases.omC (Classical.choose h)) Ψ
    := by
  classical
  /- The complete route (see `FINDING_sectorAppInteractionEstNormK.md`):
     `(R1)` at `GoodState` regularity + the joint core `a0A2QJointNormB1FixGood` +
     `boxTarget_of_joint` give the *normalised* `A₀`-form; `T₁+T₂+T₃ = m·a0MainLocBox(S/m)` and
     `S + n₊ = k·m` convert it into the target at mass one, and `boxQSumScaleB1`, `boxA2ScaleB1`
     and `boxCountsScaleB1` scale it back to arbitrary mass. -/
  -- ### thresholds and the joint-core constant (the parameter `M` is the constant `48`)
  obtain ⟨εa, hεa, hreg⟩ := Work.BoseFixB1.BddSector.regimeBdd (v := v) (R := R) hav hR
  obtain ⟨εb, γb, hMassD⟩ := Work.BoseFixB1.pairMassData (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨hεbpos, hγbpos, hMassD'⟩ := hMassD
  obtain ⟨C, hC0, hjoint⟩ := Work.BoseFixB1.SectorAux.a0A2QJointNormB1FixGood (v := v) (R0 := R)
    hv_supp hR hv hvrad hv1 h (M := 48) (by norm_num)
  refine ⟨min εa (min εb 1), C, lt_min hεa (lt_min hεbpos one_pos), hC0, ?_⟩
  intro μ hAdm n Φ u hu k hk
  -- ### expose the `let`-bound data of the statement
  simp only []
  obtain ⟨hμ, hdil, hPOK⟩ := hAdm
  have hdila : μ * (_root_.BoseGases.a v) ^ 3 ≤ εa := le_trans hdil (min_le_left _ _)
  have hdilb : μ * (_root_.BoseGases.a v) ^ 3 ≤ εb :=
    le_trans hdil (le_trans (min_le_right _ _) (min_le_left _ _))
  have hdil1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 :=
    le_trans hdil (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨hℓ, hd, hM1P, hR16, hRχ⟩ := hreg μ hμ hdila
  have hM48 : Work.BoseFixB1B.PBM v μ = 48 := by
    rw [Work.BoseFixB1B.PBM, Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hpM : 1 ≤ Work.BoseFixB1B.PBM v μ := hM1P
  rw [hM48]
  -- ### the sliding-box data
  have hVpos : 0 < Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u :=
    Work.BoseFixB1.boxMass_pos_of_goodSet hℓ hd hμ hu
  have hμv : 1 ≤ μ * Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u :=
    Work.BoseFixB1.SectorAux.one_le_mu_boxMassGood hav hμ hdil1 hu
  have hAmeas : MeasurableSet (PBB v μ u) :=
    Work.SmallBoxSliding.measurableSet_dlBox (PBℓ v μ) (PBd v μ) u
  have hVeq : Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u
      = (MeasureTheory.volume (PBB v μ u)).toReal := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.measureReal_def]
  have hAc : PBB v μ u ⊆ Submission.BoseGases.acube (PBℓ v μ) :=
    Work.SmallBoxSliding.dlBox_subset_acube (PBℓ v μ) (PBd v μ) u
  -- ### the sector piece and its regularity
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  obtain ⟨B0, hB0⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox n (PBℓ v μ)) (f := (Φ : Submission.BoseGases.X n → ℝ))
    hΦc.continuousOn
  have hΦb : ∀ x ∈ Submission.BoseGases.abox n (PBℓ v μ),
      |(Φ : Submission.BoseGases.X n → ℝ) x| ≤ B0 :=
    fun x hx => by simpa [Real.norm_eq_abs] using hB0 x hx
  have hΦg : Work.BoseFixB1S.GoodState (PBℓ v μ) (Φ : Submission.BoseGases.X n → ℝ) :=
    ⟨hΦc.measurable, B0, hΦb⟩
  have hΨg : Work.BoseFixB1S.GoodState (PBℓ v μ)
      (Work.FockBridge.sectorPiece (PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ)) :=
    goodState_sectorPiece hℓ hAmeas k hΦg
  have hΦbm : ∀ x ∈ Submission.BoseGases.abox n (PBℓ v μ),
      |(Φ : Submission.BoseGases.X n → ℝ) x| ≤ max B0 0 :=
    fun x hx => le_trans (hΦb x hx) (le_max_left _ _)
  -- ### the scalar data of the statement
  have hsec : Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
        (PBℓ v μ) (PBB v μ u)
        (Work.FockBridge.sectorPiece (PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ))
      + Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
        (PBℓ v μ) (PBB v μ u)
        (Work.FockBridge.sectorPiece (PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ))
      = (k : ℝ) * Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u)
          (Φ : Submission.BoseGases.X n → ℝ) k := by
    rw [Work.FockBridge.sectorMass_eq_integral_sectorPiece (L := PBℓ v μ) hAmeas hΦc.measurable k
      (Work.FockBridge.sectorMassENN_ne_top_of_ne_top (PBℓ v μ) (PBB v μ u)
        (Φ : Submission.BoseGases.X n → ℝ) k
        (Work.FockBridge.sectorMassENN_ne_top_of_continuous (N := n) (L := PBℓ v μ) hΦc))]
    exact Work.BoseFixB1.boxFlat_add_boxQCount_sectorPiece hℓ hVpos hAmeas hVeq hAc
      hΦc.measurable hΦbm
  have hm_eq : Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u)
      (Φ : Submission.BoseGases.X n → ℝ) k
      = ∫ x in Submission.BoseGases.abox n (PBℓ v μ),
          (Work.FockBridge.sectorPiece (PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 := by
    rw [Work.FockBridge.sectorMass_eq_integral_sectorPiece (L := PBℓ v μ) hAmeas hΦc.measurable k
      (Work.FockBridge.sectorMassENN_ne_top_of_ne_top (PBℓ v μ) (PBB v μ u)
        (Φ : Submission.BoseGases.X n → ℝ) k
        (Work.FockBridge.sectorMassENN_ne_top_of_continuous (N := n) (L := PBℓ v μ) hΦc))]
  have hm_nonneg : 0 ≤ Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u)
      (Φ : Submission.BoseGases.X n → ℝ) k := by
    rw [hm_eq]; exact MeasureTheory.integral_nonneg fun x => sq_nonneg _
  -- ### the count hypothesis: the sector piece is an eigenstate of the box count
  have hcount : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n (PBℓ v μ))),
      (Work.FockBridge.boxCount (PBB v μ u) x)
        * (Work.FockBridge.sectorPiece (PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2
        = (k : ℝ)
          * (Work.FockBridge.sectorPiece (PBB v μ u) k
              (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    by_cases hx : x ∈ Work.FockBridge.sectorSet (PBB v μ u) k
    · have h1 : Work.FockBridge.boxCount (PBB v μ u) x = (k : ℝ) :=
        Work.FockBridge.boxCount_eq_of_mem_sectorSet (PBB v μ u) hx
      rw [Work.FockBridge.sectorPiece, Set.indicator_of_mem hx, h1]
    · rw [Work.FockBridge.sectorPiece, Set.indicator_of_notMem hx]
      ring
  -- ### the `m = 0` case: every box word vanishes (the proved sibling lemma)
  by_cases hm0 : Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u)
      (Φ : Submission.BoseGases.X n → ℝ) k = 0
  · have hPsi0 : Work.FockBridge.sectorPiece (PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ)
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n (PBℓ v μ))] 0 := by
      have hInt : MeasureTheory.IntegrableOn
          (fun x => (Work.FockBridge.sectorPiece (PBB v μ u) k
            (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)
          (Submission.BoseGases.abox n (PBℓ v μ)) :=
        Work.BoseFixB1S.integrableOn_sq_of_bound hℓ hΨg.1 hΨg.2.choose_spec
      have h0 : (∫ x in Submission.BoseGases.abox n (PBℓ v μ),
          (Work.FockBridge.sectorPiece (PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)
          = 0 := by rw [← hm_eq]; exact hm0
      have hsq := (MeasureTheory.integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hInt).mp h0
      filter_upwards [hsq] with x hx
      exact sq_eq_zero_iff.mp (by simpa [pow_two] using hx)
    obtain ⟨hS0, hnq0, hA20, hQSum0⟩ :=
      Work.BoseFixB1.SectorAux.boxWords_eq_zero_of_ae_eq_zero (PBℓ v μ)
        (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u) μ (PBB v μ u) hAmeas hAc
        (Submission.BoseGases.wSmallPair 48 (PBℓ v μ) (PBd v μ) u v)
        (Submission.BoseGases.wSmall1Pair h 48 (PBℓ v μ) (PBd v μ) u)
        (Submission.BoseGases.wSmallPair 48 (PBℓ v μ) (PBd v μ) u
          (Submission.BoseGases.g2 v h))
        (Submission.BoseGases.omC (Classical.choose h)) hPsi0
    rw [hS0, hnq0, hA20, hQSum0, hm0]
    norm_num
  · -- ### `m ≠ 0`: rescale to mass one, apply the joint core, scale back
    have hmpos : 0 < Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u)
        (Φ : Submission.BoseGases.X n → ℝ) k := lt_of_le_of_ne hm_nonneg (Ne.symm hm0)
    -- ### name the statement's `let`-bound data
    set V : ℝ := Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u with hVdef
    set A : Set (EuclideanSpace ℝ (Fin 3)) := PBB v μ u with hAdef
    set Ψ : Submission.BoseGases.X n → ℝ :=
      Work.FockBridge.sectorPiece (PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ) with hΨdef
    set m : ℝ := Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u)
      (Φ : Submission.BoseGases.X n → ℝ) k with hmdef
    set S : ℝ := Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψ with hSdef
    set nq : ℝ := Work.BoseFixB1S.boxQCount V (PBℓ v μ) A Ψ with hnqdef
    set M1 : ℝ := Work.BoseFixB1S.boxM1 (PBℓ v μ) A
      (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) with hM1def
    set Pc : ℝ := Work.BoseFixB1S.boxPairCount V (PBℓ v μ) A Ψ with hPcdef
    set M2 : ℝ := Work.BoseFixB1S.boxM2 V A
      (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u
        (Submission.BoseGases.g2 v h)) with hM2def
    have hm_eq' : (∫ x in Submission.BoseGases.abox n (PBℓ v μ), (Ψ x) ^ 2) = m := by
      rw [← hm_eq, hmdef]
    have hsecS : S + nq = (k : ℝ) * m := by
      rw [hSdef, hnqdef, hmdef]; exact hsec
    have hM1nn : 0 ≤ M1 := by
      rw [hM1def]
      exact Work.BoseFixB1S.boxM1_nonneg_wSmall (v := v) (R0 := R) hv_supp hR hv hvrad h
        (M := PBM v μ) (ℓ := PBℓ v μ) (d := PBd v μ) u
    have hAdmb : Work.BoseBoxFix.Adm v εb μ := ⟨hμ, hdilb, hPOK⟩
    have hM2le : M1 ≤ M2 := by
      rw [hM1def, hM2def]
      refine le_trans ?_ (hMassD' μ hAdmb u hVpos)
      nlinarith [hM1nn, hγbpos]
    set tt : ℝ := 1 / Real.sqrt m with httdef
    have htpos : 0 < tt := by rw [httdef]; positivity
    have httsq : tt ^ 2 = 1 / m := by
      rw [httdef, div_pow, one_pow, Real.sq_sqrt hmpos.le]
    -- ### the scaled state
    set Ψt : Submission.BoseGases.X n → ℝ := fun x => tt * Ψ x with hΨtdef
    have hΨtm : Measurable Ψt := hΨg.1.const_mul tt
    have hΨtb : ∀ x ∈ Submission.BoseGases.abox n (PBℓ v μ),
        |Ψt x| ≤ tt * max hΨg.2.choose 0 := by
      intro x hx
      rw [hΨtdef, abs_mul, abs_of_pos htpos]
      exact mul_le_mul_of_nonneg_left
        (le_trans (hΨg.2.choose_spec x hx) (le_max_left _ _)) htpos.le
    have hΨtg : Work.BoseFixB1S.GoodState (PBℓ v μ) Ψt :=
      ⟨hΨtm, tt * max hΨg.2.choose 0, hΨtb⟩
    have hPct : Work.BoseFixB1S.boxPairCount V (PBℓ v μ) A Ψt = tt ^ 2 * Pc := by
      rw [hPcdef, hΨtdef]
      exact Work.BoseFixB1S.boxPairCount_scale V (PBℓ v μ) A Ψ tt
    -- ### mass one
    have hnormt : (∫ x in Submission.BoseGases.abox n (PBℓ v μ), (Ψt x) ^ 2) = 1 := by
      have h1 : (∫ x in Submission.BoseGases.abox n (PBℓ v μ), (Ψt x) ^ 2)
          = tt ^ 2 * ∫ x in Submission.BoseGases.abox n (PBℓ v μ), (Ψ x) ^ 2 := by
        rw [hΨtdef]
        rw [show (fun x => (tt * Ψ x) ^ 2)
            = fun x => tt ^ 2 * (Ψ x) ^ 2 by funext x; ring,
          MeasureTheory.integral_const_mul]
      have hm_int : m = ∫ x in Submission.BoseGases.abox n (PBℓ v μ), (Ψ x) ^ 2 := by
        rw [hmdef]; exact hm_eq
      rw [h1, ← hm_int, httsq]
      field_simp
    -- ### the count hypothesis and the sector identity at the scaled state
    have hscalet : ∀ (f : Submission.BoseGases.X n → ℝ),
        (∫ x in Submission.BoseGases.abox n (PBℓ v μ), f x) * tt ^ 2 * tt ^ 2
          = tt ^ 2 * (∫ x in Submission.BoseGases.abox n (PBℓ v μ), f x) * tt ^ 2 := by
      intro f; ring
    have hSt : Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψt = tt ^ 2 * S := by
      rw [hSdef, hΨtdef]
      exact Work.BoseFixB1S.boxFlatCount_scale V (PBℓ v μ) A Ψ tt
    have hnqt : Work.BoseFixB1S.boxQCount V (PBℓ v μ) A Ψt = tt ^ 2 * nq := by
      rw [hnqdef, hΨtdef]
      exact Work.BoseFixB1S.boxQCount_scale V (PBℓ v μ) A Ψ tt
    have hcountA : ∀ᵐ x ∂(MeasureTheory.volume.restrict
        (Submission.BoseGases.abox n (PBℓ v μ))),
        (Work.FockBridge.boxCount A x) * (Ψ x) ^ 2 = (k : ℝ) * (Ψ x) ^ 2 := hcount
    -- ### the normalised target inequality (the joint core + `boxTarget_of_joint`)
    have hnormK : Work.BoseFixB1.a0MainLocBox V μ M1
          (Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψt)
        + Work.BoseFixB1.boxA2 (PBℓ v μ) V A
            (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) Ψt
        - C * (_root_.BoseGases.a v)
            * (μ + (k : ℝ) / Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
            * Work.BoseFixB1S.boxQCount V (PBℓ v μ) A Ψt
        ≤ Work.BoseFixB1S.boxQSum V (PBℓ v μ) μ A
            (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
            (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
            (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u
              (Submission.BoseGases.g2 v h))
            (Submission.BoseGases.omC (Classical.choose h)) Ψt := by
      -- ### the split in the `A₀`-slack at mass one
      have hsp : Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψt ^ 2
            - Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψt
          = Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψt ^ 2
            - Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψt * (∫ x in Submission.BoseGases.abox n (PBℓ v μ), (Ψt x) ^ 2) := by
        rw [hnormt]; ring
      -- ### the side conditions at the scaled state
      have hPcnnt : 0 ≤ Work.BoseFixB1S.boxPairCount V (PBℓ v μ) A Ψt := by
        rw [Work.BoseFixB1S.boxPairCount]
        exact Finset.sum_nonneg fun p _ => MeasureTheory.integral_nonneg fun x => sq_nonneg _
      have hcS2t : Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψt
              * Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψt
            - Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψt
          ≤ Work.BoseFixB1S.boxPairCount V (PBℓ v μ) A Ψt := by
        have hJ0 := Work.BoseFixB1.boxFlatSqJensen_sectorPiece (N := n) (ℓ := PBℓ v μ) (V := V)
          (A := A) hℓ hVpos hAmeas hVeq hAc (k := k)
          (Φ := (Φ : Submission.BoseGases.X n → ℝ)) hΦc.measurable hΦbm
        have hJ0' : S * S - S * m ≤ m * Pc := by
          have hΨeq : Ψ = Work.FockBridge.sectorPiece A k
              (Φ : Submission.BoseGases.X n → ℝ) := by
            rw [hΨdef, ← hAdef]
          have h := hJ0
          rw [← hΨeq] at h
          rw [← hSdef, ← hPcdef, hm_eq'] at h
          simpa only [pow_two] using h
        have hL : tt ^ 2 * (S * S - S * m) = tt ^ 2 * S * S - S := by
          rw [httsq]; field_simp
        have hR : tt ^ 2 * (m * Pc) = Pc := by
          rw [httsq]; field_simp
        have key : tt ^ 2 * S * S - S ≤ Pc := by
          have h := mul_le_mul_of_nonneg_left hJ0' (sq_nonneg tt)
          calc tt ^ 2 * S * S - S = tt ^ 2 * (S * S - S * m) := hL.symm
            _ ≤ tt ^ 2 * (m * Pc) := h
            _ = Pc := hR
        rw [hSt, hPct]
        calc tt ^ 2 * S * (tt ^ 2 * S) - tt ^ 2 * S
            = tt ^ 2 * (tt ^ 2 * S * S - S) := by ring
          _ ≤ tt ^ 2 * Pc := mul_le_mul_of_nonneg_left key (sq_nonneg tt)
      -- ### the count hypothesis at the scaled state
      have hcountt : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n (PBℓ v μ))),
          (Work.FockBridge.boxCount (PBB v μ u) x) * (Ψt x) ^ 2 = (k : ℝ) * (Ψt x) ^ 2 := by
        filter_upwards [hcountA] with x hx
        simp only [hΨtdef]
        linear_combination (tt ^ 2) * hx
      -- ### the joint core at the scaled state
      have hJ := hjoint (ℓ := PBℓ v μ) (d := PBd v μ) (μ := μ) hℓ hd hμ hR16 hRχ u hVpos hμv
        hΨtm hΨtb hnormt (c := (k : ℝ)) hcountt hM1nn hM2le hPcnnt hcS2t
      -- ### the integrability bundles at the scaled state
      obtain ⟨hint0, hw2i, hfib⟩ :=
        Work.BoseFixB1.SectorAux.boxFragmentsIntegrableGood (v := v) (R0 := R) hv_supp hR hv hvrad
          hv1 h (M := PBM v μ) hM1P (ℓ := PBℓ v μ) (d := PBd v μ) (u := u) hℓ hd hR16 hRχ
          (Φ := Ψt) hΨtg
      obtain ⟨hint5, hintSq, hintCr⟩ :=
        Work.BoseFixB1.SectorAux.boxPairBlockIntegrableGood (v := v) (R0 := R) hv_supp hR hv hvrad
          hv1 h (M := PBM v μ) hM1P hℓ hd hR16 hRχ u (Φ := Ψt) hΨtg
      obtain ⟨hint1, hint2, hint3, hint4⟩ :=
        boxPairHintsGS (v := v) (R0 := R) hv_supp hR hv hvrad hv1 h (M := PBM v μ) hM1P hℓ hd
          hR16 hRχ u hVpos (Φ := Ψt) hΨtg
      -- ### the kernel identities
      have hw1 : ∀ x y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u x y
            = Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v x y
                * (1 - Submission.BoseGases.omC (Classical.choose h) x y) := by
        intro x y
        rw [Work.BoseFixB1.wSmall1Pair_eq_mul h u x y]
        simp only [Submission.BoseGases.omC]
      have hw2' : ∀ x y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u
              (Submission.BoseGases.g2 v h) x y
            = Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v x y
                * (1 - Submission.BoseGases.omC (Classical.choose h) x y ^ 2) := by
        intro x y
        rw [Work.BoseFixB1.wSmallPair_g2_eq_mul h u x y, Work.BoseFixB1.wSmall1Pair_eq_mul h u x y]
        simp only [Submission.BoseGases.omC]
        ring
      have hwsym : ∀ x y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v x y
            = Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v y x :=
        fun x y => Work.BoseFixB1.wSmallPair_symm' hvrad hM1P u x y
      have homsym : ∀ x y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.omC (Classical.choose h) x y
            = Submission.BoseGases.omC (Classical.choose h) y x :=
        fun x y => Work.BoseFixB1.omC_chosen_sym' h x y
      -- ### `(R1)` + the square/cross split
      have hred : Work.BoseFixB1S.boxQSum V (PBℓ v μ) μ A
            (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
            (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
            (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u
              (Submission.BoseGases.g2 v h))
            (Submission.BoseGases.omC (Classical.choose h)) Ψt
          - Work.BoseFixB1.boxA2 (PBℓ v μ) V A
              (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) Ψt
          + (2 * μ * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n (PBℓ v μ),
                (Work.UBBInputs8.boxQInd V A i Ψt x)
                  * (Work.UBBInputs8.boxPInd V A i Ψt x)
                  * Submission.BoseGases.w1Fibre (PBℓ v μ)
                      (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) (x i))
              + μ * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n (PBℓ v μ),
                  (Work.UBBInputs8.boxQInd V A i Ψt x) ^ 2
                    * Submission.BoseGases.w1Fibre (PBℓ v μ)
                        (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) (x i)))
          = Work.BoseFixB1S.boxQ0 V (PBℓ v μ) μ A
                (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
                (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u
                  (Submission.BoseGases.g2 v h)) Ψt
            + (Work.BoseFixB1.boxSqPart V (PBℓ v μ) A
                  (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
                  (Submission.BoseGases.omC (Classical.choose h)) Ψt
                + Work.BoseFixB1.boxCrossPart V (PBℓ v μ) A
                  (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) Ψt) := by
        have h1 := Work.BoseFixB1.SectorAux.boxQSum_sub_boxA2_blockSumGS (N := n) (ℓ := PBℓ v μ)
          (volA := V) (μ := μ) (A := A) hℓ hVpos hAmeas hVeq hAc
          (w := Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
          (w₁ := Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
          (w₂ := Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u
            (Submission.BoseGases.g2 v h))
          (om := Submission.BoseGases.omC (Classical.choose h))
          hw1 hw2' hwsym homsym hΨtg hint0 hint1 hint2 hint3 hint4 hint5
        have h2 := Work.BoseFixB1.boxSqPart_add_boxCrossPart_eq_blockSum (N := n) (ℓ := PBℓ v μ)
          (volA := V) (A := A)
          (w := Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
          (w₁ := Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
          (om := Submission.BoseGases.omC (Classical.choose h)) (Φ := Ψt) hintSq hintCr hint5 hw1
        linarith [h1, h2]
      -- ### the `A₀`-slack
      have hslack : Work.BoseFixB1S.boxQ0 V (PBℓ v μ) μ A
            (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
            (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u
              (Submission.BoseGases.g2 v h)) Ψt
          - Work.BoseFixB1.a0MainLocBox V μ
              (Work.BoseFixB1S.boxM1 (PBℓ v μ) A
                (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u))
              (Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψt)
        = Work.BoseFixB1S.boxM1 (PBℓ v μ) A
              (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
            * ((1 / 4) * (Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψt / V - μ) ^ 2
                + (Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψt / V + μ) / (2 * V)
                + 1 / (4 * V ^ 2))
          + (1 / 2) * (Work.BoseFixB1S.boxM2 V A
                (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u
                  (Submission.BoseGases.g2 v h)) / V ^ 2)
              * Work.BoseFixB1S.boxPairCount V (PBℓ v μ) A Ψt
          - (1 / 2) * (Work.BoseFixB1S.boxM1 (PBℓ v μ) A
                (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) / V ^ 2)
              * (Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψt ^ 2
                - Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψt) := by
        rw [boxQ0_sub_a0MainLocBox_eq_good (N := n) (ℓ := PBℓ v μ) (volA := V) (μ := μ)
            (A := A) hℓ hVpos hAmeas hVeq hAc
            (w1 := Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
            (w2 := Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u
              (Submission.BoseGases.g2 v h)) hw2i hfib hΨtg]
      -- ### the arithmetic core, fed by the joint core
      have hpay := Work.BoseFixB1S.boxTarget_of_joint (V := V) (μ := μ) (M₁ := M1) (M₂ := M2)
        (S := Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψt)
        (Pc := Work.BoseFixB1S.boxPairCount V (PBℓ v μ) A Ψt)
        (nq := Work.BoseFixB1S.boxQCount V (PBℓ v μ) A Ψt)
        (C := C) (aa := _root_.BoseGases.a v)
        (Sqp := Work.BoseFixB1.boxSqPart V (PBℓ v μ) A
          (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
          (Submission.BoseGases.omC (Classical.choose h)) Ψt)
        (L := Work.BoseFixB1.boxCrossPart V (PBℓ v μ) A
          (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) Ψt)
        (P := ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n (PBℓ v μ),
          (Work.UBBInputs8.boxQInd V A i Ψt x)
            * (Work.UBBInputs8.boxPInd V A i Ψt x)
            * Submission.BoseGases.w1Fibre (PBℓ v μ)
                (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) (x i))
        (Q := ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n (PBℓ v μ),
          (Work.UBBInputs8.boxQInd V A i Ψt x) ^ 2
            * Submission.BoseGases.w1Fibre (PBℓ v μ)
                (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) (x i))
        (Q0 := Work.BoseFixB1S.boxQ0 V (PBℓ v μ) μ A
          (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
          (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u
            (Submission.BoseGases.g2 v h)) Ψt)
        (A2 := Work.BoseFixB1.boxA2 (PBℓ v μ) V A
          (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) Ψt)
        (Qsum := Work.BoseFixB1S.boxQSum V (PBℓ v μ) μ A
          (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
          (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
          (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u
            (Submission.BoseGases.g2 v h))
          (Submission.BoseGases.omC (Classical.choose h)) Ψt)
        (a0 := Work.BoseFixB1.a0MainLocBox V μ
          (Work.BoseFixB1S.boxM1 (PBℓ v μ) A
            (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u))
          (Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψt))
        hVpos hM1nn hM2le hPcnnt hcS2t hred hslack hJ
      -- ### the credit conversion `(μ + S_t/V) ≤ (μ + k/V)`
      have hSk : Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψt ≤ (k : ℝ) := by
        have hnqt_nn : 0 ≤ Work.BoseFixB1S.boxQCount V (PBℓ v μ) A Ψt := by
          rw [Work.BoseFixB1S.boxQCount]
          exact Finset.sum_nonneg fun i _ => MeasureTheory.integral_nonneg fun x => sq_nonneg _
        have ht2m : tt ^ 2 * m = 1 := by rw [httsq]; field_simp
        have hsum : Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψt
            + Work.BoseFixB1S.boxQCount V (PBℓ v μ) A Ψt = (k : ℝ) := by
          calc Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψt
                + Work.BoseFixB1S.boxQCount V (PBℓ v μ) A Ψt
              = tt ^ 2 * (S + nq) := by rw [hSt, hnqt]; ring
            _ = tt ^ 2 * ((k : ℝ) * m) := by rw [hsecS]
            _ = (k : ℝ) := by
              linear_combination (k : ℝ) * ht2m
        linarith
      have hcred : C * (_root_.BoseGases.a v)
            * (μ + Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψt / V)
            * Work.BoseFixB1S.boxQCount V (PBℓ v μ) A Ψt
          ≤ C * (_root_.BoseGases.a v) * (μ + (k : ℝ) / V)
            * Work.BoseFixB1S.boxQCount V (PBℓ v μ) A Ψt := by
        have h2 : μ + Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψt / V ≤ μ + (k : ℝ) / V := by
          have := div_le_div_of_nonneg_right hSk hVpos.le
          linarith
        have h3 : (0 : ℝ) ≤ C * _root_.BoseGases.a v
            * Work.BoseFixB1S.boxQCount V (PBℓ v μ) A Ψt := by
          rw [Work.BoseFixB1S.boxQCount]
          exact mul_nonneg (mul_nonneg hC0 (le_of_lt hav))
            (Finset.sum_nonneg fun i _ => MeasureTheory.integral_nonneg fun x => sq_nonneg _)
        calc C * (_root_.BoseGases.a v)
              * (μ + Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψt / V)
              * Work.BoseFixB1S.boxQCount V (PBℓ v μ) A Ψt
            = C * _root_.BoseGases.a v * Work.BoseFixB1S.boxQCount V (PBℓ v μ) A Ψt
              * (μ + Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψt / V) := by ring
          _ ≤ C * _root_.BoseGases.a v * Work.BoseFixB1S.boxQCount V (PBℓ v μ) A Ψt
              * (μ + (k : ℝ) / V) := mul_le_mul_of_nonneg_left h2 h3
          _ = C * (_root_.BoseGases.a v) * (μ + (k : ℝ) / V)
              * Work.BoseFixB1S.boxQCount V (PBℓ v μ) A Ψt := by ring
      linarith [hpay, hcred]
    -- ### scale back: the target's inequality at `Ψ`
    -- The homogeneity bookkeeping.  `Ψt = fun x => tt * Ψ x` with `tt ^ 2 = 1 / m`, so
    -- `m · (word at Ψt) = word at Ψ` for the quadratic words, `S / m = boxFlatCount Ψt`,
    -- and the `A₀`-slack at `Ψ` is `m` times the one at `Ψt` (the scalar identity
    -- `T₁+T₂+T₃ = m·a0MainLocBox V μ M₁ (S/m)`).
    have hscal : (1 / 2) * (Work.BoseFixB1S.boxM1 (PBℓ v μ) A
              (Submission.BoseGases.wSmall1Pair h 48 (PBℓ v μ) (PBd v μ) u) / V ^ 2)
            * (S ^ 2 / m - S)
          - μ * (Work.BoseFixB1S.boxM1 (PBℓ v μ) A
              (Submission.BoseGases.wSmall1Pair h 48 (PBℓ v μ) (PBd v μ) u) / V) * S
          - Work.BoseFixB1S.boxM1 (PBℓ v μ) A
              (Submission.BoseGases.wSmall1Pair h 48 (PBℓ v μ) (PBd v μ) u)
            * (m * ((1 / 4) * (S / (m * V) - μ) ^ 2 + (S / (m * V) + μ) / (2 * V)
                + 1 / (4 * V ^ 2)))
        = m * Work.BoseFixB1.a0MainLocBox V μ
            (Work.BoseFixB1S.boxM1 (PBℓ v μ) A
              (Submission.BoseGases.wSmall1Pair h 48 (PBℓ v μ) (PBd v μ) u)) (S / m) := by
      rw [Work.BoseFixB1.a0MainLocBox]
      field_simp
      try ring
    have hSb : S / m = Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψt := by
      rw [hSt, httsq]
      ring
    have hA2b : Work.BoseFixB1.boxA2 (PBℓ v μ) V A
          (Submission.BoseGases.wSmall1Pair h 48 (PBℓ v μ) (PBd v μ) u) Ψ
        = m * Work.BoseFixB1.boxA2 (PBℓ v μ) V A
          (Submission.BoseGases.wSmall1Pair h 48 (PBℓ v μ) (PBd v μ) u) Ψt := by
      rw [hΨtdef, Work.BoseFixB1S.boxA2ScaleB1 (N := n) (ℓ := PBℓ v μ) (volA := V) (A := A)
        (w1 := Submission.BoseGases.wSmall1Pair h 48 (PBℓ v μ) (PBd v μ) u)
        (Φ := Ψ) (t := tt), httsq]
      field_simp
      try ring
    have hQb : Work.BoseFixB1S.boxQSum V (PBℓ v μ) μ A
          (Submission.BoseGases.wSmallPair 48 (PBℓ v μ) (PBd v μ) u v)
          (Submission.BoseGases.wSmall1Pair h 48 (PBℓ v μ) (PBd v μ) u)
          (Submission.BoseGases.wSmallPair 48 (PBℓ v μ) (PBd v μ) u
            (Submission.BoseGases.g2 v h))
          (Submission.BoseGases.omC (Classical.choose h)) Ψ
        = m * Work.BoseFixB1S.boxQSum V (PBℓ v μ) μ A
          (Submission.BoseGases.wSmallPair 48 (PBℓ v μ) (PBd v μ) u v)
          (Submission.BoseGases.wSmall1Pair h 48 (PBℓ v μ) (PBd v μ) u)
          (Submission.BoseGases.wSmallPair 48 (PBℓ v μ) (PBd v μ) u
            (Submission.BoseGases.g2 v h))
          (Submission.BoseGases.omC (Classical.choose h)) Ψt := by
      rw [hΨtdef, Work.BoseFixB1S.boxQSumScaleB1 (N := n) (volA := V) (ℓ := PBℓ v μ)
        (μ := μ) (A := A)
        (w := Submission.BoseGases.wSmallPair 48 (PBℓ v μ) (PBd v μ) u v)
        (w1 := Submission.BoseGases.wSmall1Pair h 48 (PBℓ v μ) (PBd v μ) u)
        (w2 := Submission.BoseGases.wSmallPair 48 (PBℓ v μ) (PBd v μ) u
          (Submission.BoseGases.g2 v h))
        (om := Submission.BoseGases.omC (Classical.choose h)) (Φ := Ψ) (t := tt), httsq]
      field_simp
      try ring
    have hcrb : C * (_root_.BoseGases.a v) * (μ + (k : ℝ) / V) * nq
        = m * (C * (_root_.BoseGases.a v) * (μ + (k : ℝ) / V)
            * Work.BoseFixB1S.boxQCount V (PBℓ v μ) A Ψt) := by
      rw [hnqt, httsq]
      field_simp
      try ring
    have h1 : (1 / 2) * (Work.BoseFixB1S.boxM1 (PBℓ v μ) A
              (Submission.BoseGases.wSmall1Pair h 48 (PBℓ v μ) (PBd v μ) u) / V ^ 2)
            * (S ^ 2 / m - S)
          - μ * (Work.BoseFixB1S.boxM1 (PBℓ v μ) A
              (Submission.BoseGases.wSmall1Pair h 48 (PBℓ v μ) (PBd v μ) u) / V) * S
          - Work.BoseFixB1S.boxM1 (PBℓ v μ) A
              (Submission.BoseGases.wSmall1Pair h 48 (PBℓ v μ) (PBd v μ) u)
            * (m * ((1 / 4) * (S / (m * V) - μ) ^ 2 + (S / (m * V) + μ) / (2 * V)
                + 1 / (4 * V ^ 2)))
          + Work.BoseFixB1.boxA2 (PBℓ v μ) V A
              (Submission.BoseGases.wSmall1Pair h 48 (PBℓ v μ) (PBd v μ) u) Ψ
          - C * (_root_.BoseGases.a v) * (μ + (k : ℝ) / V) * nq
        = m * (Work.BoseFixB1.a0MainLocBox V μ
              (Work.BoseFixB1S.boxM1 (PBℓ v μ) A
                (Submission.BoseGases.wSmall1Pair h 48 (PBℓ v μ) (PBd v μ) u))
              (Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A Ψt)
            + Work.BoseFixB1.boxA2 (PBℓ v μ) V A
              (Submission.BoseGases.wSmall1Pair h 48 (PBℓ v μ) (PBd v μ) u) Ψt
            - C * (_root_.BoseGases.a v) * (μ + (k : ℝ) / V)
              * Work.BoseFixB1S.boxQCount V (PBℓ v μ) A Ψt) := by
      rw [hscal, hSb, hA2b, hcrb]
      ring
    rw [h1, hQb]
    exact mul_le_mul_of_nonneg_left hnormK hmpos.le

end Work.BoseFixB1.SectorAux
