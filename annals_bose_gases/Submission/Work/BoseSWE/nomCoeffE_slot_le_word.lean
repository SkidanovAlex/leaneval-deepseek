import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseSWE.DefsE
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseSWE

open Classical
open Submission.BoseGases Work.BoseBoxFix Work.BoseKinLoc Work.PerSector
  Work.SmallBoxSliding Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

/-! # `Work.BoseSWE.nomCoeffE_slot_le_word` — the per-slot row of the `E`-twin of the nominal
# arity passage

This is the verbatim copy of the PROVED `Work.BoseB1Cube.nomCoeff_slot_le_word`
(`Submission/Work/BoseB1Cube/nomArbAux.lean` §6), with the nominal demand `nomRow` replaced by
its slack-carrying twin `nomRowE` and `nomCoeff` by `nomCoeffE`.  The demand is a state-independent
coefficient times the state's `abox`-mass (`nomRowE_eq_coeffE`), so the pointwise sharp row at each
fibre integrates in `y` without any change: the coefficient is a constant, and the two
factorisations (`normB_slotFibre`, `sbWordCube_slotFibre`) identify the two endpoints. -/

theorem nomCoeffE_slot_le_word {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R c₁ C CE ε₀ μ : ℝ}
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) (u : EuclideanSpace ℝ (Fin 3))
    (hu : u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (Work.BoseFixB1B.PBℓ v μ))
    (hsharp : Work.BoseSWE.NomSharpRowBodyE v h R c₁ C CE ε₀)
    (hmasse : ∀ (S : Finset (Fin n)) (e : Work.PerSector.SlotIn n S ≃ Fin S.card), 0 < S.card →
      MeasureTheory.Integrable
        (fun y : Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3) =>
          ∫ x in Submission.BoseGases.abox S.card (Work.BoseFixB1B.PBℓ v μ),
            (Work.BoseFixB1B.sharpBoxState (Work.BoseFixB1B.PBB v μ u)
              (Work.PerSector.slotFibreState S e (Φ : Submission.BoseGases.X n → ℝ) y) x) ^ 2)
        ((MeasureTheory.volume : MeasureTheory.Measure
          (Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3))).restrict
          (Work.PerSector.slotOutside (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u) S))
      ∧ (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1B.PBℓ v μ),
            (Work.PerSector.slotPiece (Work.BoseFixB1B.PBB v μ u) S
              (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)
          = ∫ y in Work.PerSector.slotOutside (Work.BoseFixB1B.PBℓ v μ)
                (Work.BoseFixB1B.PBB v μ u) S,
              ∫ x in Submission.BoseGases.abox S.card (Work.BoseFixB1B.PBℓ v μ),
                (Work.BoseFixB1B.sharpBoxState (Work.BoseFixB1B.PBB v μ u)
                  (Work.PerSector.slotFibreState S e (Φ : Submission.BoseGases.X n → ℝ) y) x) ^ 2)
    (hworde : ∀ (S : Finset (Fin n)) (e : Work.PerSector.SlotIn n S ≃ Fin S.card), 0 < S.card →
      MeasureTheory.Integrable
        (fun y : Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3) =>
          Work.BoseFixB1B.sbWordCube v h μ u
            (Work.BoseFixB1B.sharpBoxState (Work.BoseFixB1B.PBB v μ u)
              (Work.PerSector.slotFibreState S e (Φ : Submission.BoseGases.X n → ℝ) y)))
        ((MeasureTheory.volume : MeasureTheory.Measure
          (Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3))).restrict
          (Work.PerSector.slotOutside (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u) S))
      ∧ Work.BoseFixB1B.sbWordCube v h μ u
            (Work.PerSector.slotPiece (Work.BoseFixB1B.PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ))
          = ∫ y in Work.PerSector.slotOutside (Work.BoseFixB1B.PBℓ v μ)
                (Work.BoseFixB1B.PBB v μ u) S,
              Work.BoseFixB1B.sbWordCube v h μ u
                (Work.BoseFixB1B.sharpBoxState (Work.BoseFixB1B.PBB v μ u)
                  (Work.PerSector.slotFibreState S e (Φ : Submission.BoseGases.X n → ℝ) y)))
    (S : Finset (Fin n)) (hS : 0 < S.card) (e : Work.PerSector.SlotIn n S ≃ Fin S.card) :
    Work.BoseSWE.nomCoeffE v h R c₁ C CE μ u S.card
        * (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1B.PBℓ v μ),
            (Work.PerSector.slotPiece (Work.BoseFixB1B.PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)
      ≤ Work.BoseFixB1B.sbWordCube v h μ u
          (Work.PerSector.slotPiece (Work.BoseFixB1B.PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ)) := by
  classical
  obtain ⟨hmI, hmE⟩ := hmasse S e hS
  obtain ⟨hwI, hwE⟩ := hworde S e hS
  -- the pointwise sharp row at each fibre
  have hpt : ∀ᵐ y ∂((volume : Measure (SlotOut n S → E3)).restrict
      (slotOutside (PBℓ v μ) (PBB v μ u) S)),
      nomCoeffE v h R c₁ C CE μ u S.card
          * (∫ x in abox S.card (PBℓ v μ),
              (Work.BoseFixB1B.sharpBoxState (PBB v μ u)
                (slotFibreState S e (Φ : X n → ℝ) y) x) ^ 2)
        ≤ Work.BoseFixB1B.sbWordCube v h μ u
            (Work.BoseFixB1B.sharpBoxState (PBB v μ u)
              (slotFibreState S e (Φ : X n → ℝ) y)) :=
    Eventually.of_forall (fun y => by
      have hrow := hsharp μ hAdm S.card (slotFibreState S e (Φ : X n → ℝ) y)
        (Work.PerSector.contDiff_slotFibreState S e Φ.contDiff y)
        (Work.BoseFixB1B.permInvariant_slotFibreState S e Φ.symm y) u hu
      rwa [nomRowE_eq_coeffE] at hrow)
  have hInt1 : MeasureTheory.Integrable
      (fun y : SlotOut n S → E3 => nomCoeffE v h R c₁ C CE μ u S.card
        * (∫ x in abox S.card (PBℓ v μ),
            (Work.BoseFixB1B.sharpBoxState (PBB v μ u)
              (slotFibreState S e (Φ : X n → ℝ) y) x) ^ 2))
      ((volume : Measure (SlotOut n S → E3)).restrict (slotOutside (PBℓ v μ) (PBB v μ u) S)) :=
    hmI.const_mul _
  have hmono := MeasureTheory.integral_mono_ae hInt1 hwI hpt
  have hcI : (∫ y in slotOutside (PBℓ v μ) (PBB v μ u) S,
        nomCoeffE v h R c₁ C CE μ u S.card
          * (∫ x in abox S.card (PBℓ v μ),
              (Work.BoseFixB1B.sharpBoxState (PBB v μ u)
                (slotFibreState S e (Φ : X n → ℝ) y) x) ^ 2))
      = nomCoeffE v h R c₁ C CE μ u S.card
        * (∫ y in slotOutside (PBℓ v μ) (PBB v μ u) S,
            ∫ x in abox S.card (PBℓ v μ),
              (Work.BoseFixB1B.sharpBoxState (PBB v μ u)
                (slotFibreState S e (Φ : X n → ℝ) y) x) ^ 2) :=
    MeasureTheory.integral_const_mul _ _
  rw [hcI, ← hmE, ← hwE] at hmono
  exact hmono

end Work.BoseSWE
