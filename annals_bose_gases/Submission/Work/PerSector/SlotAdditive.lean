import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.PerSector.cnPlusBoxInd_eq_sum_slotPiece
import Submission.Work.PerSector.qLHSword_eq_sum_slotPiece
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.PerSector.SlotAdditive` — the slot additivity of the localised word

The formal locality statement behind the reduction `perSectorBound_of_slotWordBound`: the localised
per-box word (`tBwordBInd + qLHSwordB`) of a *sector piece* is the sum of the words of its *slot
pieces*.  Given the per-slot additivity of the excited count `cnPlusBoxInd` and of the `p`-diagonal
form `tBdiagFormInd` — which is what the pointwise support/Parseval atoms of this directory deliver —
the word-level statement is *pure rearrangement* (exactly as in
`Work.FockBridge.tBwordInd_eq_sum_sectorPiece`), and the sector-piece form follows from the state
form by the pointwise facts `slotPiece_S (sectorPiece B k Φ) = slotPiece_S Φ` for `S.card = k` and
`= 0` otherwise.

The remaining hypothesis of `sectorPiece_word_eq_sum_slotPiece` below — the per-slot additivity of
the two halves *of the sector piece* — is the integrability-bearing form of the delegated pointwise
atoms `sq_boxQInd_eq_sum_sq_boxQInd_slotPiece` and `sum_tBamp_normSq_slotPiece`; that is `hadd` of
`perSectorBound_of_slotWordBound`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.PerSector

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases
open Work.FockBridge
open Work.UBBInputs8
open Work.SmallBoxSliding
open Work.UBB
open Classical

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {N : ℕ}

/-! ## 1. The capstone: the per-box kinetic word is slot-additive -/

/-- **The per-box kinetic word is slot-additive** (the slot analogue of
`Work.FockBridge.tBwordInd_eq_sum_sectorPiece`): given the per-slot additivity of the excited count
and of the `p`-diagonal form, the gap term and the spectral term both decompose over the slot pieces,
and the only content is the rearrangement of the doubly indexed sums. -/
theorem tBwordInd_eq_sum_slotPiece {N : ℕ} {A : Set ℝ³} {volA a s ε c : ℝ} {χ : ℝ³ → ℝ}
    {Φ : X N → ℝ}
    (hcn : ∀ i : Fin N, (∫ x in abox N a, (boxQInd volA A i Φ x) ^ 2)
      = ∑ S : Finset (Fin N),
          ∫ x in abox N a, (boxQInd volA A i (slotPiece A S Φ) x) ^ 2)
    (hd : ∀ i : Fin N, (∫ p : ℝ³, fsKinCoeff c ‖p‖
          * ((a ^ 3)⁻¹ * ∫ x in abox N a, ‖SmallBoxTBWord.tBamp χ p (boxQInd volA A i Φ) i x‖ ^ 2))
      = ∑ S : Finset (Fin N),
          ∫ p : ℝ³, fsKinCoeff c ‖p‖
            * ((a ^ 3)⁻¹ * ∫ x in abox N a,
              ‖SmallBoxTBWord.tBamp χ p (boxQInd volA A i (slotPiece A S Φ)) i x‖ ^ 2)) :
    tBwordInd a A volA χ s ε c Φ
      = ∑ S : Finset (Fin N), tBwordInd a A volA χ s ε c (slotPiece A S Φ) := by
  have hcn' : (∑ i : Fin N, ∫ x in abox N a, (boxQInd volA A i Φ x) ^ 2)
      = ∑ S : Finset (Fin N),
          ∑ i : Fin N, ∫ x in abox N a,
            (boxQInd volA A i (slotPiece A S Φ) x) ^ 2 := by
    rw [Finset.sum_congr rfl (fun i _ => hcn i), Finset.sum_comm]
  have hd' : (∑ i : Fin N, ∫ p : ℝ³, fsKinCoeff c ‖p‖
        * ((a ^ 3)⁻¹ * ∫ x in abox N a,
          ‖SmallBoxTBWord.tBamp χ p (boxQInd volA A i Φ) i x‖ ^ 2))
      = ∑ S : Finset (Fin N),
          ∑ i : Fin N, ∫ p : ℝ³, fsKinCoeff c ‖p‖
            * ((a ^ 3)⁻¹ * ∫ x in abox N a,
              ‖SmallBoxTBWord.tBamp χ p (boxQInd volA A i (slotPiece A S Φ)) i x‖ ^ 2) := by
    rw [Finset.sum_congr rfl (fun i _ => hd i), Finset.sum_comm]
  simp only [tBwordInd, cnPlusBoxInd, tBwordKinInd, tBdiagFormInd, hcn',
    Finset.mul_sum, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum, hd']

/-- The sliding instance: the localised per-box kinetic word of a state is the sum of the localised
words of its slot pieces. -/
theorem tBwordBInd_eq_sum_slotPiece {N : ℕ} {L d ε c : ℝ} {u : ℝ³} {Φ : X N → ℝ}
    (hcn : ∀ i : Fin N, (∫ x in abox N L, (boxQInd (boxMass L d u) (dlBox L d u) i Φ x) ^ 2)
      = ∑ S : Finset (Fin N),
          ∫ x in abox N L,
            (boxQInd (boxMass L d u) (dlBox L d u) i (slotPiece (dlBox L d u) S Φ) x) ^ 2)
    (hd : ∀ i : Fin N, (∫ p : ℝ³, fsKinCoeff c ‖p‖
          * (((L) ^ 3)⁻¹ * ∫ x in abox N L,
            ‖SmallBoxTBWord.tBamp (chiB L d u) p
              (boxQInd (boxMass L d u) (dlBox L d u) i Φ) i x‖ ^ 2))
      = ∑ S : Finset (Fin N),
          ∫ p : ℝ³, fsKinCoeff c ‖p‖
            * (((L) ^ 3)⁻¹ * ∫ x in abox N L,
              ‖SmallBoxTBWord.tBamp (chiB L d u) p
                (boxQInd (boxMass L d u) (dlBox L d u) i (slotPiece (dlBox L d u) S Φ))
                  i x‖ ^ 2)) :
    tBwordBInd N L d ε c u Φ
      = ∑ S : Finset (Fin N), tBwordBInd N L d ε c u (slotPiece (dlBox L d u) S Φ) :=
  tBwordInd_eq_sum_slotPiece hcn hd



/-! ## 2. The word of the zero state, and the pointwise identification of the pieces -/

section ZeroAndPieces

variable {N : ℕ}

/-- FS's box projection of the zero state vanishes. -/
theorem boxQInd_zero (volA : ℝ) (A : Set ℝ³) (i : Fin N) :
    boxQInd volA A i (0 : X N → ℝ) = 0 := by
  funext x
  simp [boxQInd, boxPInd]

/-- The localised per-box kinetic word of the zero state vanishes. -/
theorem tBwordBInd_zero (N : ℕ) (L d ε c : ℝ) (u : ℝ³) :
    tBwordBInd N L d ε c u (0 : X N → ℝ) = 0 := by
  have h := tBwordInd_eq_zero_of_forall_notMem (A := dlBox L d u)
    (volA := boxMass L d u) (χ := chiB L d u) (a := L) (s := L * d) (ε := ε) (c := c)
    (Ψ := (0 : X N → ℝ)) (fun x _ => rfl)
  simpa [tBwordBInd] using h

/-- The localised per-box potential word of the zero state vanishes. -/
theorem qLHSwordB_zero {v : ℝ³ → ℝ} (h : ScatSol v) (M : ℕ) (L d μ : ℝ) (u : ℝ³) :
    qLHSwordB h M L d μ u (0 : X N → ℝ) = 0 := by
  simp only [qLHSwordB, qLHSword, Pi.zero_apply, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_mul, integral_zero]

/-- The slot piece of the sector piece at a slot set of its own cardinality is the slot piece of the
state. -/
theorem slotPiece_sectorPiece_eq_of_card_eq {B : Set ℝ³} {k : ℕ} {S : Finset (Fin N)}
    (hcard : S.card = k) (Φ : X N → ℝ) :
    slotPiece B S (sectorPiece B k Φ) = slotPiece B S Φ := by
  funext x
  by_cases hx : x ∈ slotSet B S
  · have hmem : x ∈ sectorSet B k := by
      rw [mem_sectorSet_iff]
      exact (boxOccupancy_eq_card_of_mem_slotSet B hx).trans hcard
    rw [slotPiece, Set.indicator_of_mem hx, slotPiece, Set.indicator_of_mem hx, sectorPiece,
      Set.indicator_of_mem hmem]
  · rw [slotPiece, Set.indicator_of_notMem hx, slotPiece, Set.indicator_of_notMem hx]

/-- The slot piece of the sector piece at a slot set of a *different* cardinality vanishes. -/
theorem slotPiece_sectorPiece_eq_zero_of_card_ne {B : Set ℝ³} {k : ℕ} {S : Finset (Fin N)}
    (hcard : S.card ≠ k) (Φ : X N → ℝ) :
    slotPiece B S (sectorPiece B k Φ) = 0 := by
  funext x
  by_cases hx : x ∈ slotSet B S
  · have hnot : x ∉ sectorSet B k := by
      intro hmem
      exact hcard ((boxOccupancy_eq_card_of_mem_slotSet B hx).symm.trans
        ((mem_sectorSet_iff B k x).mp hmem))
    rw [slotPiece, Set.indicator_of_mem hx, sectorPiece, Set.indicator_of_notMem hnot]
    rfl
  · rw [slotPiece, Set.indicator_of_notMem hx]
    rfl

end ZeroAndPieces

/-! ## 3. The slot additivity at the sector piece -/

/-- **The word of a sector piece is the sum of the words of its slot pieces.**  This is the `hadd`
consumed by `perSectorBound_of_slotWordBound`, derived from the state-level additivity
(`SlotAdditive.tBwordBInd_eq_sum_slotPiece` + `qLHSword_eq_sum_slotPiece`) at the state
`sectorPiece B k Φ` and the two pointwise facts `slotPiece_S (sectorPiece B k Φ) = slotPiece_S Φ`
(for `S.card = k`) resp. `= 0` (for `S.card ≠ k`).

The hypotheses are the per-slot additivity of the excited count and of the `p`-diagonal form *at the
sector piece* (`hcn`, `hd` — the integrability-bearing forms of the delegated pointwise atoms
`sq_boxQInd_eq_sum_sq_boxQInd_slotPiece`, `sum_tBamp_normSq_slotPiece`) and the `abox`-integrability
of the localised potential summands (`hq`). -/
theorem sectorPiece_slotWord_eq_sum_slotPiece {N : ℕ} {L d ε c μ : ℝ} {u : ℝ³} {v : ℝ³ → ℝ}
    (h : ScatSol v) (M : ℕ) (k : ℕ) {Φ : X N → ℝ}
    (hcn : ∀ i : Fin N, (∫ x in abox N L,
        (boxQInd (boxMass L d u) (dlBox L d u) i (sectorPiece (dlBox L d u) k Φ) x) ^ 2)
      = ∑ S : Finset (Fin N), ∫ x in abox N L,
          (boxQInd (boxMass L d u) (dlBox L d u) i
            (slotPiece (dlBox L d u) S (sectorPiece (dlBox L d u) k Φ)) x) ^ 2)
    (hd : ∀ i : Fin N, (∫ p : ℝ³, fsKinCoeff c ‖p‖
          * (((L) ^ 3)⁻¹ * ∫ x in abox N L,
            ‖SmallBoxTBWord.tBamp (chiB L d u) p
              (boxQInd (boxMass L d u) (dlBox L d u) i (sectorPiece (dlBox L d u) k Φ))
                i x‖ ^ 2))
      = ∑ S : Finset (Fin N),
          ∫ p : ℝ³, fsKinCoeff c ‖p‖
            * (((L) ^ 3)⁻¹ * ∫ x in abox N L,
              ‖SmallBoxTBWord.tBamp (chiB L d u) p
                (boxQInd (boxMass L d u) (dlBox L d u) i
                  (slotPiece (dlBox L d u) S (sectorPiece (dlBox L d u) k Φ))) i x‖ ^ 2))
    (hq : ∀ S : Finset (Fin N), IntegrableOn (fun x => qLHSden N L μ
        (wSmallPair M L d u v) (wSmall1Pair h M L d u) x
          * (slotPiece (dlBox L d u) S (sectorPiece (dlBox L d u) k Φ) x) ^ 2)
      (abox N L)) :
    (tBwordBInd N L d ε c u (sectorPiece (dlBox L d u) k Φ)
        + qLHSwordB h M L d μ u (sectorPiece (dlBox L d u) k Φ))
      = ∑ S ∈ Finset.univ.powersetCard k,
          (tBwordBInd N L d ε c u (slotPiece (dlBox L d u) S Φ)
            + qLHSwordB h M L d μ u (slotPiece (dlBox L d u) S Φ)) := by
  have hstate : (tBwordBInd N L d ε c u (sectorPiece (dlBox L d u) k Φ)
        + qLHSwordB h M L d μ u (sectorPiece (dlBox L d u) k Φ))
      = ∑ S : Finset (Fin N),
          (tBwordBInd N L d ε c u
              (slotPiece (dlBox L d u) S (sectorPiece (dlBox L d u) k Φ))
            + qLHSwordB h M L d μ u
              (slotPiece (dlBox L d u) S (sectorPiece (dlBox L d u) k Φ))) := by
    simp only [qLHSwordB]
    rw [tBwordBInd_eq_sum_slotPiece hcn hd,
      qLHSword_eq_sum_slotPiece (N := N) (ℓ := L) (μ := μ)
        (B := dlBox L d u) (w := wSmallPair M L d u v) (w1 := wSmall1Pair h M L d u)
        (Φ := sectorPiece (dlBox L d u) k Φ) hq,
      Finset.sum_add_distrib]
  rw [hstate]
  have hred : (∑ S : Finset (Fin N),
        (tBwordBInd N L d ε c u (slotPiece (dlBox L d u) S (sectorPiece (dlBox L d u) k Φ))
          + qLHSwordB h M L d μ u
            (slotPiece (dlBox L d u) S (sectorPiece (dlBox L d u) k Φ))))
      = ∑ S ∈ Finset.univ.powersetCard k,
          (tBwordBInd N L d ε c u
              (slotPiece (dlBox L d u) S (sectorPiece (dlBox L d u) k Φ))
            + qLHSwordB h M L d μ u
              (slotPiece (dlBox L d u) S (sectorPiece (dlBox L d u) k Φ))) := by
    refine (Finset.sum_subset (Finset.subset_univ _) (fun S _ hS => ?_)).symm
    have hcard : S.card ≠ k := fun hc =>
      hS (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hc⟩)
    rw [slotPiece_sectorPiece_eq_zero_of_card_ne hcard Φ, tBwordBInd_zero, qLHSwordB_zero,
      add_zero]
  rw [hred]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  rw [slotPiece_sectorPiece_eq_of_card_eq (Finset.mem_powersetCard.mp hS).2 Φ]

end Work.PerSector
