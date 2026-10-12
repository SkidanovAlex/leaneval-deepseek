import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.boxQInd_update_eq
import Submission.Work.FockBridge.tBamp_eq_zero_of_notMem_ampSector
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.sectorPieceBoxQIndAmpLe`

The windowed amplitude of a *sector piece* of a state is dominated by that of the state:
FS's box projection `Q_{A,i}` (`Work.UBBInputs8.boxQInd`) is *local on the `A`-occupancy sectors*,
because the sector indicator is invariant under replacing a slot by another point of `A`
(`Work.FockBridge.boxOccupancy_update_of_mem`).  Consequently the sector piece
`1_{n_A = k}·Φ` (`Work.FockBridge.sectorPiece`) satisfies, at every box-replacement of slot `i`,

    Q_{A,i}(1_{n_A=k}Φ)(x[i↦z]) = d · Q_{A,i}Φ(x[i↦z]) ,

with the *single* number `d = 1_{ampSector A i k}(x) ∈ {0,1}` — it is `1_{n_A=k}(x)` when
`x i ∈ A`, and `1_{n_A=k}(x[i↦z])` for any `z ∈ A` when `x i ∉ A` (the *shifted* count of
`ampSector`).  The windowed amplitude `tBamp χ p Ψ i x = ∫_z χ(z)e^{−i⟪p,z⟫}Ψ(x[i↦z])dz` is an
integral of the slot-`i` fibre, so it inherits that factor:

    tBamp χ p (Q_{A,i}(1_{n_A=k}Φ)) i x = (d : ℂ) · tBamp χ p (Q_{A,i}Φ) i x ,

and the norm inequality follows because `d ∈ {0,1}`, hence `‖(d : ℂ)‖ ≤ 1`.

This is the *pointwise* companion of the Parseval decomposition `Work.FockBridge.sum_tBamp_normSq`
(which needs `supp χ ⊆ A`) and of the corpus's `Work.BoseFixB1.tBdiagFormInd_eq_sum_sectorPiece`.
Unlike those, no hypothesis on `χ` is needed here: the box indicator inside `boxQInd` already kills
the slot-`i` fibre outside `A`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Work.FockBridge

/-- **`tBamp` of a state that is a constant multiple of another one along the slot-`i` fibre.**
The amplitude is the integral of `(χ z)e^{−i⟪p,z⟫}·Ψ(x[i↦z])` over `z`, so a constant factor in the
state comes out of the integral.  No measurability or integrability is needed: the equality of the
two integrands is *pointwise*, and the Bochner integral is a total function. -/
lemma tBamp_eq_ofReal_mul_of_fibre_eq {n : ℕ} (χ : ℝ³ → ℝ) (p : ℝ³) (i : Fin n)
    {Ψ Ψ' : Submission.BoseGases.X n → ℝ} {c : ℝ} {x : Submission.BoseGases.X n}
    (h : ∀ z : ℝ³, Ψ (Function.update x i z) = c * Ψ' (Function.update x i z)) :
    Work.SmallBoxTBWord.tBamp χ p Ψ i x
      = (c : ℂ) * Work.SmallBoxTBWord.tBamp χ p Ψ' i x := by
  rw [Work.SmallBoxTBWord.tBamp, Work.SmallBoxTBWord.tBamp]
  trans ∫ z : ℝ³, (c : ℂ) * ((χ z : ℂ) *
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (Ψ' (Function.update x i z) : ℂ))
  · exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => by
      simp only [h z, Complex.ofReal_mul]
      ring))
  · rw [MeasureTheory.integral_const_mul]

/-- **The shifted count of a box-replacement of slot `i`.**  Replacing slot `i` by a point `z` of
`A` changes the `A`-count exactly by the shifted-count rule of `Work.FockBridge.ampSector`, so the
sector membership of `x[i↦z]` is the amplitude-sector membership of `x`. -/
lemma sectorSet_update_mem_iff_ampSector {n : ℕ} {A : Set ℝ³} (x : Submission.BoseGases.X n)
    (i : Fin n) (k : ℕ) {z : ℝ³} (hz : z ∈ A) :
    (Function.update x i z ∈ Work.FockBridge.sectorSet A k
        ↔ x ∈ Work.FockBridge.ampSector A i k) := by
  rw [Work.FockBridge.mem_sectorSet_iff, Work.FockBridge.mem_ampSector_iff,
    Work.FockBridge.boxOccupancy_update_of_mem A x i hz]

/-- The pointwise identity: replacing slot `i` by a point of the box, FS's projections of the
sector piece and of the state differ by the *single* factor `d = 1_{ampSector A i k}(x)`. -/
lemma boxQInd_sectorPiece_update_eq {n : ℕ} {A : Set ℝ³} (hA : MeasurableSet A)
    {volA : ℝ} {k : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (i : Fin n)
    (x : Submission.BoseGases.X n) :
    ∃ d : ℝ, (d = 0 ∨ d = 1) ∧ ∀ z : ℝ³,
      Work.UBBInputs8.boxQInd volA A i (Work.FockBridge.sectorPiece A k Φ)
          (Function.update x i z)
        = d * Work.UBBInputs8.boxQInd volA A i Φ (Function.update x i z) := by
  classical
  refine ⟨(Work.FockBridge.ampSector A i k).indicator (fun _ => (1 : ℝ)) x, ?_, ?_⟩
  · by_cases hx : x ∈ Work.FockBridge.ampSector A i k
    · exact Or.inr (Set.indicator_of_mem hx (fun _ => (1 : ℝ)))
    · exact Or.inl (Set.indicator_of_notMem hx (fun _ => (1 : ℝ)))
  intro z
  have hfib : ∀ w ∈ A, Work.FockBridge.sectorPiece A k Φ (Function.update x i w)
      = (Work.FockBridge.ampSector A i k).indicator (fun _ => (1 : ℝ)) x
          * Φ (Function.update x i w) := by
    intro w hw
    have hmem := sectorSet_update_mem_iff_ampSector x i k hw
    rw [Work.FockBridge.sectorPiece]
    by_cases hx : x ∈ Work.FockBridge.ampSector A i k
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx)]
      simp
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (fun hc => hx (hmem.mp hc))]
      simp
  rw [boxQInd_update_eq volA A i (Work.FockBridge.sectorPiece A k Φ) x z,
    boxQInd_update_eq volA A i Φ x z]
  by_cases hz : z ∈ A
  · have hz1 : A.indicator (fun _ => (1 : ℝ)) z = 1 := by
      rw [Set.indicator_of_mem hz]
    have hint : (∫ w in A, Work.FockBridge.sectorPiece A k Φ (Function.update x i w))
        = (Work.FockBridge.ampSector A i k).indicator (fun _ => (1 : ℝ)) x
            * ∫ w in A, Φ (Function.update x i w) := by
      rw [MeasureTheory.setIntegral_congr_fun hA (fun w hw => hfib w hw),
        MeasureTheory.integral_const_mul]
    rw [hz1, hfib z hz, hint]
    ring
  · have hz0 : A.indicator (fun _ => (1 : ℝ)) z = 0 :=
      Set.indicator_of_notMem hz (fun _ => (1 : ℝ))
    rw [hz0]
    ring

theorem sectorPieceBoxQIndAmpLe {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    {volA : ℝ} {k : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (i : Fin n) (p : EuclideanSpace ℝ (Fin 3))
    (x : Submission.BoseGases.X n) :
    ‖Work.SmallBoxTBWord.tBamp χ p
        (Work.UBBInputs8.boxQInd volA A i (Work.FockBridge.sectorPiece A k Φ)) i x‖
      ≤ ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ := by
  obtain ⟨d, hd01, hQ⟩ := boxQInd_sectorPiece_update_eq (A := A) hA (volA := volA) (k := k) i x
  have htB := tBamp_eq_ofReal_mul_of_fibre_eq χ p i (x := x) hQ
  rw [htB, norm_mul]
  calc ‖(d : ℂ)‖
        * ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖
      ≤ 1 * ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rcases hd01 with h | h <;> rw [h] <;> simp
    _ = ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ :=
        one_mul _

end Work.BoseFixB1
