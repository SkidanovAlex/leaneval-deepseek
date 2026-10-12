import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FockBridge.Count
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.FockBridge.cnPlusBoxInd_eq_sum_sectorPiece`

The **sector decomposition of the box-projected (`Q_B`) square mass**.

FS's excited-count projection `Q_{B,i} = 1_{B,i} − P_{B,i}` (`Work.UBBInputs8.boxQInd`) acts on
slot `i` only.  Writing the state as the sum of its `B`-occupancy sectors
(`Φ = Σ_k sectorPiece B k Φ`, `Work.FockBridge.sum_sectorPiece`), the piece `Q_{B,i}(sectorPiece B k Φ)`
is **supported in the `B`-sector of count `k`** (off the sector both the box indicator and — when
`x i ∈ B` — the fibre average vanish; when `x i ∉ B` the box indicator kills both terms), and on the
sector `k` the projection leaves `Φ` alone.  Hence the pieces are disjointly supported, the cross
terms in `(Q_{B,i}Φ)²` vanish pointwise, and the `abox`-integral splits over the sectors.

This file proves the purely pointwise part (`cnPlusBoxInd` summand identity) and its `abox`
integral consequence, given the integrability of the squared amplitudes (which is what makes the
finite-sum/integral interchange legitimate).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.FockBridge

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases
open Classical

set_option autoImplicit false
set_option linter.unusedVariables false

variable {N : ℕ}

/-- **The projected sector piece is supported in its sector.**  If `x` is not in the count-`k`
sector of the box `A`, then `Q_{A,i}` applied to the count-`k` piece of `Φ` vanishes at `x`: the
box indicator term dies because the piece does, and the fibre-average term dies either because the
box indicator is `0` (`x i ∉ A`) or because the fibre `z ∈ A ↦ x[i↦z]` stays off the sector (so the
piece is `0` along the whole fibre). -/
lemma boxQInd_sectorPiece_eq_zero {A : Set ℝ³} (hA : MeasurableSet A)
    {volA : ℝ} (i : Fin N) {Φ : X N → ℝ} {k : ℕ} {x : X N}
    (hx : x ∉ sectorSet A k) :
    Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ) x = 0 := by
  rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
  have hpiece : sectorPiece A k Φ x = 0 := by
    rw [sectorPiece, Set.indicator_of_notMem hx]
  rw [hpiece, mul_zero, zero_sub]
  by_cases hxi : x i ∈ A
  · have hInt : (∫ z in A, sectorPiece A k Φ (Function.update x i z)) = 0 := by
      have hzero : Set.EqOn (fun z => sectorPiece A k Φ (Function.update x i z)) 0 A := by
        intro z hz
        simp only [Pi.zero_apply, sectorPiece]
        exact Set.indicator_of_notMem
          (fun hmem => hx ((mem_sectorSet_update_of_mem A hz hxi).mp hmem)) Φ
      rw [setIntegral_congr_fun hA hzero]
      simp
    rw [hInt]
    simp
  · rw [Set.indicator_of_notMem hxi (fun _ => (1:ℝ))]
    ring

/-- **On its own sector the projection sees the state.**  If `x` lies in the count-`k` sector of
the box `A`, then `Q_{A,i}Φ` and `Q_{A,i}(sectorPiece A k Φ)` agree at `x`: the box-indicator terms
agree because the piece equals `Φ` at `x`, and the fibre averages agree because on the whole fibre
`z ∈ A` the point `x[i↦z]` stays in the sector (when `x i ∈ A`), while if `x i ∉ A` both sides are
killed by the box indicator. -/
lemma boxQInd_sectorPiece_eq_of_mem {A : Set ℝ³} (hA : MeasurableSet A)
    {volA : ℝ} (i : Fin N) {Φ : X N → ℝ} {k : ℕ} {x : X N}
    (hx : x ∈ sectorSet A k) :
    Work.UBBInputs8.boxQInd volA A i Φ x
      = Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ) x := by
  unfold Work.UBBInputs8.boxQInd Work.UBBInputs8.boxPInd
  by_cases hxi : x i ∈ A
  · have hpiecex : sectorPiece A k Φ x = Φ x := by
      rw [sectorPiece, Set.indicator_of_mem hx]
    have hInt : (∫ z in A, Φ (Function.update x i z))
        = (∫ z in A, sectorPiece A k Φ (Function.update x i z)) := by
      refine setIntegral_congr_fun hA (fun z hz => ?_)
      rw [sectorPiece, Set.indicator_of_mem ((mem_sectorSet_update_of_mem A hz hxi).mpr hx)]
    rw [Set.indicator_of_mem hxi (fun _ => (1:ℝ)), hpiecex, hInt]
  · rw [Set.indicator_of_notMem hxi (fun _ => (1:ℝ))]
    ring

/-- **The pointwise sector decomposition of the projected square amplitude**: the squared
projection of `Φ` is the sum of the squared projections of its sector pieces.  The pieces are
supported on the disjoint sectors, and each restriction to a sector coincides with the projection
of `Φ` there, so the cross terms disappear. -/
lemma sq_boxQInd_eq_sum_sq_boxQInd_sectorPiece {A : Set ℝ³} (hA : MeasurableSet A)
    {volA : ℝ} (i : Fin N) {Φ : X N → ℝ} (x : X N) :
    (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2
      = ∑ k ∈ Finset.range (N + 1),
          (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ) x) ^ 2 := by
  have hmem : x ∈ sectorSet A (boxOccupancy A x) := rfl
  have hrange : boxOccupancy A x ∈ Finset.range (N + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (boxOccupancy_le A x))
  have hsingle : (∑ k ∈ Finset.range (N + 1),
        (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ) x) ^ 2)
      = (Work.UBBInputs8.boxQInd volA A i (sectorPiece A (boxOccupancy A x) Φ) x) ^ 2 :=
    Finset.sum_eq_single (boxOccupancy A x)
      (fun k _ hne => by
        have hx' : x ∉ sectorSet A k :=
          fun hx' => hne ((mem_sectorSet_iff A k x).mp hx').symm
        rw [boxQInd_sectorPiece_eq_zero hA i hx']
        simp)
      (fun hnot => absurd hrange hnot)
  rw [hsingle, boxQInd_sectorPiece_eq_of_mem hA i hmem]

/-- **The `abox`-integral sector decomposition of the projected square amplitude.**  Integrating
the pointwise identity `(Q_{A,i}Φ)² = Σ_k (Q_{A,i}(sectorPiece A k Φ))²` over the corpus box and
interchanging the finite sum with the integral — legitimate because each squared piece is
`abox`-integrable by hypothesis. -/
theorem cnPlusBoxInd_eq_sum_sectorPiece {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) {volA a : ℝ} (i : Fin N)
    {Φ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℝ}
    (hint : ∀ k ∈ Finset.range (N + 1), MeasureTheory.IntegrableOn
      (fun x => (Work.UBBInputs8.boxQInd volA A i (Work.FockBridge.sectorPiece A k Φ) x) ^ 2)
      (Submission.BoseGases.abox N a))
    (hint0 : MeasureTheory.IntegrableOn (fun x => (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
      (Submission.BoseGases.abox N a)) :
    ∫ x in Submission.BoseGases.abox N a, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2
      = ∑ k ∈ Finset.range (N + 1),
          ∫ x in Submission.BoseGases.abox N a,
            (Work.UBBInputs8.boxQInd volA A i (Work.FockBridge.sectorPiece A k Φ) x) ^ 2 := by
  calc ∫ x in Submission.BoseGases.abox N a, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2
      = ∫ x in Submission.BoseGases.abox N a, ∑ k ∈ Finset.range (N + 1),
          (Work.UBBInputs8.boxQInd volA A i (Work.FockBridge.sectorPiece A k Φ) x) ^ 2 :=
        integral_congr_ae (Filter.Eventually.of_forall
          (fun x => sq_boxQInd_eq_sum_sq_boxQInd_sectorPiece hA i x))
    _ = ∑ k ∈ Finset.range (N + 1),
          ∫ x in Submission.BoseGases.abox N a,
            (Work.UBBInputs8.boxQInd volA A i (Work.FockBridge.sectorPiece A k Φ) x) ^ 2 :=
        integral_finsetSum (Finset.range (N + 1)) (fun k hk => hint k hk)

end Work.FockBridge
