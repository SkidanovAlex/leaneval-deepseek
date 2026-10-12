import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.PerSector.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.PerSector.Strat` — the slot stratification and the slot masses

The **slot stratification** of the occupancy sectors: the occupancy sector `sectorSet B k` is the
disjoint union of the slot sets `slotSet B S` with `S.card = k`, so every sector piece splits into
its slot pieces and every sector mass into its slot masses.  Nothing here is analytic; these are the
level sets of the counting function `boxOccupancy`.

Main statements:

* `slotSet_measurable`, `slotSet_subset_sectorSet`, `slotSet_eq_of_mem`, `slotSet_disjoint`,
  `iUnion_slotSet`, `sectorSet_eq_biUnion_slotSet` (`Defs.lean`);
* `sum_indicator_slotSet`, `sum_indicator_slotSet_powersetCard` — the indicators of the slot sets
  sum to the indicator of the configuration space resp. of the occupancy sector;
* `sectorPiece_eq_sum_slotPiece` — the Fock decomposition of a sector piece into slot pieces;
* `slotMass_nonneg`, `slotMassENN_le_total`, `slotMassENN_ne_top_of_ne_top` — finiteness of the
  slot masses;
* `sectorMassENN_eq_sum_slotMassENN`, `sectorMass_eq_sum_slotMass` — the sector mass is the sum
  of its slot masses;
* `slotPiece_sq`, `sum_slotPiece_sq` — the pointwise square decomposition.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.PerSector

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases
open Work.FockBridge
open Classical

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {N : ℕ}

/-! ## 1. Measurability -/

/-- The slot sets are measurable. -/
theorem slotSet_measurable (B : Set ℝ³) (hB : MeasurableSet B) (S : Finset (Fin N)) :
    MeasurableSet (slotSet B S) := by
  classical
  have h : slotSet B S
      = ⋂ i : Fin N, (fun x : X N => x i) ⁻¹' (if i ∈ S then B else Bᶜ) := by
    ext x
    simp only [mem_slotSet_iff, Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro hx i
      have hi := hx i
      by_cases h : i ∈ S
      · simp only [h, if_pos]; exact hi.mpr h
      · simp only [h, if_neg, Set.mem_compl_iff, not_false_iff]
        exact fun hc => h (hi.mp hc)
    · intro hx i
      have hi := hx i
      by_cases h : i ∈ S
      · simp only [h, if_pos] at hi
        exact ⟨fun _ => h, fun _ => hi⟩
      · simp only [h, if_neg, Set.mem_compl_iff, not_false_iff] at hi
        exact ⟨fun hc => absurd hc hi, fun hiS => absurd hiS h⟩
  rw [h]
  refine MeasurableSet.iInter (fun i => ?_)
  refine (measurable_pi_apply i) ?_
  by_cases h : i ∈ S
  · rw [if_pos h]; exact hB
  · rw [if_neg h]; exact hB.compl

theorem slotPiece_measurable (B : Set ℝ³) (hB : MeasurableSet B) (S : Finset (Fin N))
    {Φ : X N → ℝ} (hΦ : Measurable Φ) : Measurable (slotPiece B S Φ) :=
  hΦ.indicator (slotSet_measurable B hB S)

/-! ## 2. The slot indicators sum to the sector indicators -/

/-- **The slot indicators partition the configuration space**: summing over all slot sets gives
the indicator of the whole space (the occupant of a configuration is the set of its in-box slots,
and it is unique). -/
theorem sum_indicator_slotSet {α : Type*} [AddCommMonoid α] (B : Set ℝ³) (g : X N → α)
    (x : X N) :
    ∑ S : Finset (Fin N), (slotSet B S).indicator g x = g x := by
  classical
  have hmem₀ : x ∈ slotSet B (Finset.univ.filter (fun i : Fin N => x i ∈ B)) := by
    intro i
    rw [Finset.mem_filter]
    exact ⟨fun h => ⟨Finset.mem_univ i, h⟩, fun h => h.2⟩
  rw [Finset.sum_eq_single (Finset.univ.filter (fun i : Fin N => x i ∈ B))]
  · exact Set.indicator_of_mem hmem₀ g
  · intro S _ hne
    exact Set.indicator_of_notMem (fun hxS => hne (slotSet_eq_of_mem hxS hmem₀)) g
  · intro hnot; exact absurd (Finset.mem_univ _) hnot

/-- **The slot indicators of a fixed cardinality partition the corresponding occupancy sector**:
summing over the slot sets of cardinality `k` gives the indicator of `sectorSet B k`. -/
theorem sum_indicator_slotSet_powersetCard {α : Type*} [AddCommMonoid α] (B : Set ℝ³) (k : ℕ)
    (g : X N → α) (x : X N) :
    ∑ S ∈ Finset.univ.powersetCard k, (slotSet B S).indicator g x
      = (sectorSet B k).indicator g x := by
  classical
  by_cases hx : x ∈ sectorSet B k
  · rw [Set.indicator_of_mem hx]
    obtain ⟨S₀, hS₀, hx₀⟩ := (mem_sectorSet_iff_exists_slotSet B k x).mp hx
    rw [Finset.sum_eq_single S₀]
    · exact Set.indicator_of_mem hx₀ g
    · intro S hS hne
      exact Set.indicator_of_notMem (fun hxS => hne (slotSet_eq_of_mem hxS hx₀)) g
    · intro hnot; exact absurd hS₀ hnot
  · rw [Set.indicator_of_notMem hx]
    have hzero : ∀ S ∈ Finset.univ.powersetCard k, (slotSet B S).indicator g x = (0 : α) :=
      fun S hS => Set.indicator_of_notMem
        (fun hxS => hx ((mem_sectorSet_iff_exists_slotSet B k x).mpr ⟨S, hS, hxS⟩)) g
    rw [Finset.sum_eq_zero hzero]

/-- **The Fock decomposition of a sector piece**: the sector piece is the sum of its slot
pieces. -/
theorem sectorPiece_eq_sum_slotPiece (B : Set ℝ³) (k : ℕ) (Φ : X N → ℝ) (x : X N) :
    sectorPiece B k Φ x = ∑ S ∈ Finset.univ.powersetCard k, slotPiece B S Φ x := by
  classical
  change (sectorSet B k).indicator Φ x
    = ∑ S ∈ Finset.univ.powersetCard k, (slotSet B S).indicator Φ x
  exact (sum_indicator_slotSet_powersetCard B k Φ x).symm

/-- The slot pieces of the full space sum back to the state. -/
theorem sum_slotPiece (B : Set ℝ³) (Φ : X N → ℝ) (x : X N) :
    ∑ S : Finset (Fin N), slotPiece B S Φ x = Φ x := by
  classical
  change ∑ S : Finset (Fin N), (slotSet B S).indicator Φ x = Φ x
  exact sum_indicator_slotSet B Φ x

/-! ## 3. The slot masses -/

theorem slotMassENN_nonneg (L : ℝ) (B : Set ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ) :
    0 ≤ slotMassENN L B S Φ := by simp [slotMassENN]

theorem slotMass_nonneg (L : ℝ) (B : Set ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ) :
    0 ≤ slotMass L B S Φ := ENNReal.toReal_nonneg

/-- Each slot mass is bounded by the total `abox`-`L²`-mass. -/
theorem slotMassENN_le_total (L : ℝ) (B : Set ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ) :
    slotMassENN L B S Φ ≤ ∫⁻ x in abox N L, ENNReal.ofReal ((Φ x) ^ 2) := by
  rw [slotMassENN]
  refine lintegral_mono (fun x => ?_)
  by_cases hx : x ∈ slotSet B S
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]; exact bot_le

/-- The slot masses are finite whenever the total mass is. -/
theorem slotMassENN_ne_top_of_ne_top (L : ℝ) (B : Set ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ)
    (hfin : (∫⁻ x in abox N L, ENNReal.ofReal ((Φ x) ^ 2)) ≠ ⊤) :
    slotMassENN L B S Φ ≠ ⊤ :=
  ne_top_of_le_ne_top hfin (slotMassENN_le_total L B S Φ)

/-- **The sector masses are the sums of their slot masses** (`ENNReal` form). -/
theorem sectorMassENN_eq_sum_slotMassENN (L : ℝ) {B : Set ℝ³} (hB : MeasurableSet B)
    {Φ : X N → ℝ} (hΦ : Measurable Φ) (k : ℕ) :
    sectorMassENN L B Φ k
      = ∑ S ∈ Finset.univ.powersetCard k, slotMassENN L B S Φ := by
  classical
  have hmeas : ∀ S ∈ Finset.univ.powersetCard k,
      Measurable (fun x : X N =>
        (slotSet B S).indicator (fun x => ENNReal.ofReal ((Φ x) ^ 2)) x) :=
    fun S _ => ((hΦ.pow_const 2).ennreal_ofReal).indicator (slotSet_measurable B hB S)
  have hsum : (∫⁻ x in abox N L, ∑ S ∈ Finset.univ.powersetCard k,
      (slotSet B S).indicator (fun x => ENNReal.ofReal ((Φ x) ^ 2)) x)
      = ∑ S ∈ Finset.univ.powersetCard k, slotMassENN L B S Φ :=
    lintegral_finsetSum (Finset.univ.powersetCard k) hmeas
  rw [sectorMassENN, ← hsum]
  refine lintegral_congr (fun x => ?_)
  exact (sum_indicator_slotSet_powersetCard B k (fun y => ENNReal.ofReal ((Φ y) ^ 2)) x).symm

/-- **The sector masses are the sums of their slot masses** (real form). -/
theorem sectorMass_eq_sum_slotMass (L : ℝ) {B : Set ℝ³} (hB : MeasurableSet B)
    {Φ : X N → ℝ} (hΦ : Measurable Φ)
    (hfin : (∫⁻ x in abox N L, ENNReal.ofReal ((Φ x) ^ 2)) ≠ ⊤) (k : ℕ) :
    sectorMass L B Φ k = ∑ S ∈ Finset.univ.powersetCard k, slotMass L B S Φ := by
  have h := sectorMassENN_eq_sum_slotMassENN (N := N) L hB hΦ k
  simp only [sectorMass, slotMass]
  rw [h]
  exact ENNReal.toReal_sum (fun S _ => slotMassENN_ne_top_of_ne_top L B S Φ hfin)

/-! ## 4. The pointwise square decomposition -/

/-- The slot piece is a square root of the slot indicator. -/
theorem slotPiece_sq (B : Set ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ) (x : X N) :
    (slotPiece B S Φ x) ^ 2 = (slotSet B S).indicator (fun y => (Φ y) ^ 2) x := by
  by_cases hx : x ∈ slotSet B S
  · rw [slotPiece, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [slotPiece, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

/-- The slot pieces reproduce the density (the pointwise Fock decomposition of `Φ²`). -/
theorem sum_slotPiece_sq (B : Set ℝ³) (k : ℕ) (Φ : X N → ℝ) (x : X N) :
    ∑ S ∈ Finset.univ.powersetCard k, (slotPiece B S Φ x) ^ 2 = (sectorPiece B k Φ x) ^ 2 := by
  rw [Finset.sum_congr rfl (fun S _ => slotPiece_sq B S Φ x), sectorPiece_sq]
  exact sum_indicator_slotSet_powersetCard B k (fun y => (Φ y) ^ 2) x

end Work.PerSector
