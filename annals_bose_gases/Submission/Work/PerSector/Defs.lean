import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.bsOneBody_eq_zero_of_far
import Submission.Work.BSKinetic.Decomp.continuous_bsOneBody
import Submission.Work.BSKinetic.FamilyBound_of_le
import Submission.Work.BSKinetic.FarBump.Defs
import Submission.Work.BSKinetic.FarBump.oneBody_pos_of_low_freq_bound
import Submission.Work.BSKinetic.bsOneBody_eq_dirichlet
import Submission.Work.BSKinetic.cnPlus_eq_slotSum
import Submission.Work.BSKinetic.familyBigKin_eq_slotFamily
import Submission.Work.BSKinetic.familyFormUnproj_eq_kernelForm
import Submission.Work.BSKinetic.familyForm_zero_eq
import Submission.Work.BSKinetic.locKinEnWordBox_of_familyBound
import Submission.Work.BSKinetic.tBwordBInd_slotSwap_and_integrable
import Submission.Work.BSKinetic.tsupport_bsWin_subset_bsBox
import Submission.Work.FockBridge.SectorAdditive
import Submission.Work.FockBridge.SectorZero
import Submission.Work.FockBridge.convexOn_dlDensityCoeff
import Submission.Work.FockBridge.integrableOn_sectorPiece_sq
import Submission.Work.FockBridge.sectorMassENN_ne_top_of_continuous
import Submission.Work.FockBridge.sum_tBamp_normSq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.PerSector.Defs` — the slot/fibre layer of the per-sector bound

**Read `Submission/Work/FockBridge/README.md` (especially §6) first.**

This chapter supplies the two missing pieces of the `hsum` discharge:

1. **the fibre decomposition of a sector piece** (`Strat.lean`, `Fibre.lean`): the sector piece
   `Φ_k = 1_{n_{B(u)} = k}·Φ` is stratified by the *slot sets* `S : Finset (Fin N)` of its `k`
   in-box particles (`slotSet B S`), and Fubini over the `k` in-box coordinates and the `N - k`
   outside coordinates exhibits `Φ_k` as a measurable field of `k`-particle functions on `B(u)`
   whose box mass integrates back to the sector mass `m_k`;
2. **the word comparison at the count** (`Residual.lean`): the localised per-box word of each
   *slot piece* dominates its own slot mass times the DL threshold at the count — the sharpened
   (fibre-level) form of `Work.FockBridge.PerSectorBound`.

## Conventions

* `ℝ³ = EuclideanSpace ℝ (Fin 3)`, `X N = Fin N → ℝ³`;
* `abox N L` is the corpus centred `N`-particle box; all masses are taken there;
* a **slot set** `S : Finset (Fin N)` names a *set of particles*; `slotSet B S` is the set of
  configurations in which exactly the slots of `S` lie in `B`;
* `SlotIn N S = {i // i ∈ S}` and `SlotOut N S = {i // i ∉ S}` are the in-box and outside slot
  types; `slotComb S z y` reassembles a configuration from an inside configuration `z` and an
  outside configuration `y`;
* the **fibre** of `Φ` at the outside configuration `y` is `slotFibre S Φ y : (SlotIn N S → ℝ³)
  → ℝ`, `z ↦ Φ (slotComb S z y)` — the `k`-particle function on the box that FS's `thm:smallbox`
  is applied to.
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

/-! ## 1. The slot sets -/

/-- The slots of a slot set: the particles that lie in the box. -/
abbrev SlotIn (N : ℕ) (S : Finset (Fin N)) : Type := {i : Fin N // i ∈ S}

/-- The slots outside a slot set: the particles that lie outside the box. -/
abbrev SlotOut (N : ℕ) (S : Finset (Fin N)) : Type := {i : Fin N // i ∉ S}

/-- **The `B`-slot set of `S`**: the configurations in which exactly the slots of `S` (and no
others) lie in the box `B`.  These refine the occupancy sectors: `sectorSet B k` is the disjoint
union of the `slotSet B S` with `S.card = k`. -/
def slotSet (B : Set ℝ³) (S : Finset (Fin N)) : Set (X N) :=
  {x : X N | ∀ i : Fin N, (x i ∈ B ↔ i ∈ S)}

theorem mem_slotSet_iff (B : Set ℝ³) (S : Finset (Fin N)) (x : X N) :
    x ∈ slotSet B S ↔ ∀ i : Fin N, (x i ∈ B ↔ i ∈ S) := Iff.rfl

/-- The occupant of a slot set is the set of slots whose particle lies in the box. -/
theorem boxOccupancy_eq_card_of_mem_slotSet (B : Set ℝ³) {S : Finset (Fin N)} {x : X N}
    (hx : x ∈ slotSet B S) : boxOccupancy B x = S.card := by
  classical
  have hx' : ∀ i : Fin N, (x i ∈ B ↔ i ∈ S) := hx
  rw [boxOccupancy]
  congr 1
  apply Finset.ext
  intro i
  rw [Finset.mem_filter]
  exact ⟨fun h => (hx' i).mp h.2, fun h => ⟨Finset.mem_univ i, (hx' i).mpr h⟩⟩

/-- The slot set sits inside the occupancy sector of its cardinality. -/
theorem slotSet_subset_sectorSet (B : Set ℝ³) (S : Finset (Fin N)) :
    slotSet B S ⊆ sectorSet B S.card := by
  intro x hx
  rw [mem_sectorSet_iff]
  exact boxOccupancy_eq_card_of_mem_slotSet B hx

/-- **The slot sets are determined by their occupant**: two slot sets containing the same
configuration are equal. -/
theorem slotSet_eq_of_mem {B : Set ℝ³} {S T : Finset (Fin N)} {x : X N}
    (hS : x ∈ slotSet B S) (hT : x ∈ slotSet B T) : S = T := by
  have hS' : ∀ i : Fin N, (x i ∈ B ↔ i ∈ S) := hS
  have hT' : ∀ i : Fin N, (x i ∈ B ↔ i ∈ T) := hT
  ext i
  rw [← hS' i, ← hT' i]

/-- Distinct slot sets are disjoint. -/
theorem slotSet_disjoint {B : Set ℝ³} {S T : Finset (Fin N)} (h : S ≠ T) :
    Disjoint (slotSet B S) (slotSet B T) := by
  rw [Set.disjoint_left]
  intro x hx hy
  exact h (slotSet_eq_of_mem hx hy)

/-- The slot sets cover the configuration space, and their occupant is a function of the
configuration. -/
theorem iUnion_slotSet (B : Set ℝ³) :
    (⋃ S : Finset (Fin N), slotSet B S) = Set.univ := by
  classical
  ext x
  constructor
  · intro _; exact trivial
  · intro _
    refine Set.mem_iUnion.mpr ⟨Finset.univ.filter (fun i : Fin N => x i ∈ B), fun i => ?_⟩
    rw [Finset.mem_filter]
    exact ⟨fun h => ⟨Finset.mem_univ i, h⟩, fun h => h.2⟩

/-- A configuration lies in the occupancy sector `k` exactly when it lies in some slot set of
cardinality `k`. -/
theorem mem_sectorSet_iff_exists_slotSet (B : Set ℝ³) (k : ℕ) (x : X N) :
    x ∈ sectorSet B k ↔ ∃ S ∈ Finset.univ.powersetCard k, x ∈ slotSet B S := by
  classical
  constructor
  · intro hx
    refine ⟨Finset.univ.filter (fun i : Fin N => x i ∈ B), ?_, fun i => ?_⟩
    · rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [← mem_sectorSet_iff B k x |>.mp hx]
      rfl
    · rw [Finset.mem_filter]
      exact ⟨fun h => ⟨Finset.mem_univ i, h⟩, fun h => h.2⟩
  · rintro ⟨S, hS, hxS⟩
    rw [Finset.mem_powersetCard] at hS
    rw [mem_sectorSet_iff]
    rw [boxOccupancy_eq_card_of_mem_slotSet B hxS, hS.2]

/-- **The occupancy sectors are the disjoint unions of the slot sets of their cardinality.** -/
theorem sectorSet_eq_biUnion_slotSet (B : Set ℝ³) (k : ℕ) :
    sectorSet (N := N) B k = ⋃ S ∈ Finset.univ.powersetCard k, slotSet B S := by
  ext x
  rw [mem_sectorSet_iff_exists_slotSet]
  simp only [Set.mem_iUnion, exists_prop]

/-! ## 2. The slot splitting of configurations -/

/-- Splitting a configuration into its slot set's inside coordinates and its outside
coordinates. -/
def slotEquiv (S : Finset (Fin N)) :
    X N ≃ (SlotIn N S → ℝ³) × (SlotOut N S → ℝ³) :=
  Equiv.piEquivPiSubtypeProd (fun i : Fin N => i ∈ S) (fun _ => ℝ³)

/-- Reassembling a configuration from an inside configuration `z` and an outside configuration
`y`. -/
def slotComb (S : Finset (Fin N)) (z : SlotIn N S → ℝ³) (y : SlotOut N S → ℝ³) : X N :=
  (slotEquiv S).symm (z, y)

theorem slotComb_apply (S : Finset (Fin N)) (z : SlotIn N S → ℝ³) (y : SlotOut N S → ℝ³)
    (i : Fin N) :
    slotComb S z y i = if h : i ∈ S then z ⟨i, h⟩ else y ⟨i, h⟩ := by
  simp only [slotComb, slotEquiv, Equiv.piEquivPiSubtypeProd_symm_apply]

theorem slotEquiv_slotComb (S : Finset (Fin N)) (z : SlotIn N S → ℝ³) (y : SlotOut N S → ℝ³) :
    slotEquiv S (slotComb S z y) = (z, y) :=
  (slotEquiv S).apply_symm_apply (z, y)

theorem slotComb_slotEquiv (S : Finset (Fin N)) (x : X N) :
    slotComb S (slotEquiv S x).1 (slotEquiv S x).2 = x :=
  (slotEquiv S).symm_apply_apply x

theorem slotEquiv_apply_fst (S : Finset (Fin N)) (x : X N) (i : SlotIn N S) :
    (slotEquiv S x).1 i = x i := by
  simp only [slotEquiv, Equiv.piEquivPiSubtypeProd_apply]

theorem slotEquiv_apply_snd (S : Finset (Fin N)) (x : X N) (i : SlotOut N S) :
    (slotEquiv S x).2 i = x i := by
  simp only [slotEquiv, Equiv.piEquivPiSubtypeProd_apply]

/-- **The reassembled configuration lies in the slot set exactly when `z` is inside the box and
`y` is outside it.** -/
theorem slotComb_mem_slotSet_iff (B : Set ℝ³) (S : Finset (Fin N))
    (z : SlotIn N S → ℝ³) (y : SlotOut N S → ℝ³) :
    slotComb S z y ∈ slotSet B S ↔ (∀ i : SlotIn N S, z i ∈ B) ∧ (∀ j : SlotOut N S, y j ∉ B) := by
  constructor
  · intro h
    have hh : ∀ i : Fin N, (slotComb S z y i ∈ B ↔ i ∈ S) := h
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have hi := hh i.1
      rw [slotComb_apply, dif_pos i.2] at hi
      exact hi.mpr i.2
    · have hj := hh j.1
      rw [slotComb_apply, dif_neg j.2] at hj
      intro hc
      exact j.2 (hj.mp hc)
  · rintro ⟨hz, hy⟩ i
    rw [slotComb_apply]
    by_cases h : i ∈ S
    · rw [dif_pos h]
      exact ⟨fun _ => h, fun _ => hz ⟨i, h⟩⟩
    · rw [dif_neg h]
      exact ⟨fun hc => absurd hc (hy ⟨i, h⟩), fun hiS => absurd hiS h⟩

/-! ## 3. The slot pieces, the fibre, and the slot masses -/

/-- **The slot piece of a state**: its restriction to the configurations whose box occupancy is
exactly `S`. -/
def slotPiece (B : Set ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ) : X N → ℝ :=
  (slotSet B S).indicator Φ

/-- **The fibre of a state at an outside configuration**: the `k`-particle function on the box
obtained by freezing the coordinates outside `S`. -/
def slotFibre (S : Finset (Fin N)) (Φ : X N → ℝ) (y : SlotOut N S → ℝ³) :
    (SlotIn N S → ℝ³) → ℝ :=
  fun z => Φ (slotComb S z y)

/-- The "all coordinates in `X`" set on a slot type. -/
def slotBox {ι : Type*} (X : Set ℝ³) : Set (ι → ℝ³) := {z | ∀ i, z i ∈ X}

/-- The outside configurations of a slot set at the box `B` inside the corpus box. -/
def slotOutside (L : ℝ) (B : Set ℝ³) (S : Finset (Fin N)) : Set (SlotOut N S → ℝ³) :=
  slotBox (acube L ∩ Bᶜ)

@[simp] theorem mem_slotBox_iff {ι : Type*} {X : Set ℝ³} {z : ι → ℝ³} :
    z ∈ slotBox X ↔ ∀ i, z i ∈ X := Iff.rfl

theorem mem_slotOutside_iff {L : ℝ} {B : Set ℝ³} {S : Finset (Fin N)}
    {y : SlotOut N S → ℝ³} :
    y ∈ slotOutside L B S ↔ (∀ j, y j ∈ acube L) ∧ (∀ j, y j ∉ B) := by
  simp only [slotOutside, slotBox, Set.mem_ofPred_eq, Set.mem_inter_iff]
  exact ⟨fun h => ⟨fun j => (h j).1, fun j => (h j).2⟩, fun h j => ⟨h.1 j, h.2 j⟩⟩

/-! ## 4. The shift sets of the slot-localised projections

The per-slot projections `Q_{B,i}` and the windowed amplitudes `tBamp χ p · i` of a *slot piece*
`slotPiece B S Φ` are supported on the configurations whose slots **other than `i`** agree with the
slot set `S`: replacing slot `i` by a point of `B` (which is what the fibre average/fibre transform
of `Q_{B,i}` does) moves slot `i` into the box, so what the localised object sees is only the
agreement of the *other* slots.  These are the sets that make the slot pieces have disjointly
supported projections, which is the whole content of the slot additivity of the localised word. -/

/-- **The shift set of the box projection `Q_{B,i}` at the slot set `S`**: the configurations
whose slot `i` lies in `B` and whose other slots agree with `S`. -/
def slotShiftSet (B : Set ℝ³) (S : Finset (Fin N)) (i : Fin N) : Set (X N) :=
  {x : X N | i ∈ S ∧ x i ∈ B ∧ ∀ j : Fin N, j ≠ i → (x j ∈ B ↔ j ∈ S)}

/-- **The shift set of the windowed amplitude at the slot set `S`**: the configurations whose
*other* slots agree with `S` (the amplitude's fibre integral replaces slot `i` by a point of the
window, so no condition on `x i` survives). -/
def slotAmpSet (B : Set ℝ³) (S : Finset (Fin N)) (i : Fin N) : Set (X N) :=
  {x : X N | i ∈ S ∧ ∀ j : Fin N, j ≠ i → (x j ∈ B ↔ j ∈ S)}

theorem mem_slotShiftSet_iff (B : Set ℝ³) (S : Finset (Fin N)) (i : Fin N) (x : X N) :
    x ∈ slotShiftSet B S i ↔ i ∈ S ∧ x i ∈ B ∧ ∀ j : Fin N, j ≠ i → (x j ∈ B ↔ j ∈ S) :=
  Iff.rfl

theorem mem_slotAmpSet_iff (B : Set ℝ³) (S : Finset (Fin N)) (i : Fin N) (x : X N) :
    x ∈ slotAmpSet B S i ↔ i ∈ S ∧ ∀ j : Fin N, j ≠ i → (x j ∈ B ↔ j ∈ S) :=
  Iff.rfl

/-- The projection shift set sits inside the amplitude shift set. -/
theorem slotShiftSet_subset_slotAmpSet (B : Set ℝ³) (S : Finset (Fin N)) (i : Fin N) :
    slotShiftSet B S i ⊆ slotAmpSet B S i :=
  fun _ hx => ⟨hx.1, hx.2.2⟩

/-- On its own slot set the slot piece is the state. -/
theorem slotPiece_slotComb (B : Set ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ)
    (z : SlotIn N S → ℝ³) (y : SlotOut N S → ℝ³)
    (hz : ∀ i : SlotIn N S, z i ∈ B) (hy : ∀ j : SlotOut N S, y j ∉ B) :
    slotPiece B S Φ (slotComb S z y) = Φ (slotComb S z y) :=
  Set.indicator_of_mem ((slotComb_mem_slotSet_iff B S z y).mpr ⟨hz, hy⟩) Φ

/-- **The box `L²`-mass of the fibre** at the outside configuration `y`: the `ENNReal`-valued
mass of the `k`-particle function `z ↦ Φ (slotComb S z y)` over the box `slotBox B = B^{S}`.  This
is the object that the fibre decomposition integrates over the outside configurations. -/
noncomputable def slotFibreMass (B : Set ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ)
    (y : SlotOut N S → ℝ³) : ℝ≥0∞ :=
  ∫⁻ z in slotBox B, ENNReal.ofReal ((Φ (slotComb S z y)) ^ 2)

/-- The `ENNReal` slot mass `m_S = ∫⁻_{abox} 1_{slotSet B S}·Φ²`. -/
noncomputable def slotMassENN (L : ℝ) (B : Set ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ) :
    ℝ≥0∞ :=
  ∫⁻ x in abox N L, (slotSet B S).indicator (fun x => ENNReal.ofReal ((Φ x) ^ 2)) x

/-- The slot mass `m_S = ∫_{abox} 1_{slotSet B S}·Φ²`. -/
noncomputable def slotMass (L : ℝ) (B : Set ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ) : ℝ :=
  (slotMassENN L B S Φ).toReal

end Work.PerSector
