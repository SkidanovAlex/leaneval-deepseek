import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.PerSector.Strat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.PerSector

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.PerSector

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

variable {N : ℕ}

/-! ## Helper lemmas for the fibre decomposition

The slot splitting of a configuration is the measurable equivalence
`slotEquiv S : X N ≃ (SlotIn N S → ℝ³) × (SlotOut N S → ℝ³)` of `Defs.lean`, re-packaged here as
its `MeasurableEquiv` version so that it can be used for a change of variables in Lebesgue
integrals.  `slotME S` is (definitionally) `MeasurableEquiv.piEquivPiSubtypeProd`, so
`volume_preserving_piEquivPiSubtypeProd` applies to it; the only mismatch to be bridged is the
`Fintype` instance of `SlotIn N S` (`Finset.Subtype.fintype S` versus the generic
`Subtype.fintype`), and `Fintype` being a `Subsingleton` makes those two instances *equal*. -/

/-- The measurable equivalence underlying the slot splitting (the `MeasurableEquiv` version of
`slotEquiv`). -/
noncomputable def slotME (S : Finset (Fin N)) :
    X N ≃ᵐ (SlotIn N S → ℝ³) × (SlotOut N S → ℝ³) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N => ℝ³) (fun i : Fin N => i ∈ S)

/-- The two `Fintype` instances on the slot types used in this file agree (`Fintype` is a
`Subsingleton`). -/
theorem slotIn_fintype_eq (S : Finset (Fin N)) :
    (Finset.Subtype.fintype S : Fintype (SlotIn N S))
      = Subtype.fintype (fun i : Fin N => i ∈ S) :=
  Subsingleton.elim _ _

/-- The inverse of `slotME` is `slotComb`. -/
theorem slotME_symm_apply (S : Finset (Fin N)) (z : SlotIn N S → ℝ³) (y : SlotOut N S → ℝ³) :
    (slotME S).symm (z, y) = slotComb S z y := by
  simp only [slotME, MeasurableEquiv.piEquivPiSubtypeProd, slotComb, slotEquiv]
  rfl

/-- **`slotME` maps the corpus box to the product of the slot boxes.** -/
theorem slotME_image_abox (S : Finset (Fin N)) (L : ℝ) :
    (slotME S) '' (abox N L) = slotBox (acube L) ×ˢ slotBox (acube L) := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨fun i => hx i.1, fun j => hx j.1⟩
  · rintro ⟨hz, hy⟩
    refine ⟨(slotME S).symm p, ?_, (slotME S).apply_symm_apply p⟩
    intro i
    rw [show (slotME S).symm p = slotComb S p.1 p.2 from by
      obtain ⟨z, y⟩ := p; exact slotME_symm_apply S z y]
    rw [slotComb_apply]
    by_cases h : i ∈ S
    · rw [dif_pos h]; exact hz ⟨i, h⟩
    · rw [dif_neg h]; exact hy ⟨i, h⟩

/-- `slotME` is a left inverse of the reassembling map `slotComb`. -/
theorem slotComb_slotME (S : Finset (Fin N)) (a : X N) :
    slotComb S ((slotME S) a).1 ((slotME S) a).2 = a := by
  have h1 : (slotME S).symm ((slotME S) a) = a := (slotME S).symm_apply_apply a
  rwa [slotME_symm_apply] at h1

/-- The slot box `{z | ∀ i, z i ∈ A}` is measurable for a measurable `A` and a finite index
type. -/
theorem slotBox_measurable {ι : Type*} [Fintype ι] {A : Set ℝ³} (h : MeasurableSet A) :
    MeasurableSet (slotBox (ι := ι) A) := by
  have hset : slotBox (ι := ι) A = ⋂ i, (fun z : ι → ℝ³ => z i) ⁻¹' A := by
    ext z; simp [slotBox]
  rw [hset]
  exact MeasurableSet.iInter (fun i => (measurable_pi_apply i) h)

/-- The slot box of an intersection is the intersection of the slot boxes. -/
theorem slotBox_inter_eq {ι : Type*} (A C : Set ℝ³) :
    slotBox (ι := ι) (A ∩ C) = slotBox A ∩ slotBox C := by
  ext z
  simp only [mem_slotBox_iff, Set.mem_inter_iff]
  exact forall_and

/-- The slot box is monotone in the underlying set. -/
theorem slotBox_mono {ι : Type*} {A C : Set ℝ³} (h : A ⊆ C) :
    slotBox (ι := ι) A ⊆ slotBox (ι := ι) C :=
  fun _ hz i => h (hz i)

/-- **The slot set is the product of the in-box and out-of-box slot boxes**: reassembling `(z, y)`
lands in the slot set of `S` exactly when every coordinate of `z` lies in `B` and every coordinate
of `y` lies outside `B`. -/
theorem mem_slotBox_prod_compl_iff (B : Set ℝ³) (S : Finset (Fin N))
    (z : SlotIn N S → ℝ³) (y : SlotOut N S → ℝ³) :
    (z, y) ∈ slotBox (ι := SlotIn N S) B ×ˢ slotBox (ι := SlotOut N S) Bᶜ
      ↔ slotComb S z y ∈ slotSet B S := by
  rw [Set.mem_prod, mem_slotBox_iff, mem_slotBox_iff, slotComb_mem_slotSet_iff]
  exact Iff.rfl

/-- Restricting an indicator to a measurable set: the integral over `s` of the indicator of `t` is
the integral over `s ∩ t`. -/
theorem setLIntegral_indicator_eq {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {s t : Set α} (ht : MeasurableSet t) (g : α → ℝ≥0∞) :
    ∫⁻ p in s, t.indicator g p ∂μ = ∫⁻ p in s ∩ t, g p ∂μ := by
  rw [show (∫⁻ p in s, t.indicator g p ∂μ)
      = ∫⁻ p, t.indicator g p ∂(μ.restrict s) from rfl]
  rw [lintegral_indicator ht g]
  rw [Measure.restrict_restrict ht, Set.inter_comm]

/-- **The fibre decomposition of a slot mass (Fubini).**  For a box `B` contained in the corpus box
`acube L`, the `abox N L`-mass of the slot piece at `S` equals the integral over the *outside*
configurations `y` (all coordinates outside `B` and inside `acube L`) of the box `L²`-mass, over
`z ∈ B^{S}`, of the fibre `z ↦ Φ (slotComb S z y)`.  This is the Fubini splitting of the
`N`-particle configuration space along the slot set `S`: the in-box coordinates `z` carry the
`k`-particle fibre and the outside coordinates `y` are integrated out. -/
theorem slotMassENN_eq_fibre (L : ℝ) {B : Set ℝ³} (S : Finset (Fin N))
    (hBL : B ⊆ acube L) (hB : MeasurableSet B) {Φ : X N → ℝ} (hΦ : Measurable Φ) :
    slotMassENN L B S Φ
      = ∫⁻ y in slotOutside L B S,
          ∫⁻ z in slotBox B, ENNReal.ofReal ((Φ (slotComb S z y)) ^ 2) := by
  classical
  -- `volume_preserving_piEquivPiSubtypeProd` uses the generic instance `Subtype.fintype` for the
  -- slot types; the statement uses `Finset.Subtype.fintype S`, and `Fintype` is a `Subsingleton`.
  have hinst : (Finset.Subtype.fintype S : Fintype (SlotIn N S)) =
      Subtype.fintype (fun i : Fin N => i ∈ S) := Subsingleton.elim _ _
  have hmp : MeasurePreserving (⇑(slotME S)) (volume : Measure (X N))
      (volume : Measure ((SlotIn N S → ℝ³) × (SlotOut N S → ℝ³))) := by
    rw [hinst]
    exact volume_preserving_piEquivPiSubtypeProd (fun _ : Fin N => ℝ³) (fun i : Fin N => i ∈ S)
  have hGmeas : Measurable (fun p : (SlotIn N S → ℝ³) × (SlotOut N S → ℝ³) =>
      ENNReal.ofReal ((Φ (slotComb S p.1 p.2)) ^ 2)) := by
    refine Measurable.ennreal_ofReal ?_
    refine Measurable.pow_const ?_ 2
    show Measurable (fun p : (SlotIn N S → ℝ³) × (SlotOut N S → ℝ³) => Φ (slotComb S p.1 p.2))
    rw [show (fun p : (SlotIn N S → ℝ³) × (SlotOut N S → ℝ³) => Φ (slotComb S p.1 p.2))
        = fun p => Φ ((slotME S).symm p) from by
      funext p; rw [slotME_symm_apply]]
    exact hΦ.comp (slotME S).symm.measurable
  -- the slot indicator, transported to the product of the slot types
  have hpt : ∀ p : (SlotIn N S → ℝ³) × (SlotOut N S → ℝ³),
      (slotSet B S).indicator (fun x : X N => ENNReal.ofReal ((Φ x) ^ 2)) (slotComb S p.1 p.2)
      = (slotBox (ι := SlotIn N S) B ×ˢ slotBox (ι := SlotOut N S) Bᶜ).indicator
          (fun q : (SlotIn N S → ℝ³) × (SlotOut N S → ℝ³) =>
            ENNReal.ofReal ((Φ (slotComb S q.1 q.2)) ^ 2)) p := by
    intro p
    obtain ⟨z, y⟩ := p
    have key : (z, y) ∈ slotBox (ι := SlotIn N S) B ×ˢ slotBox (ι := SlotOut N S) Bᶜ
        ↔ slotComb S z y ∈ slotSet B S := mem_slotBox_prod_compl_iff B S z y
    by_cases h : (z, y) ∈ slotBox (ι := SlotIn N S) B ×ˢ slotBox (ι := SlotOut N S) Bᶜ
    · rw [Set.indicator_of_mem h]
      show (slotSet B S).indicator (fun x : X N => ENNReal.ofReal ((Φ x) ^ 2)) (slotComb S z y)
        = ENNReal.ofReal ((Φ (slotComb S z y)) ^ 2)
      rw [Set.indicator_of_mem (key.mp h)]
    · rw [Set.indicator_of_notMem h]
      show (slotSet B S).indicator (fun x : X N => ENNReal.ofReal ((Φ x) ^ 2)) (slotComb S z y) = 0
      rw [Set.indicator_of_notMem (fun hc => h (key.mpr hc))]
  -- Step 1: change of variables along the slot splitting
  have h1 : ∫⁻ x in abox N L, (slotSet B S).indicator (fun x : X N => ENNReal.ofReal ((Φ x) ^ 2)) x
      = ∫⁻ p in slotBox (ι := SlotIn N S) (acube L) ×ˢ slotBox (ι := SlotOut N S) (acube L),
          (slotSet B S).indicator (fun x : X N => ENNReal.ofReal ((Φ x) ^ 2))
            (slotComb S p.1 p.2) := by
    have hcv := hmp.setLIntegral_comp_emb (slotME S).measurableEmbedding
      (fun p : (SlotIn N S → ℝ³) × (SlotOut N S → ℝ³) =>
        (slotSet B S).indicator (fun x : X N => ENNReal.ofReal ((Φ x) ^ 2))
          (slotComb S p.1 p.2))
      (abox N L)
    rw [slotME_image_abox (N := N) S L] at hcv
    have hcong : (∫⁻ a in abox N L,
          (slotSet B S).indicator (fun x : X N => ENNReal.ofReal ((Φ x) ^ 2))
            (slotComb S ((slotME S) a).1 ((slotME S) a).2))
        = ∫⁻ a in abox N L,
          (slotSet B S).indicator (fun x : X N => ENNReal.ofReal ((Φ x) ^ 2)) a :=
      lintegral_congr (fun a => by rw [slotComb_slotME S a])
    rw [hcong] at hcv
    exact hcv
  -- Step 2: the indicator of the slot set is the indicator of the in-box/out-of-box product
  have h2 : ∫⁻ p in slotBox (ι := SlotIn N S) (acube L) ×ˢ slotBox (ι := SlotOut N S) (acube L),
          (slotSet B S).indicator (fun x : X N => ENNReal.ofReal ((Φ x) ^ 2)) (slotComb S p.1 p.2)
      = ∫⁻ p in (slotBox (ι := SlotIn N S) (acube L) ×ˢ slotBox (ι := SlotOut N S) (acube L))
            ∩ (slotBox (ι := SlotIn N S) B ×ˢ slotBox (ι := SlotOut N S) Bᶜ),
          ENNReal.ofReal ((Φ (slotComb S p.1 p.2)) ^ 2) := by
    have hcong : (∫⁻ p in slotBox (ι := SlotIn N S) (acube L)
            ×ˢ slotBox (ι := SlotOut N S) (acube L),
          (slotSet B S).indicator (fun x : X N => ENNReal.ofReal ((Φ x) ^ 2)) (slotComb S p.1 p.2))
        = ∫⁻ p in slotBox (ι := SlotIn N S) (acube L) ×ˢ slotBox (ι := SlotOut N S) (acube L),
          (slotBox (ι := SlotIn N S) B ×ˢ slotBox (ι := SlotOut N S) Bᶜ).indicator
            (fun q : (SlotIn N S → ℝ³) × (SlotOut N S → ℝ³) =>
              ENNReal.ofReal ((Φ (slotComb S q.1 q.2)) ^ 2)) p :=
      lintegral_congr hpt
    rw [hcong]
    exact setLIntegral_indicator_eq volume
      ((slotBox_measurable (ι := SlotIn N S) hB).prod
        (slotBox_measurable (ι := SlotOut N S) hB.compl))
      (fun p => ENNReal.ofReal ((Φ (slotComb S p.1 p.2)) ^ 2))
  -- Step 3: the intersection of the two boxes is the box over `B` times the outside box
  have h3 : (slotBox (ι := SlotIn N S) (acube L) ×ˢ slotBox (ι := SlotOut N S) (acube L))
        ∩ (slotBox (ι := SlotIn N S) B ×ˢ slotBox (ι := SlotOut N S) Bᶜ)
      = slotBox (ι := SlotIn N S) B ×ˢ slotOutside L B S := by
    show (slotBox (ι := SlotIn N S) (acube L) ×ˢ slotBox (ι := SlotOut N S) (acube L))
        ∩ (slotBox (ι := SlotIn N S) B ×ˢ slotBox (ι := SlotOut N S) Bᶜ)
      = slotBox (ι := SlotIn N S) B ×ˢ slotBox (ι := SlotOut N S) (acube L ∩ Bᶜ)
    rw [Set.prod_inter_prod]
    congr 1
    · exact Set.inter_eq_right.mpr (slotBox_mono (ι := SlotIn N S) hBL)
    · exact (slotBox_inter_eq (ι := SlotOut N S) (acube L) Bᶜ).symm
  -- Step 4: Tonelli
  have h4 : ∫⁻ p in slotBox (ι := SlotIn N S) B ×ˢ slotOutside L B S,
        ENNReal.ofReal ((Φ (slotComb S p.1 p.2)) ^ 2)
      = ∫⁻ y in slotOutside L B S,
          ∫⁻ z in slotBox B, ENNReal.ofReal ((Φ (slotComb S z y)) ^ 2) := by
    rw [show (volume : Measure ((SlotIn N S → ℝ³) × (SlotOut N S → ℝ³)))
        = (volume : Measure (SlotIn N S → ℝ³)).prod (volume : Measure (SlotOut N S → ℝ³))
        from rfl]
    exact setLIntegral_prod_symm _ hGmeas.aemeasurable.restrict
  rw [slotMassENN, h1, h2, h3, h4]

end Work.PerSector

/-! ## Outer re-export

As in the neighbouring files of this chapter, the declaration proved above sits in the doubly
nested namespace produced by this file's header, so it is re-exported at the chapter's outer
namespace `Work.PerSector`. -/

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

variable {N : ℕ}

/-- **The fibre decomposition of a slot mass (Fubini)**, at the chapter's outer namespace
`Work.PerSector`. -/
theorem slotMassENN_eq_fibre (L : ℝ) {B : Set ℝ³} (S : Finset (Fin N))
    (hBL : B ⊆ acube L) (hB : MeasurableSet B) {Φ : X N → ℝ} (hΦ : Measurable Φ) :
    slotMassENN L B S Φ
      = ∫⁻ y in slotOutside L B S,
          ∫⁻ z in slotBox B, ENNReal.ofReal ((Φ (slotComb S z y)) ^ 2) :=
  Work.PerSector.Work.PerSector.slotMassENN_eq_fibre L S hBL hB hΦ
