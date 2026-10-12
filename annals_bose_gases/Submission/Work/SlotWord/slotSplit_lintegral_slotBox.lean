import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SlotWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.SlotWord.slotSplit_lintegral_slotBox` — the tight slot splitting

The `∫⁻`-level slot splitting of the `N`-particle configuration space used by the fibre
factorisation `Work.SlotWord.WordFibreFactorisation` (PerSector README §6(R1)(a)).

**Statement.**  For a box `B ⊆ acube L`, a slot set `S`, and a measurable `F : X N → ℝ≥0∞` that
*vanishes unless the outside coordinates of `S` are outside `B` and the inside coordinates are
inside `B`*, the `abox N L`-integral of `F` equals the iterated integral over the outside
configurations `y ∈ slotOutside L B S` and the in-box configurations `z ∈ B^{S}` of
`F (slotComb S z y)`.

**Proof.**  Three steps, none of which needs `B` to be measurable (the statement does not assume
it):

1. the change of variables along the measurable equivalence `slotME S : X N ≃ᵐ (SlotIn N S → ℝ³) ×
   (SlotOut N S → ℝ³)`, whose image of `abox N L` is the product of the two boxes over `acube L`;
2. the restriction to the sub-box product `slotBox B × slotOutside L B S`.  This is not an indicator
   argument (which would need `MeasurableSet B`): the auxiliary lemma
   `setLIntegral_eq_setLIntegral_of_eq_zero_off` says that an integral over `s` equals the integral
   over `t ⊆ s` as soon as the integrand vanishes on `s \ t`, and here the support hypotheses
   `hout`, `hin` give exactly this vanishing;
3. Tonelli on the product, in the `y`-outer/`z`-inner order.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SlotWord

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open Work.PerSector

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {N : ℕ}

/-- **An integral over a set is an integral over any subset off which the integrand vanishes.**
If `t ⊆ s` and `g` is zero on `s \ t`, then `∫⁻ x in s, g x = ∫⁻ x in t, g x`.  No measurability of
`t` or of `g` is needed: both sides are suprema over the same simple functions (those `≤ g`), and a
simple function `f ≤ g` can only be non-zero, on `s`, on `t`. -/
theorem setLIntegral_eq_setLIntegral_of_eq_zero_off {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {s t : Set α} (hts : t ⊆ s) {g : α → ℝ≥0∞}
    (hzero : ∀ x ∈ s, x ∉ t → g x = 0) :
    ∫⁻ x in s, g x ∂μ = ∫⁻ x in t, g x ∂μ := by
  have key : ∀ (f : SimpleFunc α ℝ≥0∞) (hf : ⇑f ≤ g),
      SimpleFunc.lintegral f (μ.restrict s) = SimpleFunc.lintegral f (μ.restrict t) := by
    intro f hf
    rw [SimpleFunc.lintegral_restrict f s μ, SimpleFunc.lintegral_restrict f t μ]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hr0 : r = 0
    · rw [hr0, zero_mul, zero_mul]
    · have hset : (⇑f) ⁻¹' {r} ∩ s = (⇑f) ⁻¹' {r} ∩ t := by
        apply Set.Subset.antisymm
        · rintro x ⟨hx, hxs⟩
          refine ⟨hx, ?_⟩
          by_contra hxt
          have hfx : ⇑f x = r := hx
          have hgx : g x = 0 := hzero x hxs hxt
          have hle : r ≤ g x := hfx ▸ (Pi.le_def.mp hf) x
          rw [hgx] at hle
          exact hr0 (le_zero_iff.mp hle)
        · rintro x ⟨hx, hxt⟩
          exact ⟨hx, hts hxt⟩
      rw [hset]
  rw [MeasureTheory.lintegral, MeasureTheory.lintegral]
  exact le_antisymm
    (iSup₂_le fun f hf => le_trans (le_of_eq (key f hf)) (le_iSup₂_of_le f hf le_rfl))
    (iSup₂_le fun f hf => le_trans (le_of_eq (key f hf).symm) (le_iSup₂_of_le f hf le_rfl))

theorem slotSplit_lintegral_slotBox {N : ℕ} (L : ℝ) {B : Set (EuclideanSpace ℝ (Fin 3))}
    (S : Finset (Fin N)) (hBL : B ⊆ Submission.BoseGases.acube L)
    (F : Submission.BoseGases.X N → ENNReal) (hF : Measurable F)
    (hout : ∀ x : Submission.BoseGases.X N, F x ≠ 0 → ∀ j : Work.PerSector.SlotOut N S, x j ∉ B)
    (hin : ∀ x : Submission.BoseGases.X N, F x ≠ 0 → ∀ i : Work.PerSector.SlotIn N S, x i ∈ B) :
    ∫⁻ x in Submission.BoseGases.abox N L, F x
      = ∫⁻ y in Work.PerSector.slotOutside L B S,
          ∫⁻ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) B,
            F (Work.PerSector.slotComb S z y) := by
  classical
  -- the `Fintype` instance of the slot types used by `volume_preserving_piEquivPiSubtypeProd`
  have hinst : (Finset.Subtype.fintype S : Fintype (SlotIn N S)) =
      Subtype.fintype (fun i : Fin N => i ∈ S) := Subsingleton.elim _ _
  have hmp : MeasurePreserving (⇑(Work.PerSector.Work.PerSector.slotME S)) (volume : Measure (X N))
      (volume : Measure ((SlotIn N S → ℝ³) × (SlotOut N S → ℝ³))) := by
    rw [hinst]
    exact volume_preserving_piEquivPiSubtypeProd (fun _ : Fin N => ℝ³) (fun i : Fin N => i ∈ S)
  have hGmeas : Measurable (fun p : (SlotIn N S → ℝ³) × (SlotOut N S → ℝ³) =>
      F (slotComb S p.1 p.2)) :=
    hF.comp (Work.PerSector.Work.PerSector.measurable_slotComb S)
  -- Step 1: change of variables along the slot splitting
  have h1 : ∫⁻ x in abox N L, F x
      = ∫⁻ p in slotBox (ι := SlotIn N S) (acube L) ×ˢ slotBox (ι := SlotOut N S) (acube L),
          F (slotComb S p.1 p.2) := by
    have hcv := hmp.setLIntegral_comp_emb
      (Work.PerSector.Work.PerSector.slotME S).measurableEmbedding
      (fun p : (SlotIn N S → ℝ³) × (SlotOut N S → ℝ³) => F (slotComb S p.1 p.2)) (abox N L)
    rw [Work.PerSector.Work.PerSector.slotME_image_abox (N := N) S L] at hcv
    have hcong : (∫⁻ a in abox N L,
          F (slotComb S ((Work.PerSector.Work.PerSector.slotME S) a).1
            ((Work.PerSector.Work.PerSector.slotME S) a).2))
        = ∫⁻ a in abox N L, F a :=
      lintegral_congr (fun a => by rw [Work.PerSector.Work.PerSector.slotComb_slotME S a])
    rw [hcong] at hcv
    exact hcv
  -- Step 2: the sub-box product, using that the integrand vanishes off it
  have hts : slotBox (ι := SlotIn N S) B ×ˢ slotOutside L B S
      ⊆ slotBox (ι := SlotIn N S) (acube L) ×ˢ slotBox (ι := SlotOut N S) (acube L) :=
    Set.prod_mono (Work.PerSector.Work.PerSector.slotBox_mono hBL)
      (Work.PerSector.Work.PerSector.slotBox_mono Set.inter_subset_left)
  have hzero : ∀ p ∈ slotBox (ι := SlotIn N S) (acube L)
        ×ˢ slotBox (ι := SlotOut N S) (acube L),
      p ∉ slotBox (ι := SlotIn N S) B ×ˢ slotOutside L B S →
        F (slotComb S p.1 p.2) = 0 := by
    rintro ⟨z, y⟩ hp hpt
    rw [Set.mem_prod, mem_slotBox_iff, mem_slotBox_iff] at hp
    obtain ⟨_, hyac⟩ := hp
    by_contra hne
    apply hpt
    rw [Set.mem_prod]
    refine ⟨?_, ?_⟩
    · rw [mem_slotBox_iff]
      intro i
      have hmem := hin (slotComb S z y) hne i
      rwa [slotComb_apply, dif_pos i.2] at hmem
    · rw [mem_slotOutside_iff]
      exact ⟨hyac, fun j => by
        have hmem := hout (slotComb S z y) hne j
        rwa [slotComb_apply, dif_neg j.2] at hmem⟩
  have h2 : ∫⁻ p in slotBox (ι := SlotIn N S) (acube L)
        ×ˢ slotBox (ι := SlotOut N S) (acube L), F (slotComb S p.1 p.2)
      = ∫⁻ p in slotBox (ι := SlotIn N S) B ×ˢ slotOutside L B S,
          F (slotComb S p.1 p.2) :=
    setLIntegral_eq_setLIntegral_of_eq_zero_off volume hts hzero
  -- Step 3: Tonelli in the `y`-outer / `z`-inner order
  have h3 : ∫⁻ p in slotBox (ι := SlotIn N S) B ×ˢ slotOutside L B S,
        F (slotComb S p.1 p.2)
      = ∫⁻ y in slotOutside L B S,
          ∫⁻ z in slotBox (ι := SlotIn N S) B, F (slotComb S z y) := by
    rw [show (volume : Measure ((SlotIn N S → ℝ³) × (SlotOut N S → ℝ³)))
        = (volume : Measure (SlotIn N S → ℝ³)).prod (volume : Measure (SlotOut N S → ℝ³))
        from rfl]
    exact setLIntegral_prod_symm _ hGmeas.aemeasurable
  rw [h1, h2]
  exact h3

end Work.SlotWord
