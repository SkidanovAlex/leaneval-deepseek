import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Sector.fibre_fibState_eq
import Submission.Work.BoseKinLoc.Sector.fsT_box_invariant
import Submission.Work.BoseKinLoc.Sector.integrable_indU_mul_fsT_fibre
import Submission.Work.SlotWord.slotSplit_integral_slotBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Sector.kinForm_fibre_sum` — the sector decomposition of the kinetic word

The `N`-body kinetic word `kinForm N ℓ d s εT b 0 Ψ` (`Work.BoseKinLoc.Defs`) is the sum over the
slots `i` of `slotForm N (fsT ℓ d s εT b 0) ℓ 0 i Ψ`, i.e. of `ℓ⁻³ ∫_x 1_{Λ}(xᵢ)·fsT(fibreᵢ Ψ x)`.
This module proves that it is also the sum, over the *slot sets* `S : Finset (Fin N)` (the sets of
particles lying in the sliding box `Λ = acube ℓ`), of the *box-restricted* kinetic word
`kinFormB S.card ℓ d s εT b` of the fibre state `fibState S Ψ y`, integrated over the outside
configurations `y ∈ slotOutside (max L ℓ) (acube ℓ) S`.

The proof has three layers:

* **the partition of each slot integral** into the slot sets (`Work.PerSector.sum_indicator_slotSet`
  together with `MeasureTheory.integral_finsetSum`, the integrability being supplied by
  `Work.BoseKinLoc.Sector.integrable_indU_mul_fsT_Tibre`), and the pointwise vanishing of the
  `i`-th slot integrand off its slot set (the indicator `indU ℓ 0` is the indicator of `acube ℓ`);
* **the slot splitting of the box integral** `Work.SlotWord.slotSplit_integral_slotBox`
  (`∫_{abox N L} f = ∫_{slotOutside L B S} ∫_{slotBox B} f (slotComb S z y)` for an `f` vanishing
  off the slot set), followed by the re-indexing of the in-box slot box onto `abox S.card ℓ` along
  the order isomorphism `slotIso S` (`slotIsoME`, measure preserving by
  `volume_measurePreserving_piCongrLeft`);
* **the fibre identity** `Work.BoseKinLoc.Sector.fibre_fibState_eq` (the `i`-th fibre of the fibre
  state is the `i.1`-th fibre of `Ψ`) and the per-configuration sum
  `∫_{abox m ℓ} Σ_k (…) = Σ_k ∫_{abox m ℓ} (…)` at the `|S|`-particle box.

The statement is an identity (both sides are sums of honest, integrable integrals), so no junk
values are involved.
-/

noncomputable section

noncomputable section

open MeasureTheory

namespace Work.BoseKinLoc.Sector

open Submission.BoseGases

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

variable {N : ℕ}

/-! ## 1. Elementary helpers -/

theorem acube_subset_of_le {a c : ℝ} (h : a ≤ c) :
    Submission.BoseGases.acube a ⊆ Submission.BoseGases.acube c := by
  intro x hx
  rw [Submission.BoseGases.mem_acube_iff] at hx ⊢
  intro m
  have hm := hx m
  rw [Set.mem_Icc] at hm ⊢
  exact ⟨by linarith [hm.1, h], by linarith [hm.2, h]⟩

theorem abox_subset_of_le {n : ℕ} {a c : ℝ} (h : a ≤ c) :
    Submission.BoseGases.abox n a ⊆ Submission.BoseGases.abox n c :=
  fun x hx i => acube_subset_of_le h (hx i)

theorem lamBox_zero (ℓ : ℝ) : Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
  ext x
  simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]

theorem indU_zero (ℓ : ℝ) :
    Work.BoseKinLoc.indU ℓ 0 = (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) := by
  ext x
  simp only [Work.BoseKinLoc.indU, lamBox_zero]

theorem indU_zero_of_notMem {ℓ : ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∉ Submission.BoseGases.acube ℓ) : Work.BoseKinLoc.indU ℓ 0 x = 0 := by
  rw [indU_zero]
  exact Set.indicator_of_notMem hx _

theorem measurableSet_slotBox (ℓ : ℝ) (S : Finset (Fin N)) :
    MeasurableSet (Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S)
      (Submission.BoseGases.acube ℓ)) :=
  Work.PerSector.Work.PerSector.slotBox_measurable (Submission.BoseGases.acube_measurable ℓ)

theorem measurableSet_slotOutside (ℓ L : ℝ) (S : Finset (Fin N)) :
    MeasurableSet (Work.PerSector.slotOutside L (Submission.BoseGases.acube ℓ) S) :=
  Work.PerSector.Work.PerSector.slotBox_measurable
    ((Submission.BoseGases.acube_measurable L).inter
      (Submission.BoseGases.acube_measurable ℓ).compl)

/-! ## 2. The per-slot kinetic integrand -/

/-- The `i`-th slot integrand of the kinetic word. -/
noncomputable def slotKin (ℓ d s εT b : ℝ) (N : ℕ) (Ψ : Submission.BoseGases.X N → ℝ)
    (i : Fin N) : Submission.BoseGases.X N → ℝ :=
  fun x => Work.BoseKinLoc.indU ℓ 0 (x i)
    * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre N i Ψ x)

/-- The slot integrand vanishes off the configuration box of side `max L ℓ`. -/
theorem slotKin_eq_zero_of_notMem_abox {ℓ L L' d s εT b : ℝ} (hℓ : 0 < ℓ)
    (hLL' : L ≤ L') (hℓL' : ℓ ≤ L')
    {Ψ : Submission.BoseGases.X N → ℝ} (hsupp : tsupport Ψ ⊆ Submission.BoseGases.abox N L)
    {x : Submission.BoseGases.X N} (hx : x ∉ Submission.BoseGases.abox N L') (i : Fin N) :
    slotKin ℓ d s εT b N Ψ i x = 0 := by
  by_cases hi : x i ∈ Submission.BoseGases.acube ℓ
  · obtain ⟨m, hm⟩ : ∃ m : Fin N, x m ∉ Submission.BoseGases.acube L' := by
      by_contra h
      exact hx fun m => not_not.mp (not_exists.mp h m)
    have hmi : m ≠ i := fun h => hm (h ▸ acube_subset_of_le hℓL' hi)
    have hmL : x m ∉ Submission.BoseGases.acube L := fun hc => hm (acube_subset_of_le hLL' hc)
    rw [slotKin, Work.BoseKinLoc.Word.fibre_eq_zero_of_slot_not_mem hsupp hmi hmL,
      Work.BoseKinLoc.Word.fsT_zero hℓ, mul_zero]
  · rw [slotKin, indU_zero_of_notMem hi, zero_mul]

/-! ## 3. The re-indexing of the in-box slot box -/

/-- The re-indexing `ζ ↦ (fun i : SlotIn N S => ζ (slotIso S i))`. -/
noncomputable def slotIsoME (S : Finset (Fin N)) :
    (Fin S.card → EuclideanSpace ℝ (Fin 3)) ≃ᵐ
      (Work.PerSector.SlotIn N S → EuclideanSpace ℝ (Fin 3)) :=
  MeasurableEquiv.piCongrLeft (fun _ : Work.PerSector.SlotIn N S => EuclideanSpace ℝ (Fin 3))
    (slotIso S).symm

theorem slotIsoME_apply (S : Finset (Fin N)) (x : Fin S.card → EuclideanSpace ℝ (Fin 3))
    (i : Work.PerSector.SlotIn N S) : slotIsoME S x i = x (slotIso S i) := by
  have h1 := Equiv.piCongrLeft_apply_apply (P := fun _ : Work.PerSector.SlotIn N S =>
    EuclideanSpace ℝ (Fin 3)) (e := (slotIso S).symm) x ((slotIso S) i)
  rwa [Equiv.symm_apply_apply] at h1

theorem measurePreserving_slotIsoME (S : Finset (Fin N)) :
    MeasurePreserving (slotIsoME S) volume volume :=
  volume_measurePreserving_piCongrLeft _ (slotIso S).symm

theorem slotIsoME_image_abox (S : Finset (Fin N)) (ℓ : ℝ) :
    slotIsoME S '' (Submission.BoseGases.abox S.card ℓ) =
      Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) (Submission.BoseGases.acube ℓ) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    rw [slotIsoME_apply]
    exact hx (slotIso S i)
  · intro hz
    refine ⟨fun j : Fin S.card => z ((slotIso S).symm j), fun j => hz _, ?_⟩
    funext i
    rw [slotIsoME_apply]
    simp

theorem slotIsoME_comp (S : Finset (Fin N)) (ζ : Fin S.card → EuclideanSpace ℝ (Fin 3)) :
    (fun m : Fin S.card => slotIsoME S ζ ((slotIso S).symm m)) = ζ := by
  funext m
  rw [slotIsoME_apply, Equiv.apply_symm_apply]

theorem sum_attach_slotIso (S : Finset (Fin N)) (f : Work.PerSector.SlotIn N S → ℝ) :
    (∑ i ∈ S.attach, f i) = ∑ k : Fin S.card, f ((slotIso S).symm k) := by
  rw [← Finset.univ_eq_attach S]
  exact Fintype.sum_equiv (slotIso S) f (fun k => f ((slotIso S).symm k)) (fun i => by simp)

/-! ## 4. The support of the fibre state -/

theorem tsupport_fibState_subset_abox {L' : ℝ} (S : Finset (Fin N))
    {Ψ : Submission.BoseGases.X N → ℝ} (hsupp : tsupport Ψ ⊆ Submission.BoseGases.abox N L')
    (y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)) :
    tsupport (fibState S Ψ y) ⊆ Submission.BoseGases.abox S.card L' := by
  refine (IsClosed.closure_subset_iff (Submission.BoseGases.abox_isClosed S.card L')).mpr ?_
  intro x hx
  rw [Function.mem_support] at hx
  rw [Submission.BoseGases.mem_abox_iff]
  intro j
  have hne : Ψ (Work.PerSector.slotComb S (fun i : Work.PerSector.SlotIn N S => x (slotIso S i)) y)
      ≠ 0 := by
    rw [← fibState_apply S Ψ y x]
    exact hx
  have hmem : Work.PerSector.slotComb S (fun i : Work.PerSector.SlotIn N S => x (slotIso S i)) y
      ∈ tsupport Ψ :=
    subset_tsupport Ψ (Function.mem_support.mpr hne)
  have hbox := hsupp hmem
  rw [Submission.BoseGases.mem_abox_iff] at hbox
  obtain ⟨i, hi⟩ := (slotIso S).surjective j
  have hb := hbox i.1
  rw [Work.PerSector.slotComb_apply, dif_pos i.2] at hb
  simpa [hi] using hb

/-! ## 5. The sum through the box integral -/

theorem setIntegral_sum_fibre {m : ℕ} {ℓ d s εT b : ℝ}
    {Φ : Submission.BoseGases.X m → ℝ}
    (hBox : ∀ k : Fin m, MeasureTheory.IntegrableOn (fun x' : Submission.BoseGases.X m =>
      Work.BoseKinLoc.indU ℓ 0 (x' k) * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre m k Φ x'))
      (Submission.BoseGases.abox m ℓ)) :
    (∫ x' in Submission.BoseGases.abox m ℓ, ∑ k : Fin m,
        Work.BoseKinLoc.indU ℓ 0 (x' k)
          * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre m k Φ x'))
      = ∑ k : Fin m, ∫ x' in Submission.BoseGases.abox m ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x' k)
            * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre m k Φ x') := by
  have h := MeasureTheory.integral_finsetSum Finset.univ
    (μ := volume.restrict (Submission.BoseGases.abox m ℓ))
    (f := fun k (x' : Submission.BoseGases.X m) =>
      Work.BoseKinLoc.indU ℓ 0 (x' k)
        * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre m k Φ x'))
    (fun k _ => hBox k)
  simpa using h

/-! ## 6. The conditional main lemma -/

theorem kinForm_fibre_sum_of {ℓ L d s εT b : ℝ} (hℓ : 0 < ℓ)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (hsupp : tsupport Ψ ⊆ Submission.BoseGases.abox N L)
    (hInt : ∀ i : Fin N, MeasureTheory.Integrable (slotKin ℓ d s εT b N Ψ i))
    (hBox : ∀ ⦃m : ℕ⦄ ⦃Φ : Submission.BoseGases.X m → ℝ⦄, ContDiff ℝ (⊤ : ENat) Φ →
      tsupport Φ ⊆ Submission.BoseGases.abox m (max L ℓ) → ∀ k : Fin m,
      MeasureTheory.IntegrableOn (fun x' : Submission.BoseGases.X m =>
        Work.BoseKinLoc.indU ℓ 0 (x' k)
          * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre m k Φ x'))
        (Submission.BoseGases.abox m ℓ)) :
    (∑ S : Finset (Fin N), ∫ y in Work.PerSector.slotOutside (max L ℓ) (Submission.BoseGases.acube ℓ) S,
        Work.BoseKinLoc.kinFormB S.card ℓ d s εT b (fibState S Ψ y))
      = Work.BoseKinLoc.kinForm N ℓ d s εT b 0 Ψ := by
  classical
  have hRHS : Work.BoseKinLoc.kinForm N ℓ d s εT b 0 Ψ
      = ∑ i : Fin N, ℓ ^ (-3 : ℤ) * ∫ x : Submission.BoseGases.X N, slotKin ℓ d s εT b N Ψ i x := by
    simp only [Work.BoseKinLoc.kinForm, Work.BoseKinLoc.slotForm, slotKin]
  rw [hRHS]
  have hzero : ∀ (S : Finset (Fin N)) (i : Fin N), i ∉ S →
      (∫ x in Work.PerSector.slotSet (Submission.BoseGases.acube ℓ) S,
        slotKin ℓ d s εT b N Ψ i x) = 0 := by
    intro S i hi
    refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (fun x hx => ?_)
    have hxi : x i ∉ Submission.BoseGases.acube ℓ := fun hc =>
      hi (((Work.PerSector.mem_slotSet_iff (Submission.BoseGases.acube ℓ) S x).mp hx i).mp hc)
    rw [slotKin, indU_zero_of_notMem hxi, zero_mul]
  have hpart : ∀ i : Fin N, (∫ x : Submission.BoseGases.X N, slotKin ℓ d s εT b N Ψ i x)
      = ∑ S : Finset (Fin N), ∫ x in Work.PerSector.slotSet (Submission.BoseGases.acube ℓ) S,
          slotKin ℓ d s εT b N Ψ i x := by
    intro i
    have h1 : (∫ x : Submission.BoseGases.X N, slotKin ℓ d s εT b N Ψ i x)
        = ∫ x : Submission.BoseGases.X N, ∑ S : Finset (Fin N),
            (Work.PerSector.slotSet (Submission.BoseGases.acube ℓ) S).indicator
              (slotKin ℓ d s εT b N Ψ i) x := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      exact (Work.PerSector.sum_indicator_slotSet (Submission.BoseGases.acube ℓ)
        (slotKin ℓ d s εT b N Ψ i) x).symm
    rw [h1, MeasureTheory.integral_finsetSum Finset.univ (fun S _ => (hInt i).indicator
      (Work.PerSector.slotSet_measurable (Submission.BoseGases.acube ℓ)
        (Submission.BoseGases.acube_measurable ℓ) S))]
    exact Finset.sum_congr rfl (fun S _ => MeasureTheory.integral_indicator
      (Work.PerSector.slotSet_measurable (Submission.BoseGases.acube ℓ)
        (Submission.BoseGases.acube_measurable ℓ) S))
  rw [Finset.sum_congr rfl (fun i _ => congrArg (fun t => ℓ ^ (-3 : ℤ) * t) (hpart i))]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  -- the per-slot-set identity
  have key : ∀ S : Finset (Fin N),
      (∑ i ∈ S.attach, ℓ ^ (-3 : ℤ) * ∫ x in Work.PerSector.slotSet (Submission.BoseGases.acube ℓ) S,
          slotKin ℓ d s εT b N Ψ i.1 x)
        = ∫ y in Work.PerSector.slotOutside (max L ℓ) (Submission.BoseGases.acube ℓ) S,
            Work.BoseKinLoc.kinFormB S.card ℓ d s εT b (fibState S Ψ y) := by
    intro S
    have hBL' : Submission.BoseGases.acube ℓ ⊆ Submission.BoseGases.acube (max L ℓ) :=
      acube_subset_of_le (le_max_right L ℓ)
    have hLL' : L ≤ max L ℓ := le_max_left L ℓ
    have hℓL' : ℓ ≤ max L ℓ := le_max_right L ℓ
    have hsupp' : tsupport Ψ ⊆ Submission.BoseGases.abox N (max L ℓ) :=
      fun x hx => abox_subset_of_le hLL' (hsupp hx)
    have hs : MeasurableSet (Work.PerSector.slotSet (Submission.BoseGases.acube ℓ) S) :=
      Work.PerSector.slotSet_measurable _ (Submission.BoseGases.acube_measurable ℓ) S
    have hsum_int : MeasureTheory.Integrable
        (fun x : Submission.BoseGases.X N => ∑ i ∈ S.attach, slotKin ℓ d s εT b N Ψ i.1 x) :=
      MeasureTheory.integrable_finsetSum S.attach (fun i _ => hInt i.1)
    have hsum_meas : MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X N => ∑ i ∈ S.attach, slotKin ℓ d s εT b N Ψ i.1 x)
        volume := hsum_int.aestronglyMeasurable
    -- (2) the sum of the set integrals is the set integral of the sum
    have h2 : (∑ i ∈ S.attach, ∫ x in Work.PerSector.slotSet (Submission.BoseGases.acube ℓ) S,
          slotKin ℓ d s εT b N Ψ i.1 x)
        = ∫ x in Work.PerSector.slotSet (Submission.BoseGases.acube ℓ) S,
            ∑ i ∈ S.attach, slotKin ℓ d s εT b N Ψ i.1 x := by
      have h := MeasureTheory.integral_finsetSum S.attach
        (μ := volume.restrict (Work.PerSector.slotSet (Submission.BoseGases.acube ℓ) S))
        (f := fun i (x : Submission.BoseGases.X N) => slotKin ℓ d s εT b N Ψ i.1 x)
        (fun i _ => (hInt i.1).integrableOn)
      simpa using h.symm
    -- (3) the support reduction to the configuration box
    have h3 : (∫ x in Work.PerSector.slotSet (Submission.BoseGases.acube ℓ) S,
            ∑ i ∈ S.attach, slotKin ℓ d s εT b N Ψ i.1 x)
        = ∫ x in Submission.BoseGases.abox N (max L ℓ),
            (Work.PerSector.slotSet (Submission.BoseGases.acube ℓ) S).indicator
              (fun x => ∑ i ∈ S.attach, slotKin ℓ d s εT b N Ψ i.1 x) x := by
      rw [MeasureTheory.setIntegral_indicator hs]
      rw [Set.inter_comm]
      refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hs
        Set.inter_subset_left ?_
      intro x hx
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have hxab : x ∉ Submission.BoseGases.abox N (max L ℓ) := fun h => hx.2 ⟨hx.1, h⟩
      obtain ⟨m, hm⟩ : ∃ m : Fin N, x m ∉ Submission.BoseGases.acube (max L ℓ) := by
        by_contra h
        exact hxab fun m => not_not.mp (not_exists.mp h m)
      have hmi : m ≠ i.1 := fun h => hm (h ▸ acube_subset_of_le hℓL'
        (((Work.PerSector.mem_slotSet_iff (Submission.BoseGases.acube ℓ) S x).mp hx.1 i.1).mpr i.2))
      have hmL : x m ∉ Submission.BoseGases.acube L := fun hc => hm (acube_subset_of_le hLL' hc)
      rw [slotKin, Work.BoseKinLoc.Word.fibre_eq_zero_of_slot_not_mem hsupp hmi hmL,
        Work.BoseKinLoc.Word.fsT_zero hℓ, mul_zero]
    -- (4) the slot splitting of the box integral
    have hsplitF : MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X N =>
          (Work.PerSector.slotSet (Submission.BoseGases.acube ℓ) S).indicator
            (fun x => ∑ i ∈ S.attach, slotKin ℓ d s εT b N Ψ i.1 x) x)
        (volume.restrict (Submission.BoseGases.abox N (max L ℓ))) :=
      (hsum_meas.indicator hs).restrict
    have hsplitI : MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X N =>
          (Work.PerSector.slotSet (Submission.BoseGases.acube ℓ) S).indicator
            (fun x => ∑ i ∈ S.attach, slotKin ℓ d s εT b N Ψ i.1 x) x)
        (Submission.BoseGases.abox N (max L ℓ)) :=
      (hsum_int.indicator hs).integrableOn
    have h4 : (∫ x in Submission.BoseGases.abox N (max L ℓ),
            (Work.PerSector.slotSet (Submission.BoseGases.acube ℓ) S).indicator
              (fun x => ∑ i ∈ S.attach, slotKin ℓ d s εT b N Ψ i.1 x) x)
        = ∫ y in Work.PerSector.slotOutside (max L ℓ) (Submission.BoseGases.acube ℓ) S,
            ∫ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S)
                (Submission.BoseGases.acube ℓ),
              (Work.PerSector.slotSet (Submission.BoseGases.acube ℓ) S).indicator
                (fun x => ∑ i ∈ S.attach, slotKin ℓ d s εT b N Ψ i.1 x)
                (Work.PerSector.slotComb S z y) :=
      Work.SlotWord.slotSplit_integral_slotBox (N := N) (max L ℓ) S hBL' hsplitF hsplitI
        (fun x hx j => by
          have hxS : x ∈ Work.PerSector.slotSet (Submission.BoseGases.acube ℓ) S := by
            by_contra hxS
            rw [Set.indicator_of_notMem hxS] at hx
            exact hx rfl
          exact fun hc =>
            j.2 (((Work.PerSector.mem_slotSet_iff (Submission.BoseGases.acube ℓ) S x).mp hxS j.1).mp hc))
        (fun x hx i => by
          have hxS : x ∈ Work.PerSector.slotSet (Submission.BoseGases.acube ℓ) S := by
            by_contra hxS
            rw [Set.indicator_of_notMem hxS] at hx
            exact hx rfl
          exact ((Work.PerSector.mem_slotSet_iff (Submission.BoseGases.acube ℓ) S x).mp hxS i.1).mpr i.2)
    have hzz : ℓ ^ (3 : ℤ) * ℓ ^ (-3 : ℤ) = 1 := by
      rw [← zpow_add₀ (ne_of_gt hℓ), show (3 : ℤ) + (-3) = 0 by norm_num, zpow_zero]
    have hzz' : ℓ ^ (-3 : ℤ) * ℓ ^ (3 : ℤ) = 1 := by rw [mul_comm, hzz]
    -- (5) the pointwise identification of the indicator with the slot sum
    have h5 : (∫ y in Work.PerSector.slotOutside (max L ℓ) (Submission.BoseGases.acube ℓ) S,
          ∫ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S)
              (Submission.BoseGases.acube ℓ),
            (Work.PerSector.slotSet (Submission.BoseGases.acube ℓ) S).indicator
              (fun x => ∑ i ∈ S.attach, slotKin ℓ d s εT b N Ψ i.1 x)
              (Work.PerSector.slotComb S z y))
        = ∫ y in Work.PerSector.slotOutside (max L ℓ) (Submission.BoseGases.acube ℓ) S,
            ∫ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S)
                (Submission.BoseGases.acube ℓ),
              ∑ i ∈ S.attach, Work.BoseKinLoc.indU ℓ 0 (z i)
                * Work.BoseKinLoc.fsT ℓ d s εT b 0
                    (Work.BoseKinLoc.fibre N i.1 Ψ (Work.PerSector.slotComb S z y)) := by
      refine MeasureTheory.setIntegral_congr_ae (measurableSet_slotOutside ℓ (max L ℓ) S)
        (Filter.Eventually.of_forall (fun y hy => ?_))
      refine MeasureTheory.setIntegral_congr_fun (measurableSet_slotBox ℓ S) (fun z hz => ?_)
      have hmem : Work.PerSector.slotComb S z y
          ∈ Work.PerSector.slotSet (Submission.BoseGases.acube ℓ) S := by
        rw [Work.PerSector.slotComb_mem_slotSet_iff]
        exact ⟨fun i => hz i, fun j => (Work.PerSector.mem_slotOutside_iff.mp hy).2 j⟩
      rw [Set.indicator_of_mem hmem]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [slotKin, Work.PerSector.slotComb_apply, dif_pos i.2]
    -- (6) the re-indexing of the in-box integral
    have h6 : (∫ y in Work.PerSector.slotOutside (max L ℓ) (Submission.BoseGases.acube ℓ) S,
          ∫ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S)
              (Submission.BoseGases.acube ℓ),
            ∑ i ∈ S.attach, Work.BoseKinLoc.indU ℓ 0 (z i)
              * Work.BoseKinLoc.fsT ℓ d s εT b 0
                  (Work.BoseKinLoc.fibre N i.1 Ψ (Work.PerSector.slotComb S z y)))
        = ∫ y in Work.PerSector.slotOutside (max L ℓ) (Submission.BoseGases.acube ℓ) S,
            ∫ ζ in Submission.BoseGases.abox S.card ℓ,
              ∑ i ∈ S.attach, Work.BoseKinLoc.indU ℓ 0 ((slotIsoME S ζ) i)
                * Work.BoseKinLoc.fsT ℓ d s εT b 0
                    (Work.BoseKinLoc.fibre N i.1 Ψ
                      (Work.PerSector.slotComb S (slotIsoME S ζ) y)) := by
      refine MeasureTheory.setIntegral_congr_ae (measurableSet_slotOutside ℓ (max L ℓ) S)
        (Filter.Eventually.of_forall (fun y hy => ?_))
      rw [← slotIsoME_image_abox S ℓ]
      exact (measurePreserving_slotIsoME S).setIntegral_image_emb (slotIsoME S).measurableEmbedding
        (fun z => ∑ i ∈ S.attach, Work.BoseKinLoc.indU ℓ 0 (z i)
          * Work.BoseKinLoc.fsT ℓ d s εT b 0
              (Work.BoseKinLoc.fibre N i.1 Ψ (Work.PerSector.slotComb S z y)))
        (Submission.BoseGases.abox S.card ℓ)
    -- (7) the re-indexing acts as `slotIsoME_apply`
    have h7 : (∫ y in Work.PerSector.slotOutside (max L ℓ) (Submission.BoseGases.acube ℓ) S,
          ∫ ζ in Submission.BoseGases.abox S.card ℓ,
            ∑ i ∈ S.attach, Work.BoseKinLoc.indU ℓ 0 ((slotIsoME S ζ) i)
              * Work.BoseKinLoc.fsT ℓ d s εT b 0
                  (Work.BoseKinLoc.fibre N i.1 Ψ
                    (Work.PerSector.slotComb S (slotIsoME S ζ) y)))
        = ∫ y in Work.PerSector.slotOutside (max L ℓ) (Submission.BoseGases.acube ℓ) S,
            ∫ ζ in Submission.BoseGases.abox S.card ℓ,
              ∑ i ∈ S.attach, Work.BoseKinLoc.indU ℓ 0 (ζ (slotIso S i))
                * Work.BoseKinLoc.fsT ℓ d s εT b 0
                    (Work.BoseKinLoc.fibre N i.1 Ψ
                      (Work.PerSector.slotComb S (slotIsoME S ζ) y)) := by
      refine MeasureTheory.setIntegral_congr_ae (measurableSet_slotOutside ℓ (max L ℓ) S)
        (Filter.Eventually.of_forall (fun y hy => ?_))
      refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable S.card ℓ)
        (fun ζ hζ => ?_)
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [slotIsoME_apply]
    -- (8) the fibre identity
    have h8 : (∫ y in Work.PerSector.slotOutside (max L ℓ) (Submission.BoseGases.acube ℓ) S,
          ∫ ζ in Submission.BoseGases.abox S.card ℓ,
            ∑ i ∈ S.attach, Work.BoseKinLoc.indU ℓ 0 (ζ (slotIso S i))
              * Work.BoseKinLoc.fsT ℓ d s εT b 0
                  (Work.BoseKinLoc.fibre N i.1 Ψ
                    (Work.PerSector.slotComb S (slotIsoME S ζ) y)))
        = ∫ y in Work.PerSector.slotOutside (max L ℓ) (Submission.BoseGases.acube ℓ) S,
            ∫ ζ in Submission.BoseGases.abox S.card ℓ,
              ∑ i ∈ S.attach, Work.BoseKinLoc.indU ℓ 0 (ζ (slotIso S i))
                * Work.BoseKinLoc.fsT ℓ d s εT b 0
                    (Work.BoseKinLoc.fibre S.card (slotIso S i) (fibState S Ψ y) ζ) := by
      refine MeasureTheory.setIntegral_congr_ae (measurableSet_slotOutside ℓ (max L ℓ) S)
        (Filter.Eventually.of_forall (fun y hy => ?_))
      refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable S.card ℓ)
        (fun ζ hζ => ?_)
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Work.BoseKinLoc.Sector.fibre_fibState_eq S i Ψ y (slotIsoME S ζ), slotIsoME_comp S ζ]
    -- (9) the re-indexing of the finite sum
    have h9 : (∫ y in Work.PerSector.slotOutside (max L ℓ) (Submission.BoseGases.acube ℓ) S,
          ∫ ζ in Submission.BoseGases.abox S.card ℓ,
            ∑ i ∈ S.attach, Work.BoseKinLoc.indU ℓ 0 (ζ (slotIso S i))
              * Work.BoseKinLoc.fsT ℓ d s εT b 0
                  (Work.BoseKinLoc.fibre S.card (slotIso S i) (fibState S Ψ y) ζ))
        = ∫ y in Work.PerSector.slotOutside (max L ℓ) (Submission.BoseGases.acube ℓ) S,
            ∫ ζ in Submission.BoseGases.abox S.card ℓ,
              ∑ k : Fin S.card, Work.BoseKinLoc.indU ℓ 0 (ζ k)
                * Work.BoseKinLoc.fsT ℓ d s εT b 0
                    (Work.BoseKinLoc.fibre S.card k (fibState S Ψ y) ζ) := by
      refine MeasureTheory.setIntegral_congr_ae (measurableSet_slotOutside ℓ (max L ℓ) S)
        (Filter.Eventually.of_forall (fun y hy => ?_))
      refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable S.card ℓ)
        (fun ζ hζ => ?_)
      rw [sum_attach_slotIso S (fun i => Work.BoseKinLoc.indU ℓ 0 (ζ (slotIso S i))
        * Work.BoseKinLoc.fsT ℓ d s εT b 0
            (Work.BoseKinLoc.fibre S.card (slotIso S i) (fibState S Ψ y) ζ))]
      simp only [Equiv.apply_symm_apply]
    -- (10) the sum through the box integral, for each outside configuration
    have h10 : ∀ y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3),
        (∫ ζ in Submission.BoseGases.abox S.card ℓ,
            ∑ k : Fin S.card, Work.BoseKinLoc.indU ℓ 0 (ζ k)
              * Work.BoseKinLoc.fsT ℓ d s εT b 0
                  (Work.BoseKinLoc.fibre S.card k (fibState S Ψ y) ζ))
          = ∑ k : Fin S.card, ∫ ζ in Submission.BoseGases.abox S.card ℓ,
              Work.BoseKinLoc.indU ℓ 0 (ζ k)
                * Work.BoseKinLoc.fsT ℓ d s εT b 0
                    (Work.BoseKinLoc.fibre S.card k (fibState S Ψ y) ζ) := by
      intro y
      exact setIntegral_sum_fibre (Φ := fibState S Ψ y)
        (hBox (contDiff_fibState S hΨ y) (tsupport_fibState_subset_abox S hsupp' y))
    -- (11) the identification with the box-restricted word
    have h11 : ∀ y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3),
        (∑ k : Fin S.card, ∫ ζ in Submission.BoseGases.abox S.card ℓ,
            Work.BoseKinLoc.indU ℓ 0 (ζ k)
              * Work.BoseKinLoc.fsT ℓ d s εT b 0
                  (Work.BoseKinLoc.fibre S.card k (fibState S Ψ y) ζ))
          = ℓ ^ (3 : ℤ) * Work.BoseKinLoc.kinFormB S.card ℓ d s εT b (fibState S Ψ y) := by
      intro y
      simp only [Work.BoseKinLoc.kinFormB]
      rw [← mul_assoc, hzz, one_mul]
    calc (∑ i ∈ S.attach, ℓ ^ (-3 : ℤ)
            * ∫ x in Work.PerSector.slotSet (Submission.BoseGases.acube ℓ) S,
                slotKin ℓ d s εT b N Ψ i.1 x)
        = ℓ ^ (-3 : ℤ) * ∑ i ∈ S.attach,
            ∫ x in Work.PerSector.slotSet (Submission.BoseGases.acube ℓ) S,
              slotKin ℓ d s εT b N Ψ i.1 x := (Finset.mul_sum S.attach _ _).symm
      _ = ℓ ^ (-3 : ℤ) * (∫ x in Work.PerSector.slotSet (Submission.BoseGases.acube ℓ) S,
            ∑ i ∈ S.attach, slotKin ℓ d s εT b N Ψ i.1 x) := by rw [h2]
      _ = ℓ ^ (-3 : ℤ) * (∫ x in Submission.BoseGases.abox N (max L ℓ),
            (Work.PerSector.slotSet (Submission.BoseGases.acube ℓ) S).indicator
              (fun x => ∑ i ∈ S.attach, slotKin ℓ d s εT b N Ψ i.1 x) x) := by rw [h3]
      _ = ℓ ^ (-3 : ℤ) * (∫ y in Work.PerSector.slotOutside (max L ℓ)
              (Submission.BoseGases.acube ℓ) S,
            ∫ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S)
                (Submission.BoseGases.acube ℓ),
              (Work.PerSector.slotSet (Submission.BoseGases.acube ℓ) S).indicator
                (fun x => ∑ i ∈ S.attach, slotKin ℓ d s εT b N Ψ i.1 x)
                (Work.PerSector.slotComb S z y)) := by rw [h4]
      _ = ℓ ^ (-3 : ℤ) * (∫ y in Work.PerSector.slotOutside (max L ℓ)
              (Submission.BoseGases.acube ℓ) S,
            ∫ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S)
                (Submission.BoseGases.acube ℓ),
              ∑ i ∈ S.attach, Work.BoseKinLoc.indU ℓ 0 (z i)
                * Work.BoseKinLoc.fsT ℓ d s εT b 0
                    (Work.BoseKinLoc.fibre N i.1 Ψ (Work.PerSector.slotComb S z y))) := by rw [h5]
      _ = ℓ ^ (-3 : ℤ) * (∫ y in Work.PerSector.slotOutside (max L ℓ)
              (Submission.BoseGases.acube ℓ) S,
            ∫ ζ in Submission.BoseGases.abox S.card ℓ,
              ∑ i ∈ S.attach, Work.BoseKinLoc.indU ℓ 0 ((slotIsoME S ζ) i)
                * Work.BoseKinLoc.fsT ℓ d s εT b 0
                    (Work.BoseKinLoc.fibre N i.1 Ψ
                      (Work.PerSector.slotComb S (slotIsoME S ζ) y))) := by rw [h6]
      _ = ℓ ^ (-3 : ℤ) * (∫ y in Work.PerSector.slotOutside (max L ℓ)
              (Submission.BoseGases.acube ℓ) S,
            ∫ ζ in Submission.BoseGases.abox S.card ℓ,
              ∑ i ∈ S.attach, Work.BoseKinLoc.indU ℓ 0 (ζ (slotIso S i))
                * Work.BoseKinLoc.fsT ℓ d s εT b 0
                    (Work.BoseKinLoc.fibre N i.1 Ψ
                      (Work.PerSector.slotComb S (slotIsoME S ζ) y))) := by rw [h7]
      _ = ℓ ^ (-3 : ℤ) * (∫ y in Work.PerSector.slotOutside (max L ℓ)
              (Submission.BoseGases.acube ℓ) S,
            ∫ ζ in Submission.BoseGases.abox S.card ℓ,
              ∑ i ∈ S.attach, Work.BoseKinLoc.indU ℓ 0 (ζ (slotIso S i))
                * Work.BoseKinLoc.fsT ℓ d s εT b 0
                    (Work.BoseKinLoc.fibre S.card (slotIso S i) (fibState S Ψ y) ζ)) := by rw [h8]
      _ = ℓ ^ (-3 : ℤ) * (∫ y in Work.PerSector.slotOutside (max L ℓ)
              (Submission.BoseGases.acube ℓ) S,
            ∫ ζ in Submission.BoseGases.abox S.card ℓ,
              ∑ k : Fin S.card, Work.BoseKinLoc.indU ℓ 0 (ζ k)
                * Work.BoseKinLoc.fsT ℓ d s εT b 0
                    (Work.BoseKinLoc.fibre S.card k (fibState S Ψ y) ζ)) := by rw [h9]
      _ = ℓ ^ (-3 : ℤ) * (∫ y in Work.PerSector.slotOutside (max L ℓ)
              (Submission.BoseGases.acube ℓ) S,
            ∑ k : Fin S.card, ∫ ζ in Submission.BoseGases.abox S.card ℓ,
              Work.BoseKinLoc.indU ℓ 0 (ζ k)
                * Work.BoseKinLoc.fsT ℓ d s εT b 0
                    (Work.BoseKinLoc.fibre S.card k (fibState S Ψ y) ζ)) := by
          refine congrArg (fun t => ℓ ^ (-3 : ℤ) * t) ?_
          refine MeasureTheory.setIntegral_congr_ae (measurableSet_slotOutside ℓ (max L ℓ) S)
            (Filter.Eventually.of_forall (fun y hy => h10 y))
      _ = ℓ ^ (-3 : ℤ) * (∫ y in Work.PerSector.slotOutside (max L ℓ)
              (Submission.BoseGases.acube ℓ) S,
            ℓ ^ (3 : ℤ) * Work.BoseKinLoc.kinFormB S.card ℓ d s εT b (fibState S Ψ y)) := by
          refine congrArg (fun t => ℓ ^ (-3 : ℤ) * t) ?_
          refine MeasureTheory.setIntegral_congr_ae (measurableSet_slotOutside ℓ (max L ℓ) S)
            (Filter.Eventually.of_forall (fun y hy => h11 y))
      _ = ℓ ^ (-3 : ℤ) * (ℓ ^ (3 : ℤ) * ∫ y in Work.PerSector.slotOutside (max L ℓ)
              (Submission.BoseGases.acube ℓ) S,
            Work.BoseKinLoc.kinFormB S.card ℓ d s εT b (fibState S Ψ y)) := by
          rw [MeasureTheory.integral_const_mul]
      _ = ∫ y in Work.PerSector.slotOutside (max L ℓ) (Submission.BoseGases.acube ℓ) S,
            Work.BoseKinLoc.kinFormB S.card ℓ d s εT b (fibState S Ψ y) := by
          rw [← mul_assoc, hzz', one_mul]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [← Finset.sum_subset (Finset.subset_univ S)
    (fun i _ hiS => by rw [hzero S i hiS, mul_zero])]
  rw [← Finset.sum_attach]
  exact (key S).symm

/-- **The sector decomposition of the kinetic word.**  The `N`-body kinetic word `kinForm N ℓ d s εT b 0 Ψ` is the sum, over the slot sets `S`, of the box-restricted kinetic word `kinFormB |S| ℓ d s εT b` of the fibre state.  On the slot set of `S` the `i`-th slot integral of `kinForm` sees exactly the `i`-th slot fibre of the fibre state, and `fsT` is blind to the values off the sliding box (`Work.BoseKinLoc.Sector.fsT_box_invariant`); the slot splitting `slotME` is measure preserving, so the `x`-integral over the slot set is the Fubini integral over `(z, y)` (`Work.PerSector.slotME`, `Work.PerSector.slotME_image_abox`). -/
theorem kinForm_fibre_sum {N : ℕ} {ℓ L d s εT b : ℝ} (hℓ : 0 < ℓ)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (hsupp : tsupport Ψ ⊆ Submission.BoseGases.abox N L) :
    (∑ S : Finset (Fin N),
        ∫ y in Work.PerSector.slotOutside (max L ℓ) (Submission.BoseGases.acube ℓ) S,
          Work.BoseKinLoc.kinFormB S.card ℓ d s εT b (fibState S Ψ y))
      = Work.BoseKinLoc.kinForm N ℓ d s εT b 0 Ψ := by
  have hℓL' : ℓ ≤ max L ℓ := le_max_right L ℓ
  have hL'0 : 0 ≤ max L ℓ := le_trans (le_of_lt hℓ) hℓL'
  have hLL' : L ≤ max L ℓ := le_max_left L ℓ
  have hsupp' : tsupport Ψ ⊆ Submission.BoseGases.abox N (max L ℓ) :=
    fun x hx => abox_subset_of_le hLL' (hsupp hx)
  refine kinForm_fibre_sum_of (L := L) hℓ hΨ hsupp ?_ ?_
  · intro i
    exact Work.BoseKinLoc.Sector.integrable_indU_mul_fsT_fibre (ℓ := ℓ) (L := max L ℓ)
      hℓ hL'0 hΨ hsupp' i
  · intro m Φ hΦ hsuppΦ k
    exact (Work.BoseKinLoc.Sector.integrable_indU_mul_fsT_fibre (ℓ := ℓ) (L := max L ℓ)
      hℓ hL'0 hΦ hsuppΦ k).integrableOn

end Work.BoseKinLoc.Sector
