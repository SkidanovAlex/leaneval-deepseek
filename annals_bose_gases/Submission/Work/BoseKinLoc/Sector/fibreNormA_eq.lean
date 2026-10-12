import Mathlib.CategoryTheory.Countable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Sector.integrable_sq_of_contDiff_tsupport
import Submission.Work.BoseKinLoc.Sector.lintegral_sectorRegion_eq
import Submission.Work.BoseKinLoc.Sector.ofReal_sqNormB_eq_lintegral
import Submission.Work.BoseKinLoc.Sector.stronglyMeasurable_sqNormB_fibState
import Submission.Work.BoseKinLoc.Sector.translate_abox_subset_iUnion_sectorRegion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Sector.fibreNormA_eq` — the sector decomposition of the squared norm

This module proves the `L²`-bookkeeping half of the C3 sector decomposition for a state carried by a
*translated* box: for a smooth state `Ψ` supported in `c + abox N L`, the sum over the slot sets `S`
of the box `L²`-mass of the fibre states, integrated over the outside configurations in the
translated ambient box `c + acube (max L ℓ)`, is the total squared norm `∫ Ψ²`.

The mathematical content is the Fubini/Tonelli identity of the slot splitting, run in the following
order (all at the level of `∫⁻` of nonnegative integrands, the `ℝ≥0∞`-identities then being read
back through `ENNReal.toReal`):

* the *sector regions* `sectorRegion A B S` (configurations whose `B`-occupant is `S` and all of
  whose coordinates outside `S` lie in `A`) cover the support of `Ψ` and are pairwise disjoint;
* `∫⁻ f` splits as the sum over `S` of `∫⁻` over `sectorRegion A B S` (a pointwise partition of
  unity by indicators, `lintegral_finsetSum`);
* the measure-preserving slot splitting `slotME S` (whose inverse is `slotComb S`) transports each
  sector-region integral to the product of the in-box and outside slot boxes
  (`lintegral_sectorRegion_eq`), and Tonelli turns it into the iterated integral;
* the re-indexing by the order isomorphism `slotIso S` (`lintegral_slotBox_slotIso`) exhibits the
  in-box integral as the box mass of the fibre state `fibState`.

The `ℝ`-identity follows from `integral_eq_lintegral_of_nonneg_ae` (nonnegativity and strong
measurability of each fibre mass, no integrability needed) together with the finiteness of the total
`∫⁻`, which follows from the integrability of `Ψ²` (smooth, compactly supported); this is where
`ENNReal.toReal_sum` is applied.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Sector

open Submission.BoseGases
open Work.PerSector

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {N : ℕ}

/-! ## 1. The sector regions -/

/-- The **sector region** of the slot set `S` for the box `B` and the ambient set `A`: the
configurations whose `B`-occupant is exactly `S` and all of whose coordinates outside `S` lie in
`A`.  These are the pieces of the sector decomposition of the squared norm; the union over `S`
contains every configuration all of whose coordinates lie in `A ∪ B` with those in `B` forming a
slot set, in particular every configuration supported in a translate of a box contained in `A`. -/
def sectorRegion (A B : Set ℝ³) (S : Finset (Fin N)) : Set (X N) :=
  Work.PerSector.slotSet B S ∩ {x : X N | ∀ j : Work.PerSector.SlotOut N S, x j.1 ∈ A}

/-- The sector regions are measurable for a measurable ambient set `A` and a measurable box
`B`. -/
theorem sectorRegion_measurable {A B : Set ℝ³} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (S : Finset (Fin N)) : MeasurableSet (sectorRegion A B S) := by
  refine (Work.PerSector.slotSet_measurable B hB S).inter ?_
  have h1 : {x : X N | ∀ j : Work.PerSector.SlotOut N S, x j.1 ∈ A}
      = ⋂ j : Work.PerSector.SlotOut N S, (fun x : X N => x j.1) ⁻¹' A := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h1]
  exact MeasurableSet.iInter (fun j => hA.preimage (measurable_pi_apply j.1))

/-- Two sector regions with the same box containing a common configuration carry the same slot
set. -/
theorem sectorRegion_eq_of_mem {A B : Set ℝ³} {S T : Finset (Fin N)} {x : X N}
    (hS : x ∈ sectorRegion A B S) (hT : x ∈ sectorRegion A B T) : S = T :=
  Work.PerSector.slotSet_eq_of_mem hS.1 hT.1

/-! ## 2. Elementary geometry of the translated boxes -/

/-- The centred cube `acube` is monotone in its side length. -/
theorem acube_mono {ℓ M : ℝ} (h : ℓ ≤ M) : Submission.BoseGases.acube ℓ ⊆ Submission.BoseGases.acube M := by
  intro z hz
  rw [Submission.BoseGases.mem_acube_iff] at hz ⊢
  intro m
  exact ⟨by linarith [(hz m).1], by linarith [(hz m).2]⟩

/-- A translate of a centred cube is measurable. -/
theorem measurableSet_translate_acube (c : ℝ³) (M : ℝ) :
    MeasurableSet ((fun z : ℝ³ => c + z) '' Submission.BoseGases.acube M) := by
  rw [show ((fun z : ℝ³ => c + z) '' Submission.BoseGases.acube M)
      = (fun z : ℝ³ => z - c) ⁻¹' Submission.BoseGases.acube M from by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hz
      exact ⟨z - c, hz, by simp⟩]
  exact (Submission.BoseGases.acube_measurable M).preimage (by fun_prop)

/-- The reassembly `slotComb S` of an inside and an outside slot configuration is continuous in the
pair (it is a coordinatewise selection). -/
theorem continuous_slotComb (S : Finset (Fin N)) :
    Continuous (fun p : (Work.PerSector.SlotIn N S → ℝ³) × (Work.PerSector.SlotOut N S → ℝ³) =>
      Work.PerSector.slotComb S p.1 p.2) := by
  refine continuous_pi (fun i => ?_)
  by_cases h : i ∈ S
  · have hpt : (fun p : (Work.PerSector.SlotIn N S → ℝ³) × (Work.PerSector.SlotOut N S → ℝ³) =>
        Work.PerSector.slotComb S p.1 p.2 i) = fun p => p.1 ⟨i, h⟩ := by
      funext p
      rw [Work.PerSector.slotComb_apply, dif_pos h]
    rw [hpt]
    exact (continuous_apply (⟨i, h⟩ : Work.PerSector.SlotIn N S)).comp continuous_fst
  · have hpt : (fun p : (Work.PerSector.SlotIn N S → ℝ³) × (Work.PerSector.SlotOut N S → ℝ³) =>
        Work.PerSector.slotComb S p.1 p.2 i) = fun p => p.2 ⟨i, h⟩ := by
      funext p
      rw [Work.PerSector.slotComb_apply, dif_neg h]
    rw [hpt]
    exact (continuous_apply (⟨i, h⟩ : Work.PerSector.SlotOut N S)).comp continuous_snd

/-- The reassembled fibre integral of a measurable state is jointly measurable in the pair (inside,
outside) of slot configurations.  This is the measurability input of the Tonelli step below; it is
stated for an arbitrary (not necessarily real-valued) codomain. -/
theorem measurable_slotComb_pair {α : Type*} [MeasurableSpace α] (S : Finset (Fin N))
    {Φ : X N → α} (hΦ : Measurable Φ) :
    Measurable (fun p : (Work.PerSector.SlotIn N S → ℝ³) × (Work.PerSector.SlotOut N S → ℝ³) =>
      Φ (Work.PerSector.slotComb S p.1 p.2)) :=
  hΦ.comp (continuous_slotComb S).measurable

/-- The box mass of a state is nonnegative (the Bochner convention only makes it larger: a
non-integrable integrand gives the junk value `0`). -/
theorem sqNormB_nonneg_A {n : ℕ} {ℓ : ℝ} {Φ : X n → ℝ} :
    0 ≤ Work.BoseKinLoc.sqNormB n ℓ Φ := by
  rw [Work.BoseKinLoc.sqNormB]
  exact setIntegral_nonneg (Submission.BoseGases.abox_measurable n ℓ) (fun x _ => sq_nonneg (Φ x))

/-! ## 3. The partition by the sector regions -/

/-- **Partition of a nonnegative integrand by the sector regions.**  If `f` vanishes off the union
of the sector regions, then `∫⁻ f` is the sum of the `∫⁻` over the individual sector regions: the
indicators of the (disjoint) sector regions sum to one on the support of `f`. -/
theorem lintegral_eq_sum_sectorRegion {A B : Set ℝ³} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {f : X N → ℝ≥0∞} (hf : Measurable f)
    (hzero : ∀ x : X N, x ∉ ⋃ S : Finset (Fin N), sectorRegion A B S → f x = 0) :
    ∫⁻ x, f x = ∑ S : Finset (Fin N), ∫⁻ x in sectorRegion A B S, f x := by
  classical
  have hR : ∀ S : Finset (Fin N), MeasurableSet (sectorRegion A B S) :=
    fun S => sectorRegion_measurable hA hB S
  have hpoint : ∀ x : X N, (∑ S : Finset (Fin N), (sectorRegion A B S).indicator f x) = f x := by
    intro x
    by_cases hx : ∃ S : Finset (Fin N), x ∈ sectorRegion A B S
    · obtain ⟨S0, hS0⟩ := hx
      rw [Finset.sum_eq_single S0]
      · exact Set.indicator_of_mem hS0 f
      · intro S _ hne
        exact Set.indicator_of_notMem (fun hS => hne (sectorRegion_eq_of_mem hS hS0)) f
      · intro h
        exact absurd (Finset.mem_univ S0) h
    · rw [Finset.sum_congr rfl (fun S _ => Set.indicator_of_notMem (fun hS => hx ⟨S, hS⟩) f),
        Finset.sum_const_zero]
      exact (hzero x (fun hmem => hx (Set.mem_iUnion.mp hmem))).symm
  calc ∫⁻ x, f x
      = ∫⁻ x, ∑ S : Finset (Fin N), (sectorRegion A B S).indicator f x :=
        lintegral_congr (fun x => (hpoint x).symm)
    _ = ∑ S : Finset (Fin N), ∫⁻ x, (sectorRegion A B S).indicator f x :=
        lintegral_finsetSum _ (fun S _ => hf.indicator (hR S))
    _ = ∑ S : Finset (Fin N), ∫⁻ x in sectorRegion A B S, f x := by
        refine Finset.sum_congr rfl (fun S _ => ?_)
        exact lintegral_indicator (hR S) f

/-! ## 4. Change of variables and Fubini -/

/-- **Change of variables along the measure-preserving slot splitting**, in the vocabulary of the
sector region `sectorRegion A B S` (definitionally the same set as in `..._stub`). -/
theorem lintegral_sectorRegion_eq' {A B : Set ℝ³} (S : Finset (Fin N)) (f : X N → ℝ≥0∞) :
    ∫⁻ x in sectorRegion A B S, f x
      = ∫⁻ p in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) B
          ×ˢ Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S) (A ∩ Bᶜ),
        f (Work.PerSector.slotComb S p.1 p.2) :=
  lintegral_sectorRegion_eq S A B f

/-- **The sector decomposition of a nonnegative integrand (Fubini/Tonelli).**  If `f` vanishes off
the union of the sector regions of the box `B` and the ambient set `A`, then `∫⁻ f` equals the sum
over the slot sets `S` of the iterated integral of `f ∘ slotComb S` over the in-box slot box `B^S`
and the outside slot box `(A ∩ Bᶜ)^{Sᶜ}`. -/
theorem lintegral_eq_sum_slotBox {A B : Set ℝ³} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {f : X N → ℝ≥0∞} (hf : Measurable f)
    (hzero : ∀ x : X N, x ∉ ⋃ S : Finset (Fin N), sectorRegion A B S → f x = 0) :
    ∫⁻ x, f x = ∑ S : Finset (Fin N),
      ∫⁻ y in Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S) (A ∩ Bᶜ),
        ∫⁻ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) B,
          f (Work.PerSector.slotComb S z y) := by
  classical
  rw [lintegral_eq_sum_sectorRegion hA hB hf hzero]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  refine (lintegral_sectorRegion_eq' (A := A) (B := B) S f).trans ?_
  have hG : AEMeasurable (fun p : (Work.PerSector.SlotIn N S → ℝ³) ×
        (Work.PerSector.SlotOut N S → ℝ³) => f (Work.PerSector.slotComb S p.1 p.2))
      (((volume : Measure (Work.PerSector.SlotIn N S → ℝ³)).prod
        (volume : Measure (Work.PerSector.SlotOut N S → ℝ³))).restrict
        (Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) B
          ×ˢ Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S) (A ∩ Bᶜ))) :=
    ((measurable_slotComb_pair S hf).aemeasurable).restrict
  rw [show (volume : Measure ((Work.PerSector.SlotIn N S → ℝ³) ×
        (Work.PerSector.SlotOut N S → ℝ³)))
      = (volume : Measure (Work.PerSector.SlotIn N S → ℝ³)).prod
        (volume : Measure (Work.PerSector.SlotOut N S → ℝ³)) from rfl]
  exact setLIntegral_prod_symm _ hG

/-- **Re-indexing the in-box integral.**  Transporting the in-box slot integral of `Ψ ∘ slotComb`
along the order isomorphism `slotIso S` exhibits it as the box mass of the fibre state
`fibState S Ψ y` on `abox |S| ℓ`. -/
theorem sum_slotBox_eq_sum_fibState {ℓ : ℝ} {A : Set ℝ³} (Ψ : X N → ℝ) :
    (∑ S : Finset (Fin N),
        ∫⁻ y in Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
            (A ∩ (Submission.BoseGases.acube ℓ)ᶜ),
          ∫⁻ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S)
              (Submission.BoseGases.acube ℓ),
            ENNReal.ofReal ((Ψ (Work.PerSector.slotComb S z y)) ^ 2))
      = ∑ S : Finset (Fin N),
          ∫⁻ y in Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
              (A ∩ (Submission.BoseGases.acube ℓ)ᶜ),
            ∫⁻ z in Submission.BoseGases.abox S.card ℓ,
              ENNReal.ofReal ((fibState S Ψ y z) ^ 2) := by
  refine Finset.sum_congr rfl (fun S _ => ?_)
  refine lintegral_congr (fun y => ?_)
  rw [← lintegral_slotBox_slotIso S (Submission.BoseGases.acube_measurable ℓ)
    (fun z : Work.PerSector.SlotIn N S → ℝ³ =>
      ENNReal.ofReal ((Ψ (Work.PerSector.slotComb S z y)) ^ 2))]
  rw [show Work.PerSector.slotBox (ι := Fin S.card) (Submission.BoseGases.acube ℓ)
      = Submission.BoseGases.abox S.card ℓ from rfl]
  exact lintegral_congr (fun x => by simp only [fibState_apply])

/-! ## 5. The `L²`-bookkeeping of the sector decomposition -/

/-- **The sector decomposition of the squared norm, `∫⁻` form.**  For a measurable state `Ψ` whose
support lies in the union of the sector regions of the box `acube ℓ` and the ambient set `A`, the
total `∫⁻` of `ofReal (Ψ²)` is the sum over the slot sets `S` of the outside integral of the box
`L²`-mass of the fibre state `fibState S Ψ y`. -/
theorem lintegral_eq_sum_fibState {ℓ : ℝ} {A : Set ℝ³} (hA : MeasurableSet A)
    {Ψ : X N → ℝ} (hΨm : Measurable Ψ)
    (hzero : ∀ x : X N, x ∉ ⋃ S : Finset (Fin N), sectorRegion A (Submission.BoseGases.acube ℓ) S →
      ENNReal.ofReal ((Ψ x) ^ 2) = 0) :
    ∫⁻ x, ENNReal.ofReal ((Ψ x) ^ 2)
      = ∑ S : Finset (Fin N),
          ∫⁻ y in Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
              (A ∩ (Submission.BoseGases.acube ℓ)ᶜ),
            ∫⁻ z in Submission.BoseGases.abox S.card ℓ,
              ENNReal.ofReal ((fibState S Ψ y z) ^ 2) :=
  (lintegral_eq_sum_slotBox hA (Submission.BoseGases.acube_measurable ℓ)
    ((hΨm.pow_const 2).ennreal_ofReal) hzero).trans (sum_slotBox_eq_sum_fibState Ψ)

/-- **The sector decomposition of the squared norm, translated support.**  This is the general
`L ≤ M` form of the requested statement: for a smooth state `Ψ` supported in `c + abox N L` and any
`M ≥ L`, the fibre norm sum with outside configurations in the translated box `c + acube M` equals
`∫ Ψ²`. -/
theorem fibreNormA_eq_of_le {ℓ : ℝ} (hℓ : 0 < ℓ) {c : ℝ³} {L M : ℝ} (hLM : L ≤ M)
    {Ψ : X N → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (hsupp : tsupport Ψ ⊆ (fun x : X N => fun i : Fin N => c + x i) '' Submission.BoseGases.abox N L) :
    fibreNormA ℓ ((fun z : ℝ³ => c + z) '' Submission.BoseGases.acube M) Ψ
      = ∫ x : X N, (Ψ x) ^ 2 := by
  classical
  set A : Set ℝ³ := (fun z : ℝ³ => c + z) '' Submission.BoseGases.acube M with hA
  have hAmeas : MeasurableSet A := by
    rw [hA]
    exact measurableSet_translate_acube c M
  have hΨc : Continuous Ψ := hΨ.continuous
  have hΨm : Measurable Ψ := hΨc.measurable
  -- the sector regions cover the support
  have hcover : (fun x : X N => fun i : Fin N => c + x i) '' Submission.BoseGases.abox N L
      ⊆ ⋃ S : Finset (Fin N), sectorRegion A (Submission.BoseGases.acube ℓ) S := by
    refine translate_abox_subset_iUnion_sectorRegion (ℓ := ℓ) (A := A) ?_
    intro z hz
    rw [hA]
    exact ⟨z, acube_mono hLM hz, rfl⟩
  have hzero : ∀ x : X N,
      x ∉ ⋃ S : Finset (Fin N), sectorRegion A (Submission.BoseGases.acube ℓ) S →
      ENNReal.ofReal ((Ψ x) ^ 2) = 0 := by
    intro x hx
    have hΨx : Ψ x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx (hcover (hsupp h)))
    rw [hΨx]
    simp
  -- the `∫⁻`-identity
  have hmaster : ∫⁻ x, ENNReal.ofReal ((Ψ x) ^ 2)
      = ∑ S : Finset (Fin N),
          ∫⁻ y in Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
              (A ∩ (Submission.BoseGases.acube ℓ)ᶜ),
            ∫⁻ z in Submission.BoseGases.abox S.card ℓ,
              ENNReal.ofReal ((fibState S Ψ y z) ^ 2) :=
    lintegral_eq_sum_fibState hAmeas hΨm hzero
  -- the total `∫⁻` is finite
  have hLfin : (∫⁻ x, ENNReal.ofReal ((Ψ x) ^ 2)) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_sq_of_contDiff_tsupport hΨ hsupp)
      (Filter.Eventually.of_forall (fun x => sq_nonneg (Ψ x)))]
    exact ENNReal.ofReal_ne_top
  -- the per-slot-set real/`ℝ≥0∞` conversion
  have hterm : ∀ S : Finset (Fin N),
      (∫ y in Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
          (A ∩ (Submission.BoseGases.acube ℓ)ᶜ),
          Work.BoseKinLoc.sqNormB S.card ℓ (fibState S Ψ y))
        = (∫⁻ y in Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
              (A ∩ (Submission.BoseGases.acube ℓ)ᶜ),
            ENNReal.ofReal (Work.BoseKinLoc.sqNormB S.card ℓ (fibState S Ψ y))).toReal := by
    intro S
    exact integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun y => sqNormB_nonneg_A))
      (((stronglyMeasurable_sqNormB_fibState S hΨm).aestronglyMeasurable).restrict)
  -- the fibre mass is the `∫⁻` of the fibre state
  have hfib : ∀ S : Finset (Fin N),
      (∫⁻ y in Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
          (A ∩ (Submission.BoseGases.acube ℓ)ᶜ),
        ENNReal.ofReal (Work.BoseKinLoc.sqNormB S.card ℓ (fibState S Ψ y)))
        = ∫⁻ y in Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
            (A ∩ (Submission.BoseGases.acube ℓ)ᶜ),
          ∫⁻ z in Submission.BoseGases.abox S.card ℓ,
            ENNReal.ofReal ((fibState S Ψ y z) ^ 2) := by
    intro S
    refine lintegral_congr (fun y => ?_)
    exact ofReal_sqNormB_eq_lintegral hℓ (contDiff_fibState S hΨ y).continuous
  -- the sum of the per-slot-set `∫⁻` of the box masses is the (finite) total `∫⁻`
  have hfibsum : (∑ S : Finset (Fin N),
        ∫⁻ y in Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
            (A ∩ (Submission.BoseGases.acube ℓ)ᶜ),
          ENNReal.ofReal (Work.BoseKinLoc.sqNormB S.card ℓ (fibState S Ψ y)))
      = ∫⁻ x, ENNReal.ofReal ((Ψ x) ^ 2) := by
    rw [hmaster]
    exact Finset.sum_congr rfl (fun S _ => hfib S)
  have hsumfin : ∀ S : Finset (Fin N),
      (∫⁻ y in Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
          (A ∩ (Submission.BoseGases.acube ℓ)ᶜ),
        ENNReal.ofReal (Work.BoseKinLoc.sqNormB S.card ℓ (fibState S Ψ y))) ≠ ⊤ := by
    intro S
    have hle : (∫⁻ y in Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
          (A ∩ (Submission.BoseGases.acube ℓ)ᶜ),
        ENNReal.ofReal (Work.BoseKinLoc.sqNormB S.card ℓ (fibState S Ψ y)))
        ≤ ∑ T : Finset (Fin N),
            ∫⁻ y in Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N T)
                (A ∩ (Submission.BoseGases.acube ℓ)ᶜ),
              ENNReal.ofReal (Work.BoseKinLoc.sqNormB T.card ℓ (fibState T Ψ y)) :=
      Finset.single_le_sum (s := Finset.univ)
        (f := fun T : Finset (Fin N) =>
          ∫⁻ y in Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N T)
              (A ∩ (Submission.BoseGases.acube ℓ)ᶜ),
            ENNReal.ofReal (Work.BoseKinLoc.sqNormB T.card ℓ (fibState T Ψ y)))
        (a := S) (fun T _ => bot_le) (Finset.mem_univ S)
    exact ne_top_of_le_ne_top (by rw [hfibsum]; exact hLfin) hle
  -- assembly
  have hstart : fibreNormA ℓ ((fun z : ℝ³ => c + z) '' Submission.BoseGases.acube M) Ψ
      = ∑ S : Finset (Fin N),
          ∫ y in Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
              (A ∩ (Submission.BoseGases.acube ℓ)ᶜ),
            Work.BoseKinLoc.sqNormB S.card ℓ (fibState S Ψ y) := by
    rw [← hA, Work.BoseKinLoc.Sector.fibreNormA]
  calc fibreNormA ℓ ((fun z : ℝ³ => c + z) '' Submission.BoseGases.acube M) Ψ
      = ∑ S : Finset (Fin N),
          ∫ y in Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
              (A ∩ (Submission.BoseGases.acube ℓ)ᶜ),
            Work.BoseKinLoc.sqNormB S.card ℓ (fibState S Ψ y) := hstart
    _ = ∑ S : Finset (Fin N),
          (∫⁻ y in Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
              (A ∩ (Submission.BoseGases.acube ℓ)ᶜ),
            ENNReal.ofReal (Work.BoseKinLoc.sqNormB S.card ℓ (fibState S Ψ y))).toReal :=
        Finset.sum_congr rfl (fun S _ => hterm S)
    _ = (∑ S : Finset (Fin N),
          ∫⁻ y in Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
              (A ∩ (Submission.BoseGases.acube ℓ)ᶜ),
            ENNReal.ofReal (Work.BoseKinLoc.sqNormB S.card ℓ (fibState S Ψ y))).toReal :=
        (ENNReal.toReal_sum (fun a _ => hsumfin a)).symm
    _ = (∑ S : Finset (Fin N),
          ∫⁻ y in Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
              (A ∩ (Submission.BoseGases.acube ℓ)ᶜ),
            ∫⁻ z in Submission.BoseGases.abox S.card ℓ,
              ENNReal.ofReal ((fibState S Ψ y z) ^ 2)).toReal := by
        congr 1
        exact Finset.sum_congr rfl (fun S _ => hfib S)
    _ = (∫⁻ x, ENNReal.ofReal ((Ψ x) ^ 2)).toReal := by rw [← hmaster]
    _ = ∫ x : X N, (Ψ x) ^ 2 :=
        (integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall (fun x => sq_nonneg (Ψ x)))
          ((hΨc.pow 2).aestronglyMeasurable)).symm

/-- **The sector decomposition of the squared norm, translated support.**  For a smooth state `Ψ` supported in the translated box `c + abox N L`, the total squared norm is the sum, over the slot sets `S`, of the box `L²`-mass of the fibre state integrated over the outside configurations in the translated ambient box `c + acube (max L ℓ)`: `fibreNormA ℓ (c + acube (max L ℓ)) Ψ = ∫ Ψ²`.  This is `fibreNorm_eq` with a general support box (the `L²`-bookkeeping of the sector decomposition, by the slot partition and the measure-preserving slot splitting `slotME`, Tonelli at the level of `∫⁻` of nonnegative integrands, then converting back using compact support). -/
theorem fibreNormA_eq {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {c : ℝ³} {L : ℝ}
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (hsupp : tsupport Ψ ⊆ (fun x : Submission.BoseGases.X N => fun i : Fin N => c + x i) ''
      Submission.BoseGases.abox N L) :
    fibreNormA ℓ ((fun z : ℝ³ => c + z) '' Submission.BoseGases.acube (max L ℓ)) Ψ
      = ∫ x : Submission.BoseGases.X N, (Ψ x) ^ 2 :=
  fibreNormA_eq_of_le hℓ (le_max_left L ℓ) hΨ hsupp

end Work.BoseKinLoc.Sector
