
import Mathlib
import Submission.Work.EKLC6Core.cutHelpers
import Submission.Work.EKLC6Core.saturated_measurable
import Submission.Work.EKLC6Core.borel_atom_saturated_measurable
import Submission.Work.Topology.exists_measurable_saturated_large
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLC6Core.exists_bound_shape_of_atom_eq

/-!
# `Work.EKLC6Core.plaqueAlgebra_of_ae_pointwise`

The `Prop`-level assembling step of the plaque construction: if the sigma-algebra `A` (a countably
generated sub-sigma-algebra of the Borel sigma-algebra of `X3`) satisfies, *almost everywhere*, the
three plaque conditions at a point

* every `A`-atom is contained in the `U`-orbit of its point,
* the shape `{u in U | u . x in [x]_A}` is `O cap U` with `O` open,
* the shape is entrywise bounded,

then there is a **conull** set `Z` with `IsPlaqueAlgebra U Z A`.

`IsPlaqueAlgebra U Z A` asks for those three conditions at *every* point of `Z`, plus
`MeasurableSet[A] Z`.  The three conditions are invariant under moving inside an `A`-atom, so

1. a Borel set `H` of full measure carries all three of them at each of its points
   (`exists_borel_conull_of_three_ae`, a direct consequence of the a.e. hypotheses: the
   measurable hulls of the complements of the three properties are null);
2. the code-map construction of `Work.Topology.exists_measurable_saturated_large` produces, for
   every `eps > 0` and for any sequence `B` generating `A`, an `A`-measurable set `Z_eps` with
   `mu Z_epsᶜ < eps` all of whose atoms meet `H`; taking a *union* over `eps = 1/(n+1)` gives an
   `A`-measurable `Z` with `mu Zᶜ = 0` (`saturated_conull_of_codes`).  Note that the union -- and
   not the intersection -- is what turns the `eps`-bounds into `mu Zᶜ = 0`: the complement of a
   union is contained in the complement of each member.
3. Since the set of good points is a union of atoms and `H` is contained in it, the saturation
   of `H` consists of good points; and every atom of `Z` meets `H`, so all points of `Z` are good.
   The atom-transfer package of `Work.EKLC6Core.cutHelpers` then moves the orbit clause and the
   openness of the shape from `H` to `Z`, `Work.EKLC6Core.exists_bound_shape_of_atom_eq` moves
   the entrywise bound, and `[x]_A subset Z` for `x in Z` is automatic from `MeasurableSet[A] Z`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## Step 1: three a.e. properties hold on a common Borel set of full measure -/

/-- **Three a.e. properties hold on a common Borel set of full measure.**

Instances are written out (`instMeasurableSpaceX3` is the Borel sigma-algebra of `X3`): a local
sigma-algebra hypothesis would otherwise be picked up by type class search, and `mu` is typed with
respect to the Borel sigma-algebra. -/
private theorem exists_borel_conull_of_three_ae
    {μ : @MeasureTheory.Measure X3 instMeasurableSpaceX3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {P1 P2 P3 : X3 → Prop}
    (h1 : ∀ᵐ x ∂μ, P1 x) (h2 : ∀ᵐ x ∂μ, P2 x) (h3 : ∀ᵐ x ∂μ, P3 x) :
    ∃ H : Set X3, @MeasurableSet X3 instMeasurableSpaceX3 H ∧ μ H = 1 ∧
      H ⊆ {x | P1 x} ∧ H ⊆ {x | P2 x} ∧ H ⊆ {x | P3 x} := by
  have hone : ∀ (P : X3 → Prop), (∀ᵐ x ∂μ, P x) →
      ∃ T : Set X3, @MeasurableSet X3 instMeasurableSpaceX3 T ∧ μ T = 0 ∧ ∀ x ∉ T, P x := by
    intro P h
    refine ⟨MeasureTheory.toMeasurable μ {x | ¬ P x},
      MeasureTheory.measurableSet_toMeasurable μ _, ?_, ?_⟩
    · rw [MeasureTheory.measure_toMeasurable]
      exact MeasureTheory.ae_iff.mp h
    · intro x hx
      by_contra hc
      exact hx (MeasureTheory.subset_toMeasurable μ _ (show x ∈ {x : X3 | ¬ P x} from hc))
  obtain ⟨T1, hT1m, hT1μ, hT1⟩ := hone P1 h1
  obtain ⟨T2, hT2m, hT2μ, hT2⟩ := hone P2 h2
  obtain ⟨T3, hT3m, hT3μ, hT3⟩ := hone P3 h3
  have hUm : @MeasurableSet X3 instMeasurableSpaceX3 (T1 ∪ T2 ∪ T3) :=
    (hT1m.union hT2m).union hT3m
  refine ⟨(T1 ∪ T2 ∪ T3)ᶜ, hUm.compl, ?_, ?_, ?_, ?_⟩
  · rw [MeasureTheory.measure_compl hUm (measure_ne_top μ _),
      measure_union_null (measure_union_null hT1μ hT2μ) hT3μ, measure_univ, tsub_zero]
  · intro x hx
    exact hT1 x fun hc => hx (Or.inl (Or.inl hc))
  · intro x hx
    exact hT2 x fun hc => hx (Or.inl (Or.inr hc))
  · intro x hx
    exact hT3 x fun hc => hx (Or.inr hc)

/-! ## Step 2: the measurable saturated set of full measure -/

/-- **A countably generated sigma-algebra has a generating sequence.** -/
private theorem exists_gen_seq_of_countable {A : MeasurableSpace X3}
    (hgen : ∃ b : Set (Set X3), b.Countable ∧ A = MeasurableSpace.generateFrom b) :
    ∃ B : ℕ → Set X3, (∀ n, @MeasurableSet X3 A (B n)) ∧
      A = MeasurableSpace.generateFrom (Set.range B) := by
  obtain ⟨b, hbc, hbA⟩ := hgen
  have hbc' : (insert Set.univ b).Countable := hbc.insert _
  have hne : (insert Set.univ b).Nonempty := ⟨Set.univ, Set.mem_insert _ _⟩
  obtain ⟨f, hf⟩ := hbc'.exists_eq_range hne
  refine ⟨f, ?_, ?_⟩
  · intro n
    have hmem : f n ∈ insert Set.univ b := by rw [hf]; exact Set.mem_range_self n
    rcases Set.mem_insert_iff.mp hmem with h | h
    · rw [h]; exact @MeasurableSet.univ X3 A
    · rw [hbA]
      exact MeasurableSpace.measurableSet_generateFrom h
  · rw [hbA, ← hf, MeasurableSpace.generateFrom_insert_univ]

/-- **A measurable, saturated set of full measure.**

If `A` is a countably generated sub-sigma-algebra of the Borel sigma-algebra of `X3`, presented by
a generating sequence `B`, and `H` is a Borel set of full `mu`-measure, then there is an
`A`-measurable `Z` with `mu Zᶜ = 0` every `A`-atom of which meets `H`.

The proof applies `Work.Topology.exists_measurable_saturated_large` to the trimmed measure
`mu.trim hAle` at the scale `eps n = (n + 1)⁻¹` and takes the **union** of the resulting sets:
the complement of the union is contained in the complement of each member, so its measure is
bounded by `(n+1)⁻¹` for every `n`, hence is `0`. -/
private theorem saturated_conull_of_codes
    {A : MeasurableSpace X3} (hAle : A ≤ borel X3)
    {B : ℕ → Set X3} (hBmeas : ∀ n, @MeasurableSet X3 A (B n))
    (μ : @MeasureTheory.Measure X3 instMeasurableSpaceX3) [MeasureTheory.IsProbabilityMeasure μ]
    {H : Set X3} (hH : @MeasurableSet X3 instMeasurableSpaceX3 H) (hH1 : μ H = 1) :
    ∃ Z : Set X3, @MeasurableSet X3 A Z ∧ μ Zᶜ = 0 ∧
      ∀ x ∈ Z, ∃ y ∈ H, ∀ k : ℕ, (x ∈ B k ↔ y ∈ B k) := by
  classical
  have hprob : MeasureTheory.IsProbabilityMeasure (μ.trim hAle) :=
    MeasureTheory.IsProbabilityMeasure.mk (by
      rw [MeasureTheory.trim_measurableSet_eq (μ := μ) hAle (@MeasurableSet.univ X3 A),
        MeasureTheory.measure_univ])
  haveI := hprob
  have hH1' : (μ.trim hAle) H = 1 := by
    refine le_antisymm ?_ ?_
    · calc (μ.trim hAle) H ≤ (μ.trim hAle) Set.univ :=
          MeasureTheory.measure_mono (Set.subset_univ H)
        _ = 1 := MeasureTheory.measure_univ
    · calc (1 : ℝ≥0∞) = μ H := hH1.symm
        _ ≤ (μ.trim hAle) H := MeasureTheory.le_trim (μ := μ) hAle
  have key : ∀ n : ℕ, ∃ Z : Set X3, @MeasurableSet X3 A Z ∧
      (∀ x ∈ Z, ∃ y ∈ H, ∀ k : ℕ, (x ∈ B k ↔ y ∈ B k)) ∧
      (μ.trim hAle) Zᶜ < (((n + 1 : ℕ)) : ℝ≥0∞)⁻¹ := by
    intro n
    have hε : (0 : ℝ≥0∞) < (((n + 1 : ℕ)) : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.inv_pos]
      exact ENNReal.natCast_ne_top _
    have hlt : 1 - (((n + 1 : ℕ)) : ℝ≥0∞)⁻¹ < (μ.trim hAle) H := by
      rw [hH1']
      exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (ne_of_gt hε)
    obtain ⟨Z, hZ1, hZ2, _hZ3, hZ4⟩ :=
      @Work.Topology.exists_measurable_saturated_large X3 _ _ _ instMeasurableSpaceX3 _ A hAle
        B hBmeas H hH (μ.trim hAle) _ _ hε hlt
    exact ⟨Z, hZ1, hZ2, hZ4⟩
  choose Z hZmeas hZmeet hZμ using key
  have hZi : @MeasurableSet X3 A (⋃ n, Z n) := MeasurableSet.iUnion hZmeas
  refine ⟨⋃ n, Z n, hZi, ?_, ?_⟩
  · rw [← MeasureTheory.trim_measurableSet_eq (μ := μ) hAle hZi.compl]
    have hb : ∀ n : ℕ, (μ.trim hAle) (⋃ n, Z n)ᶜ ≤ (((n + 1 : ℕ)) : ℝ≥0∞)⁻¹ := by
      intro n
      refine le_of_lt (lt_of_le_of_lt ?_ (hZμ n))
      exact MeasureTheory.measure_mono
        (fun x hx hxz => hx (Set.mem_iUnion.mpr ⟨n, hxz⟩))
    have htend : Tendsto (fun n : ℕ => (((n + 1 : ℕ)) : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero.comp (Filter.tendsto_add_atTop_nat 1)
    exact le_bot_iff.mp (le_of_tendsto_of_tendsto tendsto_const_nhds htend
      (Filter.Eventually.of_forall hb))
  · intro x hx
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
    exact hZmeet n x hxn

/-! ## The main assembly -/

theorem plaqueAlgebra_of_ae_pointwise
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup Work.EKLContract.SL3} {A : MeasurableSpace Work.EKLContract.X3}
    (hAle : A ≤ borel Work.EKLContract.X3)
    (hgen : ∃ b : Set (Set Work.EKLContract.X3), b.Countable ∧
      A = MeasurableSpace.generateFrom b)
    (horbit : ∀ᵐ x ∂μ, Work.EKLContract.atom A x ⊆
      (fun u : Work.EKLContract.SL3 => u • x) '' (U : Set Work.EKLContract.SL3))
    (hopen : ∀ᵐ x ∂μ, ∃ O : Set Work.EKLContract.SL3, IsOpen O ∧
      Work.EKLContract.shape A U x = O ∩ (U : Set Work.EKLContract.SL3))
    (hbdd : ∀ᵐ x ∂μ, ∃ C : ℝ, ∀ u ∈ Work.EKLContract.shape A U x,
      ∀ i j : Fin 3, |u i j| ≤ C) :
    ∃ Z : Set Work.EKLContract.X3, μ Zᶜ = 0 ∧ Work.EKLContract.IsPlaqueAlgebra U Z A := by
  classical
  -- Step 1: a Borel set of full measure on which all three conditions hold pointwise.
  obtain ⟨H, hHmeas, hHone, hHG1, hHG2, hHG3⟩ :=
    exists_borel_conull_of_three_ae (μ := μ)
      (P1 := fun x => atom A x ⊆ (fun u : SL3 => u • x) '' (U : Set SL3))
      (P2 := fun x => ∃ O : Set SL3, IsOpen O ∧ shape A U x = O ∩ (U : Set SL3))
      (P3 := fun x => ∃ C : ℝ, ∀ u ∈ shape A U x, ∀ i j : Fin 3, |u i j| ≤ C)
      horbit hopen hbdd
  -- Step 2: a generating sequence of `A` and an `A`-measurable conull set whose atoms meet `H`.
  obtain ⟨B, hBmeas, hBgen⟩ := exists_gen_seq_of_countable (A := A) hgen
  obtain ⟨Z, hZmeas, hZnull, hZcodes⟩ := saturated_conull_of_codes hAle hBmeas μ hHmeas hHone
  -- Every point of `Z` is good: its atom meets `H`, hence is an atom of a point of `H`.
  have hZmeet : ∀ x ∈ Z, ∃ y ∈ H, atom A x = atom A y := by
    intro x hx
    obtain ⟨y, hyH, hy⟩ := hZcodes x hx
    have hyatom : y ∈ atom A x := by
      rw [hBgen, mem_atom_generateFrom_range_iff]
      exact fun k => (hy k).symm
    exact ⟨y, hyH, (atom_eq_of_mem_atom_c hyatom).symm⟩
  refine ⟨Z, hZnull, hAle, hgen, hZmeas, fun x hx => ⟨?_, ?_, ?_, ?_⟩⟩
  · -- the atom of a point of `Z` is contained in `Z`
    exact Set.sInter_subset_of_mem ⟨hZmeas, hx⟩
  · -- the orbit clause is inherited from `H`
    exact atom_subset_orb_of_forall_exists_atom_eq_c hZmeet hHG1 x hx
  · -- openness of the shape is inherited from `H`
    exact exists_isOpen_shape_of_forall_exists_atom_eq_c hZmeet hHG1
      (fun y hy => hHG2 hy) x hx
  · -- the entrywise bound is inherited from `H`
    obtain ⟨y, hyH, hyatom⟩ := hZmeet x hx
    exact exists_bound_shape_of_atom_eq
      (atom_subset_orb_of_forall_exists_atom_eq_c hZmeet hHG1 x hx) hyatom (hHG3 hyH)

end Work.EKLC6Core
