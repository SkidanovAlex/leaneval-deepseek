import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLContract.Lemmas.Gamma3Facts

/-!
# `Work.EKLProd.exists_compact_family`

The Luzin clause `hU6` produces, for every `ε > 0`, a compact set `K ⊆ XT` with `μ Kᶜ < ε`
on which every "leafwise average" `x ↦ ∫ g, f g ∂(νT x)` is continuous.

What the rest of the development needs is a *monotone* family `K : ℕ → Set X₃` of compact
subsets of `XT` with `μ (K m)ᶜ < (m+1)⁻¹`, the same continuity property, and `K` monotone.

The nesting is obtained for free by taking the union of the first `m+1` sets produced by `hU6`
at the levels `1, 1/2, 1/3, …`: a finite union of compact sets is compact, it is contained in
`XT`, the family is monotone by construction, and the complement of the union is contained in
the complement of its largest member, so `μ (K m)ᶜ ≤ μ (A m)ᶜ < (m+1)⁻¹`.  Continuity on the
finite union uses that a finite family of sets is locally finite and that compact sets are
closed.
-/

open MeasureTheory
open scoped ENNReal

set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLProd

/-- A function continuous on each member of a *finite* family of compact sets is continuous on
the union.  (A finite family of sets is locally finite, and compact sets are closed.) -/
lemma continuousOn_iUnion_of_isCompact {ι : Type*} [Finite ι]
    {A : ι → Set Work.EKLContract.X3} {f : Work.EKLContract.X3 → ℝ}
    (hA : ∀ i, IsCompact (A i)) (hf : ∀ i, ContinuousOn f (A i)) :
    ContinuousOn f (⋃ i, A i) :=
  LocallyFinite.continuousOn_iUnion (locallyFinite_of_finite A)
    (fun i ↦ (hA i).isClosed) hf

theorem exists_compact_family {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {νT : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {XT : Set Work.EKLContract.X3}
    (hU6 : ∀ ε : ENNReal, 0 < ε → ∃ K : Set Work.EKLContract.X3, IsCompact K ∧ K ⊆ XT ∧ μ Kᶜ < ε ∧
        ∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
          ContinuousOn (fun x => ∫ g, f g ∂(νT x)) K) :
    ∃ K : ℕ → Set Work.EKLContract.X3,
      (∀ m, IsCompact (K m)) ∧ (∀ m, K m ⊆ XT) ∧ Monotone K ∧
      (∀ m, μ (K m)ᶜ < (((m + 1 : ℕ) : ENNReal))⁻¹) ∧
      (∀ m, ∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
          ContinuousOn (fun x => ∫ g, f g ∂(νT x)) (K m)) := by
  classical
  -- `1/(m+1) > 0` in `ℝ≥0∞`, so `hU6` applies at each level.
  have hpos : ∀ m : ℕ, (0 : ENNReal) < (((m + 1 : ℕ) : ENNReal))⁻¹ := by
    intro m
    rw [ENNReal.inv_pos]
    exact ENNReal.natCast_ne_top (m + 1)
  choose A hAc hAsub hAμ hAcont using fun m ↦ hU6 _ (hpos m)
  -- The accumulating family: `K m = ⋃_{i ≤ m} A i`.
  refine ⟨fun m ↦ ⋃ i : {i : ℕ // i ≤ m}, A i.1, ?_, ?_, ?_, ?_, ?_⟩
  · -- compactness: a finite union of compact sets
    intro m
    haveI : Finite {i : ℕ // i ≤ m} := (Set.finite_Iic m).to_subtype
    exact isCompact_iUnion fun i ↦ hAc i.1
  · -- containment in `XT`
    intro m
    exact Set.iUnion_subset fun i ↦ hAsub i.1
  · -- monotonicity
    intro m n hmn x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨⟨i.1, le_trans i.2 hmn⟩, hi⟩
  · -- the measure estimate: the complement of the union sits inside `(A m)ᶜ`
    intro m
    refine lt_of_le_of_lt (measure_mono ?_) (hAμ m)
    intro x hx
    simp only [Set.mem_compl_iff] at hx ⊢
    intro hxm
    exact hx (Set.mem_iUnion.mpr ⟨⟨m, le_rfl⟩, hxm⟩)
  · -- continuity on the finite union
    intro m f
    haveI : Finite {i : ℕ // i ≤ m} := (Set.finite_Iic m).to_subtype
    exact continuousOn_iUnion_of_isCompact (fun i ↦ hAc i.1) (fun i ↦ hAcont i.1 f)

end Work.EKLProd
