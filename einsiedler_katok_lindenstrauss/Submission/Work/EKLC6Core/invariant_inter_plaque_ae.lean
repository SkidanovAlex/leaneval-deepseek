import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLC6Core.hopf_saturate
import Submission.Work.EKLC6Core.borel_atom_saturated_measurable

/-!
# `Work.EKLC6Core.invariant_inter_plaque_ae`

Let `T = aDiag t ·` preserve the probability measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, let `Z ⊆ X₃`
and let `m` be a `Uminus t`-**plaque algebra** on `Z` (`IsPlaqueAlgebra`): a countably generated
sub-`σ`-algebra of the Borel algebra on `X₃`, with `Z ∈ m`, whose atoms inside `Z` are open,
bounded pieces of `Uminus t`-orbits and are contained in `Z`.

Then every `T`-invariant measurable set `E` admits an `m`-measurable representative of `E ∩ Z`:
there is `E'` with `MeasurableSet[m] E'` and `μ (E' Δ (E ∩ Z)) = 0`.

## Proof

A set measurable for `MeasurableSpace.invariants T` is, by definition of that `σ`-algebra, Borel
measurable and *strictly* `T`-invariant.  The Hopf argument (`hopf_saturate`, Pisa 7.20) upgrades
`E` to a Borel set `C'` with `μ (E Δ C') = 0` which is invariant under the whole stable
horospherical subgroup: `u • C' = C'` for every `u ∈ Uminus t`.

The representative is `E' := C' ∩ Z`.  It is Borel (`Z` is Borel because `m ≤ borel X₃`), and it
is *atom-saturated*: for `x ∈ C' ∩ Z` and `y ∈ [x]_m` we have `y = u • x` with `u ∈ Uminus t`
(the atoms inside `Z` lie in a single `Uminus t`-orbit), hence `y ∈ C'` by `Uminus t`-invariance,
and `y ∈ Z` because the atom of a point of `Z` is contained in `Z`.  A Borel atom-saturated set
is `m`-measurable by `borel_atom_saturated_measurable` (Lusin separation).

Finally `E ∩ Z` and `C' ∩ Z` differ only inside `E Δ C'`, so their symmetric difference is null.
-/

open MeasureTheory

noncomputable section

namespace Work.EKLC6Core

theorem invariant_inter_plaque_ae
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (Z : Set Work.EKLContract.X3) (M : {𝔪 : MeasurableSpace Work.EKLContract.X3 //
      Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z 𝔪}) :
    ∀ E : Set Work.EKLContract.X3,
      @MeasurableSet Work.EKLContract.X3
        (MeasurableSpace.invariants (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)) E →
      ∃ E' : Set Work.EKLContract.X3, @MeasurableSet Work.EKLContract.X3 (M.1) E' ∧
        μ ((E' \ (E ∩ Z)) ∪ ((E ∩ Z) \ E')) = 0 := by
  intro E hE
  -- `E` is Borel and strictly `T`-invariant.
  obtain ⟨hEmeas, hEinv⟩ := MeasurableSpace.measurableSet_invariants.mp hE
  -- Hopf: an a.e. equal, strictly `Uminus t`-invariant Borel representative `C'` of `E`.
  obtain ⟨C', hC'meas, hC'inv, hC'diff1, hC'diff2⟩ := hopf_saturate t hmp hEmeas hEinv
  have hZborel : MeasurableSet Z := M.2.1 Z M.2.2.2.1
  have hgen : @MeasurableSpace.CountablyGenerated Work.EKLContract.X3 M.1 :=
    @MeasurableSpace.CountablyGenerated.mk Work.EKLContract.X3 M.1 M.2.2.1
  refine ⟨C' ∩ Z, ?_, ?_⟩
  · -- `C' ∩ Z` is Borel and atom-saturated, hence `m`-measurable.
    refine borel_atom_saturated_measurable (m := M.1) M.2.1 hgen (hC'meas.inter hZborel) ?_
    intro x hx
    obtain ⟨hxC', hxZ⟩ := hx
    obtain ⟨hatomZ, hatomU, -, -⟩ := M.2.2.2.2 x hxZ
    intro y hy
    refine ⟨?_, hatomZ hy⟩
    obtain ⟨u, hu, rfl⟩ := hatomU hy
    rw [← hC'inv u hu]
    exact ⟨x, hxC', rfl⟩
  · -- `C' ∩ Z` and `E ∩ Z` differ only inside `E Δ C'`.
    have hsub : ((C' ∩ Z) \ (E ∩ Z)) ∪ ((E ∩ Z) \ (C' ∩ Z)) ⊆ (C' \ E) ∪ (E \ C') := by
      intro y hy
      rcases hy with h | h
      · rw [Set.mem_sdiff, Set.mem_inter_iff] at h
        exact Or.inl ⟨h.1.1, fun hyE => h.2 ⟨hyE, h.1.2⟩⟩
      · rw [Set.mem_sdiff, Set.mem_inter_iff] at h
        exact Or.inr ⟨h.1.1, fun hyC' => h.2 ⟨hyC', h.1.2⟩⟩
    have h0 : μ ((C' \ E) ∪ (E \ C')) = 0 := measure_union_null hC'diff2 hC'diff1
    have hle : μ (((C' ∩ Z) \ (E ∩ Z)) ∪ ((E ∩ Z) \ (C' ∩ Z))) ≤ μ ((C' \ E) ∪ (E \ C')) :=
      measure_mono hsub
    rw [h0] at hle
    exact le_bot_iff.mp hle

end Work.EKLC6Core

end
