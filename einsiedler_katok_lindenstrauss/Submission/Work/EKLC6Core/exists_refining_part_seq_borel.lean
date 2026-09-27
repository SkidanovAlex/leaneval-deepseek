import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.leafwise_acovariant
import Submission.Work.EKLC6Core.atom_iSup_comap_iterate_eq
import Submission.Work.EKLComp.JacRefiningGenSeq

/-!
# `Work.EKLC6Core.exists_refining_part_seq_borel`

The **corrected** form of `Work.EKLC6Core.exists_refining_part_seq`: a refining sequence of
finite partitions of `X₃ = SL₃(ℝ)/SL₃(ℤ)` whose generated σ-algebras are sub-σ-algebras of a
given countably generated σ-algebra `S.m`, and whose atoms shrink to the atoms of `S.m`.

The correction is the hypothesis `S.m ≤ borel X₃`.  It is not a convenience: `FinPart X₃` is
`FinPart` for the *ambient* σ-algebra of `X₃` (`instMeasurableSpaceX3 = borel X₃`), so every cell
of every `P n` must be a **Borel** set, while `partSigma (P n) ≤ S.m` says it must also be
`S.m`-measurable.  For a countably generated `S.m` which is *not* contained in `borel X₃` — e.g.
`S.m = generateFrom {A}` for a non-Borel `A`, whose only measurable sets are `∅, A, Aᶜ, univ` and
whose atoms are `A` and `Aᶜ` — the two requirements force every cell to be `∅` or `univ`, so the
atoms of `partSigma (P n)` are all of `X₃` and can never shrink to `A`; the statement without
`S.m ≤ borel X₃` is therefore false.  In the intended application `S.m` *is* a plaque algebra
(`IsPlaqueAlgebra U Z S.m` carries `S.m ≤ borel X₃` as its first field), so the correction loses
nothing there.

The proof is short because the two halves already exist in the workspace:

* `exists_generating_sequence_of_countablyGenerated` turns countable generation into a sequence
  `f` of `S.m`-measurable sets with `generateFrom (range f) = S.m`; combined with `S.m ≤ borel X₃`
  the sets `f n` are Borel, so the membership partitions `Work.EKLComp.memPartitionFinPart f · n`
  (JacRefiningGenSeq.lean) are `FinPart`s for the *ambient* Borel instance, refine one another,
  generate `S.m` and satisfy `partSigma ≤ S.m`;
* `Work.EKLC6Core.atom_iSup_eq` identifies `⋂ n, atom (σ (P n)) x` with `atom (⨆ n, σ (P n)) x`.
-/

open MeasureTheory

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- A countably generated σ-algebra on `X₃` admits a sequence of measurable sets whose range
generates it. -/
theorem exists_generating_sequence_of_countablyGenerated (m : MeasurableSpace X3)
    (hgen : ∃ b : Set (Set X3), b.Countable ∧ m = MeasurableSpace.generateFrom b) :
    ∃ f : ℕ → Set X3, (∀ n, @MeasurableSet X3 m (f n)) ∧
      MeasurableSpace.generateFrom (Set.range f) = m := by
  obtain ⟨b, hb, hbm⟩ := hgen
  letI : MeasurableSpace X3 := m
  haveI : MeasurableSpace.CountablyGenerated X3 := ⟨b, hb, hbm⟩
  exact ⟨MeasurableSpace.natGeneratingSequence X3,
    fun n => MeasurableSpace.measurableSet_natGeneratingSequence n,
    MeasurableSpace.generateFrom_natGeneratingSequence X3⟩

/-- **The atoms of a refining sequence shrink to the atoms of the σ-algebra it generates.** -/
theorem iInter_atom_partSigma_eq_atom_iSup (P : ℕ → FinPart X3) (x : X3) :
    (⋂ n, atom (partSigma (P n)) x) = atom (⨆ n, partSigma (P n)) x := by
  rw [atom_iSup_eq]
  ext y
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]

/-- **`exists_refining_part_seq` with the missing hypothesis `S.m ≤ borel X₃`.**  For every
countably generated σ-algebra `S.m` contained in the Borel σ-algebra of `X₃` there is a refining
sequence of finite partitions `P n` (with *Borel* cells) such that `partSigma (P n) ≤ S.m` for all
`n` and the atoms of `partSigma (P n)` shrink, at every point, to the atom of `S.m`. -/
theorem exists_refining_part_seq_borel (S : Work.EKLRelCross.MSAlg) (hS : S.m ≤ borel X3)
    (hgen : ∃ b : Set (Set X3), b.Countable ∧ S.m = MeasurableSpace.generateFrom b) :
    ∃ P : ℕ → FinPart X3,
      (∀ n, partSigma (P n) ≤ S.m) ∧
      (∀ n, Refines (P (n + 1)) (P n)) ∧
      (∀ x : X3, (⋂ n, atom (partSigma (P n)) x) = atom S.m x) := by
  obtain ⟨f, hfm, hfgen⟩ := exists_generating_sequence_of_countablyGenerated S.m hgen
  -- `S.m ≤ borel X₃` makes the generators Borel, so the membership partitions are `FinPart`s for
  -- the ambient Borel instance.
  have hfB : ∀ n, MeasurableSet (f n) := fun n => hS _ (hfm n)
  let P : ℕ → FinPart X3 := fun n => Work.EKLComp.memPartitionFinPart f hfB n
  have hPpart : ∀ n, partSigma (P n) = MeasurableSpace.generateFrom (memPartition f n) :=
    fun n => Work.EKLComp.partSigma_memPartitionFinPart f hfB n
  have hPref : ∀ n, Refines (P (n + 1)) (P n) :=
    fun n => Work.EKLComp.refines_memPartitionFinPart f hfB n
  have hPsup : (⨆ n, partSigma (P n)) = S.m := by
    have hsig : (⨆ n, partSigma (P n)) = ⨆ n, MeasurableSpace.generateFrom (memPartition f n) :=
      iSup_congr hPpart
    rw [hsig, MeasurableSpace.iSup_generateFrom (fun n => memPartition f n),
      MeasurableSpace.generateFrom_iUnion_memPartition f, hfgen]
  refine ⟨P, ?_, hPref, fun x => ?_⟩
  · intro n
    rw [hPpart n]
    exact (MeasurableSpace.generateFrom_memPartition_le_range f n).trans_eq hfgen
  · rw [iInter_atom_partSigma_eq_atom_iSup P x, hPsup]

end Work.EKLC6Core
