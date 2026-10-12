import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.PotSplitDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.PotWordUBlockSplit`

The block-splitting identity for the multiplicative potential word `potWordU` of FS
`eq:Def_HB`: the `(k+j)`-particle word at a configuration `x` is the sum of the two
block words at `firstBlock x` and `lastBlock x` **plus** the cross-pair interaction
`Σ_{i : Fin k} Σ_{i' : Fin j} wLoc ℓ v 0 (x_i) (x_{i'})`.

The only non-trivial ingredient is the combinatorial splitting of the sum over
unordered pairs `i < j` of `Fin (k+j)` into pairs inside the first block, pairs inside
the second block, and cross pairs; that is `Submission.BoseGases.sum_pairs_block_split`.
-/

open scoped BigOperators

namespace Work.BoseFixR

/-- A sum over the unordered pairs `i < j` of `Fin N` (a sum over the subtype
`{ij : Fin N × Fin N // ij.1 < ij.2}`) as a sum over the filtered `Finset`. -/
lemma pairSubtype_eq_filter {N : ℕ} (f : Fin N × Fin N → ℝ) :
    (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, f ij.1) =
      ∑ ij ∈ (Finset.univ.filter (fun ij : Fin N × Fin N => ij.1 < ij.2)), f ij := by
  exact (Finset.sum_subtype (Finset.univ.filter (fun ij : Fin N × Fin N => ij.1 < ij.2))
    (fun x => by simp) (f := f)).symm

/-- **The pair-sum block split**: the sum over the unordered pairs `i < j` of
`Fin (k+j)` splits into the pairs inside `Fin k` (embedded by `Fin.castAdd j`), the pairs
inside `Fin j` (embedded by `Fin.natAdd k`), and the cross pairs (first block, second
block). -/
lemma pairSubtype_split {k j : ℕ} (f : Fin (k + j) × Fin (k + j) → ℝ) :
    (∑ ij : {ij : Fin (k + j) × Fin (k + j) | ij.1 < ij.2}, f ij.1)
      = (∑ ij : {ij : Fin k × Fin k | ij.1 < ij.2},
            f (Fin.castAdd j ij.1.1, Fin.castAdd j ij.1.2))
        + (∑ ij : {ij : Fin j × Fin j | ij.1 < ij.2},
            f (Fin.natAdd k ij.1.1, Fin.natAdd k ij.1.2))
        + ∑ i : Fin k, ∑ i' : Fin j, f (Fin.castAdd j i, Fin.natAdd k i') := by
  rw [pairSubtype_eq_filter f,
    Submission.BoseGases.sum_pairs_block_split (fun a b => f (a, b))]
  rw [← pairSubtype_eq_filter (fun p : Fin k × Fin k => f (Fin.castAdd j p.1, Fin.castAdd j p.2)),
    ← pairSubtype_eq_filter (fun p : Fin j × Fin j => f (Fin.natAdd k p.1, Fin.natAdd k p.2))]

theorem PotWordUBlockSplit {k j : ℕ} {v g : EuclideanSpace ℝ (Fin 3) → ℝ} {ℓ μ : ℝ}
    (x : Submission.BoseGases.X (k + j)) :
    Work.BoseKinLoc.potWordU (k + j) v g ℓ μ 0 x
      = Work.BoseKinLoc.potWordU k v g ℓ μ 0 (Submission.BoseGases.firstBlock k j x)
        + Work.BoseKinLoc.potWordU j v g ℓ μ 0 (Submission.BoseGases.lastBlock k j x)
        + ∑ i : Fin k, ∑ i' : Fin j,
            Submission.BoseGases.wLoc ℓ v 0 (Submission.BoseGases.firstBlock k j x i)
              (Submission.BoseGases.lastBlock k j x i') := by
  simp only [Work.BoseKinLoc.potWordU, Submission.BoseGases.firstBlock,
    Submission.BoseGases.lastBlock]
  rw [Fin.sum_univ_add (f := fun i : Fin (k + j) => ∫ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.wLoc ℓ g 0 (x i) y)]
  rw [pairSubtype_split (fun p : Fin (k + j) × Fin (k + j) =>
        Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))]
  ring

end Work.BoseFixR
