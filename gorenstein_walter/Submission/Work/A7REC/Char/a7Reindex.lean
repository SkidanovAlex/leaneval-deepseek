/-
Area `A7REC`, file `Char/a7Reindex.lean`: **B3**, the reindexing step of the p11 bridge
(`Submission/Work/A7REC/Char/Bridge.lean`, `A7ReindexProp`).

Given an injective enumeration `ι : Fin n → Irr G` of the non-trivial irreducibles that occur in
`Δ_π, Δ_A, Δ_B`, with every other non-trivial irreducible `χ` satisfying `χ(z) = 0`, the sum

  `∑_{χ ≠ 1} χ(z)² χ(x) / χ(1)`

collapses onto the range of `ι`: the terms with `χ ∉ range ι` vanish because `χ(z) = 0`, and on
`rangeι` the sum is reindexed along the injection `ι`.  Finally the complex sum is the cast of a
rational sum because all the values involved are (casts of) rationals:
`χ(z) = b i - 2·a i`, `χ(x) = v i`, `χ(1) = f i`.

The proof is a `Finset.sum_subset` (support reduction) followed by `Finset.sum_image` (reindexing
along an injection) and the cast lemma `Rat.cast_sum`.
-/
import Mathlib
import Submission.Work.A7REC.Char.Bridge

namespace Work.A7REC.Char

open OddOrder.RepresentationTheory

theorem a7Reindex : Work.A7REC.A7ReindexProp := by
  intro G _ _ z x n ι f a b v hinj hne hzero hf hz hx
  classical
  -- Name the trivial irreducible and the summand.
  set t : IrreducibleCharacter G := trivialIrreducibleCharacter G
  set φ : IrreducibleCharacter G → ℂ :=
    fun χ => ((χ : ClassFunction G ℂ) z) ^ 2 * (χ : ClassFunction G ℂ) x /
      (χ : ClassFunction G ℂ) 1 with hφ
  -- The range of `ι` consists of non-trivial irreducibles, hence lies in the summation index set.
  have himg_sub : Finset.univ.image ι ⊆ Finset.univ.erase t := by
    intro χ hχ
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hχ
    obtain ⟨i, rfl⟩ := hχ
    rw [Finset.mem_erase]
    exact ⟨hne i, Finset.mem_univ _⟩
  -- Every summand outside the range of `ι` vanishes, because `χ(z) = 0` there.
  have hzero' : ∀ χ ∈ Finset.univ.erase t, χ ∉ Finset.univ.image ι → φ χ = 0 := by
    intro χ hχ hχim
    have hχne : χ ≠ t := (Finset.mem_erase.mp hχ).1
    have hχz : (χ : ClassFunction G ℂ) z = 0 := by
      apply hzero χ hχne
      intro hmem
      exact hχim (by
        rw [Finset.mem_image]
        obtain ⟨i, hi⟩ := hmem
        exact ⟨i, Finset.mem_univ i, hi⟩)
    simp only [hφ]
    simp [hχz]
  -- Termwise evaluation of the summand on the range of `ι`.
  have hterm : ∀ i, φ (ι i) = ((b i - 2 * a i : ℂ) ^ 2 * (v i : ℂ)) / (f i : ℂ) := by
    intro i
    have hA := hf i
    have hB := hz i
    have hC := hx i
    simp only [hφ]
    rw [hA, hB, hC]
  -- Support reduction to `range ι`, then reindexing along the injection `ι`.
  have hkey : ∑ χ ∈ Finset.univ.erase t, φ χ
      = ∑ i, ((b i - 2 * a i : ℂ) ^ 2 * (v i : ℂ)) / (f i : ℂ) := by
    rw [← Finset.sum_subset himg_sub hzero']
    rw [Finset.sum_image (fun p _ q _ h => hinj h)]
    exact Finset.sum_congr rfl (fun i _ => hterm i)
  -- The remaining complex sum is the cast of the corresponding rational sum.
  have hcast : ((∑ i, ((b i - 2 * a i) ^ 2 * v i : ℚ) / (f i : ℚ) : ℚ) : ℂ)
      = ∑ i, ((b i - 2 * a i : ℂ) ^ 2 * (v i : ℂ)) / (f i : ℂ) := by
    rw [Rat.cast_sum]
    exact Finset.sum_congr rfl (fun i _ => by push_cast; ring)
  rw [hkey, hcast]

end Work.A7REC.Char
