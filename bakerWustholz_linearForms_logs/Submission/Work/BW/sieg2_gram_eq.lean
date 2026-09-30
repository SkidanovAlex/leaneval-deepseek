import Mathlib
import Submission.Work.BW.sieg2Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Gram identity for the sharp Siegel step (`sieg2_gram_eq`)

In the mixed coordinates of `F^N` (see `Submission.Work.BW.sieg2Defs`), the ordinary Euclidean
dot product of two coordinate vectors can be written either as a plain sum over the coordinates
`Fin N × mixedEmbedding.index F`, or "geometrically" as `siegInner`, i.e. as a sum over the
infinite places of `F`, where a real place contributes the single real coordinate and a complex
place contributes the two real coordinates `re`, `im`.

The two descriptions agree because the index set of the standard orthonormal basis is
`mixedEmbedding.index F = {w // IsReal w} ⊕ ({w // IsComplex w} × Fin 2)`, the disjoint union of
the real places (one coordinate each) and the complex places (two coordinates each), while the
sum in `siegInner` ranges over `InfinitePlace F` with the same real/complex case split.
-/

open NumberField
open scoped Classical

namespace Work.BW

/-- For any `g : mixedEmbedding.index F → ℝ`, summing over the basis index set is the same as
summing over the infinite places, expanding each complex place into its two real coordinates. -/
theorem sieg2_sum_index_eq {F : Type*} [Field F] [NumberField F]
    [Fintype (NumberField.mixedEmbedding.index F)]
    (g : NumberField.mixedEmbedding.index F → ℝ) :
    (∑ c : NumberField.mixedEmbedding.index F, g c)
      = ∑ w : NumberField.InfinitePlace F,
          if hw : NumberField.InfinitePlace.IsReal w then g (Sum.inl ⟨w, hw⟩)
          else g (Sum.inr (⟨w, NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw⟩, 0))
             + g (Sum.inr (⟨w, NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw⟩, 1)) := by
  -- `univ` on the index set is the disjoint union of the real and complex part.
  have hcongr : (@Finset.univ (NumberField.mixedEmbedding.index F) _ : Finset _)
      = (Finset.univ : Finset {w : NumberField.InfinitePlace F // w.IsReal}).disjSum
        (Finset.univ : Finset ({w : NumberField.InfinitePlace F // w.IsComplex} × Fin 2)) := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_disjSum, true_and]
    refine ⟨fun _ => ?_, fun _ => trivial⟩
    cases x with
    | inl a => exact Or.inl ⟨a, rfl⟩
    | inr b => exact Or.inr ⟨b, rfl⟩
  rw [hcongr, Finset.sum_disjSum, NumberField.InfinitePlace.sum_eq_sum_add_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    rw [dite_eq_left a.2]
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro z _
    rw [dite_eq_right (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr z.2),
      Fin.sum_univ_two]

theorem sieg2_gram_eq {F : Type*} [Field F] [NumberField F]
    [Fintype (NumberField.mixedEmbedding.index F)]
    [DecidableEq (NumberField.mixedEmbedding.index F)]
    {N K : ℕ} (v : Fin K → (Fin N → NumberField.RingOfIntegers F)) (i j : Fin K) :
    (∑ p : Fin N × NumberField.mixedEmbedding.index F,
        Work.BW.siegCoord (v i) p.1 p.2 * Work.BW.siegCoord (v j) p.1 p.2)
      = Work.BW.siegInner (Work.BW.siegCoord (v i)) (Work.BW.siegCoord (v j)) := by
  rw [Fintype.sum_prod_type]
  simp only [Work.BW.siegInner]
  apply Finset.sum_congr rfl
  intro a _
  exact sieg2_sum_index_eq
    (fun c => Work.BW.siegCoord (v i) a c * Work.BW.siegCoord (v j) a c)

end Work.BW
