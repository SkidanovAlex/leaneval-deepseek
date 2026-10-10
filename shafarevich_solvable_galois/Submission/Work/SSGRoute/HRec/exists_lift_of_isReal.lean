import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Step 1 of the reverse Artin–Schreier dictionary

A real infinite place `w` of a number field `k` gives a real embedding
`φ = NumberField.InfinitePlace.embedding_of_isReal hw : k →+* ℝ`; composing with `ℝ ↪ ℂ` and
extending along an algebraic closure `Ω/k` by `ComplexEmbedding.lift` produces an embedding
`Ψ : Ω →+* ℂ` whose restriction to `k` is `φ`.

This is the first step of the construction of the involution attached to a real place
(`Work.SSGRoute.HRec.NOTES_exists_conjInv_kummerChar.md`): the next steps feed `Ψ` and
`conjugate Ψ` into `NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq`, exactly as in the
private `exists_involution_extension_omega_aux` of `Submission/Work/SSGRoute/glue_infinite_place.lean`.
-/

open NumberField

noncomputable section

namespace Work.SSGRoute.HRec

/-- A real infinite place of a number field lifts to a complex embedding of any algebraic closure,
extending the real point of the place. -/
theorem exists_lift_of_isReal {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (w : NumberField.InfinitePlace k) (hw : w.IsReal) :
    ∃ Ψ : Ω →+* ℂ, ∀ a : k,
      Ψ (algebraMap k Ω a) = (((NumberField.InfinitePlace.embedding_of_isReal hw) a : ℝ) : ℂ) := by
  refine ⟨NumberField.ComplexEmbedding.lift Ω
    ((algebraMap ℝ ℂ).comp (NumberField.InfinitePlace.embedding_of_isReal hw)), ?_⟩
  intro a
  rw [NumberField.ComplexEmbedding.lift_algebraMap_apply]
  rfl

end Work.SSGRoute.HRec
