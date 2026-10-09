import Mathlib
import Submission.Work.SSGRoute.HRec.exists_lift_of_isReal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Step 2 of the reverse Artin–Schreier dictionary

The lift `Ψ : Ω →+* ℂ` of a real place `w` (step 1, `HRec.exists_lift_of_isReal`) is *real on `k`*:
because `Ψ` restricts to `((embedding_of_isReal hw ·) : ℝ) : ℂ`, complex conjugation fixes the
composite `Ψ.comp (algebraMap k Ω)` pointwise.

This is the hypothesis `hreal` that feeds `NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq`
in step 3 (see `Submission/Work/SSGRoute/HRec/NOTES_exists_conjInv_kummerChar.md`).
-/

open NumberField

noncomputable section

namespace Work.SSGRoute.HRec

/-- The lift of a real place to a complex embedding of an algebraic closure is real on the base
field. -/
theorem exists_lift_isReal_comp {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (w : NumberField.InfinitePlace k) (hw : w.IsReal) :
    ∃ Ψ : Ω →+* ℂ, NumberField.ComplexEmbedding.IsReal (Ψ.comp (algebraMap k Ω)) ∧
      ∀ a : k,
        Ψ (algebraMap k Ω a) = (((NumberField.InfinitePlace.embedding_of_isReal hw) a : ℝ) : ℂ) := by
  obtain ⟨Ψ, hΨ⟩ := exists_lift_of_isReal (Ω := Ω) w hw
  refine ⟨Ψ, ?_, hΨ⟩
  rw [NumberField.ComplexEmbedding.isReal_iff]
  ext a
  first
    | (simp only [RingHom.comp_apply, hΨ a, ComplexEmbedding.conjugate_coe_eq]
       exact Complex.conj_ofReal _)
    | (rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
       simp only [RingHom.comp_apply, hΨ a]
       exact Complex.conj_ofReal _)
    | simp [ComplexEmbedding.conjugate, Complex.conj_ofReal]

end Work.SSGRoute.HRec
