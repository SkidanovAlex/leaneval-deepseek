import Mathlib
import Submission.Work.SSGRoute.HRec.exists_lift_isReal_comp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Step 3 of the reverse Artin–Schreier dictionary

The lift `Ψ : Ω →+* ℂ` of a real place `w` (steps 1–2) is real on `k`, so
`NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq` produces `σ` with
`Ψ ∘ σ = star ∘ Ψ`; conjugating, `c := σ.symm` is an involution of `Ω ≃ₐ[k] Ω` with
`Ψ (c x) = star (Ψ x)` for all `x`.  This is the conjugation at the real place `w`; steps 4–5
(`AlgEquiv.ofRingEquiv` packaging for `k`-linearity, and the characterisation
`a ∈ normSet c ↔ ¬ IsNegAt w a`) complete `Work.SSGRoute.HRec.NOTES_exists_conjInv_kummerChar.md`.
-/

open NumberField

noncomputable section

namespace Work.SSGRoute.HRec

/-- The complex conjugation at a real place, as an involution of the absolute Galois group. -/
theorem exists_involution_conj_comp {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (w : NumberField.InfinitePlace k) (hw : w.IsReal) :
    ∃ (Ψ : Ω →+* ℂ) (c : Ω ≃ₐ[k] Ω),
      (∀ a : k, Ψ (algebraMap k Ω a) =
        (((NumberField.InfinitePlace.embedding_of_isReal hw) a : ℝ) : ℂ)) ∧
      c ^ 2 = 1 ∧ ∀ x : Ω, Ψ (c x) = starRingEnd ℂ (Ψ x) := by
  obtain ⟨Ψ, hreal, hΨ⟩ := exists_lift_isReal_comp (Ω := Ω) w hw
  obtain ⟨σ₁, hσ₁⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (K := Ω) (k := k)
    Ψ (NumberField.ComplexEmbedding.conjugate Ψ) (by
      rw [NumberField.ComplexEmbedding.conjugate_comp]
      exact hreal.symm)
  have hσ : Ψ.comp (↑(σ₁.symm) : Ω →+* Ω) = NumberField.ComplexEmbedding.conjugate Ψ := hσ₁
  have hIsConj : NumberField.ComplexEmbedding.IsConj (k := k) (K := Ω) Ψ σ₁.symm := hσ.symm
  refine ⟨Ψ, σ₁.symm, hΨ, ?_, ?_⟩
  · rw [pow_two]
    ext x
    rw [AlgEquiv.mul_apply, AlgEquiv.one_apply]
    exact NumberField.ComplexEmbedding.isConj_apply_apply hIsConj x
  · intro x
    exact RingHom.congr_fun hσ x

end Work.SSGRoute.HRec
