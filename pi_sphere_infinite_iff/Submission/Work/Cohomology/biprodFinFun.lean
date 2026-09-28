import Mathlib
import Submission.Work.Cohomology.Singular

namespace Work.Cohomology

open CategoryTheory Limits

/-- The linear equivalence sending a pair `(f, g)` to the function on `Fin (a + b)` obtained by
concatenating `f` and `g`.  This is the underlying map of the biproduct decomposition
`(Fin a → ℤ) ⊞ (Fin b → ℤ) ≅ (Fin (a + b) → ℤ)`. -/
noncomputable def finProdEquiv (a b : ℕ) :
    ((Fin a → ℤ) × (Fin b → ℤ)) ≃ₗ[ℤ] (Fin (a + b) → ℤ) where
  toFun p := Fin.append p.1 p.2
  invFun F := (F ∘ Fin.castAdd b, F ∘ Fin.natAdd a)
  left_inv p := by
    ext i <;> simp [Fin.append_left, Fin.append_right]
  right_inv F := by
    funext x
    refine Fin.addCases ?_ ?_ x
    · intro i; simp [Fin.append_left]
    · intro j; simp [Fin.append_right]
  map_add' p q := by
    funext x
    refine Fin.addCases ?_ ?_ x
    · intro i; simp [Fin.append_left]
    · intro j; simp [Fin.append_right]
  map_smul' c p := by
    funext x
    refine Fin.addCases ?_ ?_ x
    · intro i; simp [Fin.append_left]
    · intro j; simp [Fin.append_right]

/-- The biproduct of `Fin a → ℤ` and `Fin b → ℤ` is `Fin (a + b) → ℤ`. -/
theorem biprodFinFun (a b : ℕ) :
    Nonempty (ModuleCat.of ℤ (Fin a → ℤ) ⊞ ModuleCat.of ℤ (Fin b → ℤ) ≅
      ModuleCat.of ℤ (Fin (a + b) → ℤ)) :=
  ⟨(ModuleCat.biprodIsoProd _ _).trans (LinearEquiv.toModuleIso (finProdEquiv a b))⟩

end Work.Cohomology
