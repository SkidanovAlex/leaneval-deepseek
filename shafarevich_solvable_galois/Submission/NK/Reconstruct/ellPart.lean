import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.GroupTheory.Abelianization.Defs
import Submission.NK.Reconstruct.Gamma
import Submission.NK.Reconstruct.ellPrimary_mul_mem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The ℓ-primary part of a finite abelian group, and of the abelianisation of a finite level

This is the first piece of the object-level vocabulary of Shimizu's §4 (item (1) of the
reconstruction deliverable): the ℓ-part `Γ_{L,ℓ}` of the abelianisation `Gal(L/K)^{ab}` of a finite
Galois level, whose projective limit over the finite levels is `Γ_K = (G_K^{ab,(ℓ)})/torsion` and
whose ℓ-rank is `NK.Reconstruct.levelRank` / `ellRank`.

The closure step is `NK.Reconstruct.ellPrimary_mul_mem` (proved); the ℓ-rank of the ℓ-part agrees
with `ellRank` because the ℓ-torsion of `A` is the ℓ-torsion of its ℓ-part.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace NK.Reconstruct

/-- **The ℓ-primary part of a commutative group**: the subgroup of elements whose order divides some
power of `ℓ`.  For a finite abelian group this is its ℓ-primary component, i.e. Shimizu's
`Γ_{L,ℓ}` when `A = Gal(L/K)^{ab}`. -/
def ellPart (A : Type*) [CommGroup A] (ℓ : ℕ) : Subgroup A where
  carrier := {x : A | ∃ n : ℕ, x ^ (ℓ ^ n) = 1}
  mul_mem' := fun hx hy => ellPrimary_mul_mem ℓ hx hy
  one_mem' := ⟨0, by simp⟩
  inv_mem' := by
    rintro x ⟨n, hn⟩
    exact ⟨n, by rw [inv_pow, hn, inv_one]⟩

/-- Membership in the ℓ-primary part, unfolded. -/
theorem mem_ellPart_iff {A : Type*} [CommGroup A] (ℓ : ℕ) (x : A) :
    x ∈ ellPart A ℓ ↔ ∃ n : ℕ, x ^ (ℓ ^ n) = 1 := Iff.rfl

/-- **The ℓ-part of the abelianisation of a finite Galois level** — Shimizu's `Γ_{L,ℓ}` for the
level `L/K` (the objects whose projective limit is `Γ_K`). -/
abbrev LevelEllPart {K : Type*} [Field K] {K' : Type*} [Field K'] [Algebra K K']
    (L : IntermediateField K K') (ℓ : ℕ) : Subgroup (LevelAbelianization L) :=
  ellPart (LevelAbelianization L) ℓ

end NK.Reconstruct
