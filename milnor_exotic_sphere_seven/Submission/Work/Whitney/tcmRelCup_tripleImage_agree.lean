import Mathlib
import Submission.Work.Whitney.TripleRel
import Submission.Work.Whitney.TCMQDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Whitney

open Work.Cohomology
open CategoryTheory AlgebraicTopology CategoryTheory.Limits

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-
# The two bracketings of the triple product have the same image in `H^*(X,A+B+C)`

Cochain-level input for the associativity of the canonical relative–relative cup: the two
bracketed triple products have the same image in the three-fold intersection complex
`Work.Whitney.pd3CohR`, up to the degree transport `Nat.add_assoc`.

Note on the set bookkeeping.  `pd3InclRelR X A B C` has source `C^*(X,(A∪B)∪C)` (this is how
`Work.Whitney.pd3InclRelR` is defined: Lean parses `A ∪ B ∪ C` as `(A ∪ B) ∪ C`), while the
right-hand side of the association lives over `A ∪ (B ∪ C)`.  The transport between the two is the
type-level cast along `Set.union_assoc A B C`; it cannot be handled by `cases` (the two set
carriers `fun x => (x ∈ A ∨ x ∈ B) ∨ x ∈ C` and `fun x => x ∈ A ∨ (x ∈ B ∨ x ∈ C)` are only
*propositionally* equal), so it has to be handled through `relCohMap (ContinuousMap.id X)` together
with the equality of the two membership proofs (`relCohMap_hcongrA`-style).
-/

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- Cupping an element of the `A+B` complex with an element of `C^*(X,C)` lands in the three-fold
intersection `C^*(X,A+B+C)`. -/
lemma cup_mem_pd3KernR (A B C : Set X) (m n : ℕ)
    (y : (pdABCohR (R := ℤ) (TopCat.of X) A B).X m)
    (γ : (relComplex ℤ (TopCat.of X) C).X n) :
    cup ℤ (TopCat.toSSet.obj (TopCat.of X)) y.1 γ.1 ∈ pd3KernR (TopCat.of X) A B C (m + n) := by
  rw [pd3KernR, Submodule.mem_inf, Submodule.mem_inf]
  exact ⟨⟨cup_mem_relKern_left ℤ (TopCat.of X) A (Submodule.mem_inf.mp y.2).1 γ.1,
    cup_mem_relKern_left ℤ (TopCat.of X) B (Submodule.mem_inf.mp y.2).2 γ.1⟩,
    cup_mem_relKern_right ℤ (TopCat.of X) C y.1 γ.2⟩

/-- Cupping an element of `C^*(X,A)` with an element of the `B+C` complex lands in the three-fold
intersection `C^*(X,A+B+C)`. -/
lemma cup_mem_pd3KernR' (A B C : Set X) (m n : ℕ)
    (α : (relComplex ℤ (TopCat.of X) A).X m)
    (y : (pdABCohR (R := ℤ) (TopCat.of X) B C).X n) :
    cup ℤ (TopCat.toSSet.obj (TopCat.of X)) α.1 y.1 ∈ pd3KernR (TopCat.of X) A B C (m + n) := by
  rw [pd3KernR, Submodule.mem_inf, Submodule.mem_inf]
  exact ⟨⟨cup_mem_relKern_left ℤ (TopCat.of X) A α.2 y.1,
    cup_mem_relKern_right ℤ (TopCat.of X) B α.1 (Submodule.mem_inf.mp y.2).1⟩,
    cup_mem_relKern_right ℤ (TopCat.of X) C α.1 (Submodule.mem_inf.mp y.2).2⟩

/-- **The factorisation of `pd3InclRelR` through the pair `(A∪B, C)`**, as an identity of cochain
maps: both sides have source `C^*(X,(A∪B)∪C)` (the source of `Work.Whitney.pd3InclRelR`), so this
is a `rfl`-level statement about inclusions of submodules. -/
lemma pd3InclRelR_factor_left_cm (A B C : Set X) :
    pd3InclRelR (TopCat.of X) A B C
      = pdABInclRelR (R := ℤ) (TopCat.of X) (A ∪ B) C ≫
        pdABCOhR_to_pd3CohR_left (TopCat.of X) A B C := by
  apply HomologicalComplex.hom_ext
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  rfl

/-- The cohomology-level form of `pd3InclRelR_factor_left_cm`. -/
lemma pd3InclRelR_factor_left (A B C : Set X) (n : ℕ)
    (x : Work.Thom.RelCoh ℤ n X ((A ∪ B) ∪ C)) :
    (HomologicalComplex.homologyMap (pd3InclRelR (TopCat.of X) A B C) n).hom x
      = (HomologicalComplex.homologyMap
            (pdABCOhR_to_pd3CohR_left (TopCat.of X) A B C) n).hom
          ((HomologicalComplex.homologyMap
            (pdABInclRelR (R := ℤ) (TopCat.of X) (A ∪ B) C) n).hom x) := by
  rw [pd3InclRelR_factor_left_cm, HomologicalComplex.homologyMap_comp]
  rfl

/-- The two transports of a class (along an equality of degrees and along an equality of the sets)
commute. -/
lemma eqRec_swap {α β : Type*} {P : α → β → Type*} {a a' : α} {b b' : β}
    (h₁ : a = a') (h₂ : b = b') (x : P a b) :
    h₂ ▸ (h₁ ▸ x) = h₁ ▸ (h₂ ▸ x) := by
  cases h₁
  cases h₂
  rfl

end

end Work.Whitney
