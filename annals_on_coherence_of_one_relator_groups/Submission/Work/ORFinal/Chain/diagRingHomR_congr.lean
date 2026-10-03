/-
# `K`-linear maps commuting with the diagonal right action are `K[Gᵐᵒᵖ]`-linear

`Work.ORFlatness.diagRingHomR` makes `S ⊗[K] X` a `K[Gᵐᵒᵖ]`-module (equivalently, a right
`K[G]`-module) by the diagonal action `(s ⊗ x)·g = (s·φ g) ⊗ (g⁻¹ • x)`.

The present lemma records the elementary but essential fact that a `K`-linear map
`f : S ⊗[K] X₁ → S ⊗[K] X₂` which commutes with each of the generators `diagLinR g`
automatically commutes with the action of *every* element `b` of the group algebra
`K[Gᵐᵒᵖ]`, i.e. it is `K[Gᵐᵒᵖ]`-linear for the two diagonal structures.

This is proved by `K`-linearity/induction on `b`: the group-algebra elements are spanned by the
monomials `single m c`, on which `diagRingHomR` acts by `c • diagLinR m.unop`; `f` then passes
through `c •` (it is `K`-linear) and through `diagLinR m.unop` (the hypothesis `hf`).
-/
import Mathlib
import Submission.Work.ORFlatness.DiagonalRight

namespace Work.ORFinal.Chain

universe u

/-- The value of `diagRingHomR` on a monomial `single m c` of `K[Gᵐᵒᵖ]` (with `m : Gᵐᵒᵖ`),
reindexing `Work.ORFlatness.diagRingHomR_single` from generators of `G` to elements of `Gᵐᵒᵖ`. -/
theorem diagRingHomR_single_op
    (K : Type u) [CommRing K] (G : Type u) [Group G]
    (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K G →ₐ[K] S)
    (X : Type u) [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [IsScalarTower K (MonoidAlgebra K G) X] [SMulCommClass K (MonoidAlgebra K G) X]
    (m : Gᵐᵒᵖ) (c : K) :
    Work.ORFlatness.diagRingHomR K G S φ X (MonoidAlgebra.single m c) =
      c • Work.ORFlatness.diagLinR K G S φ X m.unop := by
  rw [Work.ORFlatness.diagRingHomR, MonoidAlgebra.lift_single]
  rfl

theorem diagRingHomR_congr
    (K : Type u) [CommRing K] (G : Type u) [Group G]
    (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K G →ₐ[K] S)
    (X₁ : Type u) [AddCommGroup X₁] [Module K X₁] [Module (MonoidAlgebra K G) X₁]
    [IsScalarTower K (MonoidAlgebra K G) X₁] [SMulCommClass K (MonoidAlgebra K G) X₁]
    (X₂ : Type u) [AddCommGroup X₂] [Module K X₂] [Module (MonoidAlgebra K G) X₂]
    [IsScalarTower K (MonoidAlgebra K G) X₂] [SMulCommClass K (MonoidAlgebra K G) X₂]
    (f : (TensorProduct K S X₁) →ₗ[K] (TensorProduct K S X₂))
    (hf : ∀ g : G,
      f.comp (Work.ORFlatness.diagLinR K G S φ X₁ g) =
        (Work.ORFlatness.diagLinR K G S φ X₂ g).comp f)
    (b : MonoidAlgebra K Gᵐᵒᵖ) (z : TensorProduct K S X₁) :
    f (Work.ORFlatness.diagRingHomR K G S φ X₁ b z) =
      Work.ORFlatness.diagRingHomR K G S φ X₂ b (f z) := by
  induction b using MonoidAlgebra.induction_on with
  | of m =>
      rw [MonoidAlgebra.of_apply, diagRingHomR_single_op K G S φ X₁,
        diagRingHomR_single_op K G S φ X₂]
      simp only [one_smul]
      simpa [LinearMap.comp_apply] using congrArg (fun L => L z) (hf m.unop)
  | add r s hr hs =>
      simp only [map_add, LinearMap.add_apply, hr, hs]
  | smul c r hr =>
      simp only [map_smul, LinearMap.smul_apply, hr]

end Work.ORFinal.Chain
