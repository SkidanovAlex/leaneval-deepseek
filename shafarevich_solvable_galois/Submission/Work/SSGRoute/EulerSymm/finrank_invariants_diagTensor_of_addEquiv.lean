import Mathlib
import Submission.Work.Shrinking.Basic
import Submission.Work.Shrinking.finite_tensorProduct_of_finite
import Submission.Work.CohomologicalShrinking.Models
import Submission.Work.SSGRoute.PTCore.invariantsSubmodule
import Submission.Work.SSGRoute.PTCore.finrank_invariants_equivariant
import Submission.Work.SSGRoute.PTCore.tensorProduct_congr_equivariant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Invariants of `A ⊗ N` only depend on `A` up to `A × C ≅ B × C`

Let `G` be a group, `p` a prime and `A`, `B`, `C`, `N` finite `𝔽_p[G]`-modules (with the
diagonal `G`-action on tensor products, `Work.Shrinking.instDistribMulActionTensorProduct`).
If there is a `G`-equivariant linear equivalence `A × C ≃ₗ B × C`, then the `G`-invariants of
`A ⊗ N` and of `B ⊗ N` have the same `𝔽_p`-dimension.

The proof is the additivity of the fixed-point dimension: applying `_ ⊗ N` to the given
equivariant equivalence gives a `G`-equivariant equivalence `(A × C) ⊗ N ≃ (B × C) ⊗ N`
(`TensorProduct.congr`), and the distributivity isomorphisms
`TensorProduct.prodLeft : (M₁ × M₂) ⊗ N ≃ (M₁ ⊗ N) × (M₂ ⊗ N)` are `G`-equivariant.  Since the
fixed points of a product are the product of the fixed points, both sides compute to
`dim (A ⊗ N)^G + dim (C ⊗ N)^G = dim (B ⊗ N)^G + dim (C ⊗ N)^G`, and the common summand
`dim (C ⊗ N)^G` cancels.
-/

namespace Work.SSGRoute.EulerSymm

set_option linter.style.haveILetI false

open scoped TensorProduct

variable {p : ℕ} {G : Type}

section Helpers

/-- For `𝔽_p[G]`-modules `M₁`, `M₂`, `N` the distributivity isomorphism
`TensorProduct.prodLeft : (M₁ × M₂) ⊗ N ≃ₗ (M₁ ⊗ N) × (M₂ ⊗ N)` is `G`-equivariant, the tensor
products carrying the diagonal action and the product the pointwise action. -/
theorem tensorProduct_prodLeft_equivariant_aux {M₁ M₂ N : Type} [Group G]
    [AddCommGroup M₁] [Module (ZMod p) M₁] [DistribMulAction G M₁] [SMulCommClass G (ZMod p) M₁]
    [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction G M₂] [SMulCommClass G (ZMod p) M₂]
    [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N] [SMulCommClass G (ZMod p) N] :
    ∀ (g : G) (x : TensorProduct (ZMod p) (M₁ × M₂) N),
      TensorProduct.prodLeft (ZMod p) (ZMod p) M₁ M₂ N (g • x)
        = g • TensorProduct.prodLeft (ZMod p) (ZMod p) M₁ M₂ N x := by
  intro g x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul y n =>
    obtain ⟨m₁, m₂⟩ := y
    simp
  | add x y hx hy => simp [hx, hy]

/-- The fixed points of a product of two `𝔽_p[G]`-modules are the product of the fixed points. -/
noncomputable def invariantsSubmoduleProdEquivAux [Group G] (V W : Type)
    [AddCommGroup V] [Module (ZMod p) V] [DistribMulAction G V] [SMulCommClass G (ZMod p) V]
    [AddCommGroup W] [Module (ZMod p) W] [DistribMulAction G W] [SMulCommClass G (ZMod p) W] :
    Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p) (V × W) ≃ₗ[ZMod p]
      Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p) V ×
        Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p) W where
  toFun x := (⟨x.1.1, fun g => by simpa using congrArg Prod.fst (x.2 g)⟩,
              ⟨x.1.2, fun g => by simpa using congrArg Prod.snd (x.2 g)⟩)
  invFun y := ⟨(y.1.1, y.2.1), fun g => by rw [Prod.smul_mk, y.1.2 g, y.2.2 g]⟩
  left_inv x := Subtype.ext rfl
  right_inv y := Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
  map_add' x y := rfl
  map_smul' c x := rfl

/-- **Dimension of the invariants of a product.**  For finite `𝔽_p[G]`-modules `V`, `W` the
`𝔽_p`-dimension of the invariants of `V × W` is the sum of the dimensions of the invariants
of the two factors. -/
theorem finrank_invariants_prod_aux [Fact p.Prime] [Group G] (V W : Type)
    [AddCommGroup V] [Module (ZMod p) V] [DistribMulAction G V] [SMulCommClass G (ZMod p) V]
    [AddCommGroup W] [Module (ZMod p) W] [DistribMulAction G W] [SMulCommClass G (ZMod p) W]
    [Finite V] [Finite W] :
    Module.finrank (ZMod p) ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p) (V × W)) =
      Module.finrank (ZMod p) ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p) V)
        + Module.finrank (ZMod p) ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p) W) := by
  rw [(invariantsSubmoduleProdEquivAux (p := p) (G := G) V W).finrank_eq, Module.finrank_prod]

end Helpers

theorem finrank_invariants_diagTensor_of_addEquiv (p : ℕ) [Fact p.Prime] (G : Type) [Group G]
    (A B C : Type)
    [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A] [SMulCommClass G (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B] [DistribMulAction G B] [SMulCommClass G (ZMod p) B]
    [AddCommGroup C] [Module (ZMod p) C] [DistribMulAction G C] [SMulCommClass G (ZMod p) C]
    [Finite A] [Finite B] [Finite C]
    (e : (A × C) ≃ₗ[ZMod p] (B × C))
    (he : ∀ (g : G) (x : A × C), e (g • x) = g • e x)
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N] [Finite N] :
    Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p) (TensorProduct (ZMod p) A N)) =
      Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p) (TensorProduct (ZMod p) B N)) := by
  -- finiteness of all the tensor products involved
  haveI hACN : Finite (TensorProduct (ZMod p) (A × C) N) :=
    Work.Shrinking.finite_tensorProduct_of_finite (ZMod p) (A × C) N
  haveI hBCN : Finite (TensorProduct (ZMod p) (B × C) N) :=
    Work.Shrinking.finite_tensorProduct_of_finite (ZMod p) (B × C) N
  haveI hAN : Finite (TensorProduct (ZMod p) A N) :=
    Work.Shrinking.finite_tensorProduct_of_finite (ZMod p) A N
  haveI hBN : Finite (TensorProduct (ZMod p) B N) :=
    Work.Shrinking.finite_tensorProduct_of_finite (ZMod p) B N
  haveI hCN : Finite (TensorProduct (ZMod p) C N) :=
    Work.Shrinking.finite_tensorProduct_of_finite (ZMod p) C N
  -- (1)  `e ⊗ id` is `G`-equivariant, so it identifies the invariants of `(A × C) ⊗ N`
  --      and of `(B × C) ⊗ N`
  have h₁ : Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
            (TensorProduct (ZMod p) (A × C) N)) =
      Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
            (TensorProduct (ZMod p) (B × C) N)) :=
    Work.SSGRoute.PTCore.finrank_invariants_equivariant
      (TensorProduct.congr e (LinearEquiv.refl (ZMod p) N))
      (fun g x =>
        Work.SSGRoute.PTCore.tensorProduct_congr_equivariant p e (LinearEquiv.refl (ZMod p) N)
          he (fun _ _ => rfl) g x)
  -- (2)  `TensorProduct.prodLeft` distributes `(A × C) ⊗ N` as `(A ⊗ N) × (C ⊗ N)`
  have h₂ : Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
            (TensorProduct (ZMod p) (A × C) N)) =
      Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
            ((TensorProduct (ZMod p) A N) × (TensorProduct (ZMod p) C N))) :=
    Work.SSGRoute.PTCore.finrank_invariants_equivariant
      (TensorProduct.prodLeft (ZMod p) (ZMod p) A C N)
      (fun g x =>
        tensorProduct_prodLeft_equivariant_aux (p := p) (G := G)
          (M₁ := A) (M₂ := C) (N := N) g x)
  -- (3)  the same for `B`
  have h₃ : Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
            (TensorProduct (ZMod p) (B × C) N)) =
      Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
            ((TensorProduct (ZMod p) B N) × (TensorProduct (ZMod p) C N))) :=
    Work.SSGRoute.PTCore.finrank_invariants_equivariant
      (TensorProduct.prodLeft (ZMod p) (ZMod p) B C N)
      (fun g x =>
        tensorProduct_prodLeft_equivariant_aux (p := p) (G := G)
          (M₁ := B) (M₂ := C) (N := N) g x)
  -- (4)  additivity of the invariant dimension over a product
  have h₄ := finrank_invariants_prod_aux (p := p) (G := G)
    (V := TensorProduct (ZMod p) A N) (W := TensorProduct (ZMod p) C N)
  have h₅ := finrank_invariants_prod_aux (p := p) (G := G)
    (V := TensorProduct (ZMod p) B N) (W := TensorProduct (ZMod p) C N)
  -- (5)  cancel the common summand
  rw [h₂, h₃, h₄, h₅] at h₁
  omega

end Work.SSGRoute.EulerSymm
