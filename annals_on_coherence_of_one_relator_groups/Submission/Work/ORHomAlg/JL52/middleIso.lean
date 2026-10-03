import Mathlib
import Submission.Work.ORHomAlg.JL52.DiagTensorDefs

namespace Work.ORHomAlg.JL52

open scoped TensorProduct

universe u

/-! ## The underlying `K`-linear flip

We realise the flip `A ⊗[K] (B ⊗[K] C) ≃ C ⊗[K] (B ⊗[K] A)` as the composite of the outer
commutativity, commutativity inside the first factor, and reassociation:
`A ⊗ (B ⊗ C) ≅ (B ⊗ C) ⊗ A ≅ (C ⊗ B) ⊗ A ≅ C ⊗ (B ⊗ A)`.
The point of the file is that this `K`-linear isomorphism is `K[G]`-linear for the *diagonal*
`K[G]`-actions of `DiagTensorDefs`. -/

/-- The `K`-linear flip `A ⊗[K] (B ⊗[K] C) ≃ₗ[K] C ⊗[K] (B ⊗[K] A)`. -/
noncomputable def flipLin (K : Type u) [Field K] (A B C : Type u)
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [AddCommGroup C] [Module K C] :
    TensorProduct K A (TensorProduct K B C) ≃ₗ[K] TensorProduct K C (TensorProduct K B A) :=
  (TensorProduct.comm K A (TensorProduct K B C)).trans
    ((TensorProduct.congr (TensorProduct.comm K B C) (LinearEquiv.refl K A)).trans
      (TensorProduct.assoc K C B A))

/-- `flipLin` sends `a ⊗ (b ⊗ c)` to `c ⊗ (b ⊗ a)`. -/
theorem flipLin_tmul (K : Type u) [Field K] (A B C : Type u)
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [AddCommGroup C] [Module K C] (a : A) (b : B) (c : C) :
    flipLin K A B C (a ⊗ₜ[K] (b ⊗ₜ[K] c)) = c ⊗ₜ[K] (b ⊗ₜ[K] a) := by
  simp only [flipLin, LinearEquiv.trans_apply, TensorProduct.comm_tmul, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, TensorProduct.assoc_tmul]

section

variable {K G : Type u} [Field K] [Group G]
variable {A B C : Type u}
variable [AddCommGroup A] [Module K A] [Module (MonoidAlgebra K G) A]
  [SMulCommClass K (MonoidAlgebra K G) A]
variable [AddCommGroup B] [Module K B] [Module (MonoidAlgebra K G) B]
  [SMulCommClass K (MonoidAlgebra K G) B]
variable [AddCommGroup C] [Module K C] [Module (MonoidAlgebra K G) C]
  [SMulCommClass K (MonoidAlgebra K G) C]
variable [SMulCommClass K (MonoidAlgebra K G) (TensorProduct K B C)]
variable [SMulCommClass K (MonoidAlgebra K G) (TensorProduct K B A)]

/-- `flipLin` intertwines the diagonal actions of a group element: the three factors are moved
around but the diagonal action is insensitive to the order. -/
theorem flipLin_diagElem (g : G) (z : TensorProduct K A (TensorProduct K B C)) :
    flipLin K A B C (diagElem (K := K) (G := G) A (TensorProduct K B C) g z)
      = diagElem (K := K) (G := G) C (TensorProduct K B A) g (flipLin K A B C z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul b c => simp only [diagElem_tmul, diag_smul_single_tmul, flipLin_tmul]
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- On the diagonal `K[G]`-module `A ⊗[K] X` the `K`-action and the `K[G]`-action associate:
`(c • r) • z = c • (r • z)`. -/
theorem diag_smul_smul_general {X : Type u} [AddCommGroup X] [Module K X]
    [Module (MonoidAlgebra K G) X] [SMulCommClass K (MonoidAlgebra K G) X]
    (c : K) (r : MonoidAlgebra K G) (z : TensorProduct K A X) :
    (c • r) • z = c • (r • z) := by
  rw [diag_smul_def, diagRingHom_smul]
  rfl

/-- `flipLin` intertwines the action of a generator `single g 1` of `K[G]`. -/
theorem flipLin_smul_single (g : G) (z : TensorProduct K A (TensorProduct K B C)) :
    flipLin K A B C ((MonoidAlgebra.single g (1 : K)) • z)
      = (MonoidAlgebra.single g (1 : K)) • flipLin K A B C z := by
  have h1 : (MonoidAlgebra.single g (1 : K)) • z
      = diagElem (K := K) (G := G) A (TensorProduct K B C) g z := by
    rw [diag_smul_def, diagRingHom_single]; rfl
  have h2 : (MonoidAlgebra.single g (1 : K)) • flipLin K A B C z
      = diagElem (K := K) (G := G) C (TensorProduct K B A) g (flipLin K A B C z) := by
    rw [diag_smul_def, diagRingHom_single]; rfl
  rw [h1, h2]
  exact flipLin_diagElem g z

/-- `flipLin` is `K[G]`-linear. -/
theorem flipLin_smul (r : MonoidAlgebra K G) (z : TensorProduct K A (TensorProduct K B C)) :
    flipLin K A B C (r • z) = r • flipLin K A B C z := by
  induction r using MonoidAlgebra.induction_on with
  | of m =>
      rw [MonoidAlgebra.of_apply]
      exact flipLin_smul_single m z
  | add r s hr hs => rw [add_smul, map_add, hr, hs, add_smul]
  | smul c r hr =>
      rw [diag_smul_smul_general, diag_smul_smul_general, map_smul, hr]

end

/-- The flip of the three factors of a triple tensor product over a field is `K[G]`-linear for the
diagonal `K[G]`-actions: `A ⊗[K] (B ⊗[K] C) ≅ C ⊗[K] (B ⊗[K] A)`.  This is the "middle
isomorphism" in the proof of Jaikin-Zapirain--Linton, Lemma 5.2 (2) (the identification
`L* ⊗_K (M ⊗_K N) ≅ N ⊗_K (M ⊗_K L*)`).  The two extra `SMulCommClass` hypotheses on the nested
tensors are exactly what is needed for the (`K[G]`-) diagonal structure on a tensor of tensors. -/
theorem middleIso (K G : Type u) [Field K] [Group G] (A B C : Type u)
    [AddCommGroup A] [Module K A] [Module (MonoidAlgebra K G) A]
    [SMulCommClass K (MonoidAlgebra K G) A]
    [AddCommGroup B] [Module K B] [Module (MonoidAlgebra K G) B]
    [SMulCommClass K (MonoidAlgebra K G) B]
    [AddCommGroup C] [Module K C] [Module (MonoidAlgebra K G) C]
    [SMulCommClass K (MonoidAlgebra K G) C]
    [SMulCommClass K (MonoidAlgebra K G) (TensorProduct K B C)]
    [SMulCommClass K (MonoidAlgebra K G) (TensorProduct K B A)] :
    Nonempty (TensorProduct K A (TensorProduct K B C) ≃ₗ[MonoidAlgebra K G]
      TensorProduct K C (TensorProduct K B A)) := by
  exact ⟨{ toFun := flipLin K A B C
           map_add' := (flipLin K A B C).map_add
           map_smul' := fun m x => flipLin_smul m x
           invFun := (flipLin K A B C).symm
           left_inv := (flipLin K A B C).left_inv
           right_inv := (flipLin K A B C).right_inv }⟩

end Work.ORHomAlg.JL52
