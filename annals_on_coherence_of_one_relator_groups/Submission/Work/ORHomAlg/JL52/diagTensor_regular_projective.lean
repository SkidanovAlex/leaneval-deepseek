/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `A ⊗[K] K[G]` with the diagonal action is a free `K[G]`-module

Jaikin-Zapirain--Linton, Lemma 5.2 (2): for a field `K`, a group `G` and a left `K[G]`-module `A`
whose `K`-action commutes with the `K[G]`-action, the `K`-module `A ⊗[K] K[G]` endowed with the
diagonal `K[G]`-action `g • (a ⊗ x) = (g • a) ⊗ (g • x)` is a free (hence projective) left
`K[G]`-module.

The proof exhibits a `K[G]`-linear isomorphism
`Ψ : K[G] ⊗[K] A ≃ A ⊗[K] K[G]`, `y ⊗ b ↦ y • (b ⊗ 1)`,
where the source carries the action on the first factor; the source is free over `K[G]` because
`K[G] ⊗[K] A = K[G] ⊗[K] (⊕ K)` is a direct sum of copies of `K[G]`.  The inverse of `Ψ` is the
`K`-linear "Hopf twist" `Φ : A ⊗[K] K[G] → K[G] ⊗[K] A`, `a ⊗ x ↦ ∑_g x_g • (g ⊗ (g⁻¹ • a))`,
defined through the canonical `K`-basis `{single g 1}` of `K[G]`; it is inverse to `Ψ` because
`Φ(Ψ(y ⊗ b)) = Φ((y • b) ⊗ 1) = y ⊗ b` and `Ψ(Φ(a ⊗ g)) = Ψ(g ⊗ g⁻¹ • a) = a ⊗ g`.
-/
import Mathlib
import Submission.Work.ORHomAlg.JL52.DiagTensorDefs

open scoped TensorProduct

namespace Work.ORHomAlg.JL52

universe u

namespace RegProj

/-! ## The `K`-linear maps `Φ` (a "Hopf twist") and `Ψ` -/

/-- The `K`-linear map underlying `Φ`: it is the composition of the family
`g ↦ single g 1 ⊗ g⁻¹ • a` with the canonical equivalence `(G → M) ≃ (K[G] →ₗ[K] M)` given by the
basis `{single g 1}` of `K[G]`. -/
noncomputable def vphi (K : Type u) [Field K] (G : Type u) [Group G] (A : Type u) [AddCommGroup A]
    [Module K A] [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A] :
    A →ₗ[K] (G → (MonoidAlgebra K G ⊗[K] A)) where
  toFun a g := (MonoidAlgebra.single g (1 : K)) ⊗ₜ[K] (gLin (K := K) (G := G) A g⁻¹ a)
  map_add' a a' := by
    funext g
    simp only [gLin_apply, smul_add, TensorProduct.tmul_add, Pi.add_apply]
  map_smul' c a := by
    funext g
    simp only [gLin_apply, map_smul, TensorProduct.tmul_smul, Pi.smul_apply, RingHom.id_apply]

/-- The bilinear map whose tensor product is the "Hopf twist" `Φ`. -/
noncomputable def PhiBeta (K : Type u) [Field K] (G : Type u) [Group G] (A : Type u) [AddCommGroup A]
    [Module K A] [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A] :
    A →ₗ[K] (MonoidAlgebra K G →ₗ[K] MonoidAlgebra K G ⊗[K] A) :=
  ((Module.Basis.constr (MonoidAlgebra.basis G K) K).toLinearMap).comp (vphi K G A)

/-- The `K`-linear "Hopf twist" `Φ : A ⊗[K] K[G] → K[G] ⊗[K] A`, sending `a ⊗ single g 1` to
`single g 1 ⊗ (g⁻¹ • a)`.  It is the inverse of `Ψ` (see `Phi_comp_Psi`, `Psi_comp_Phi`). -/
noncomputable def Phi (K : Type u) [Field K] (G : Type u) [Group G] (A : Type u) [AddCommGroup A]
    [Module K A] [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A] :
    A ⊗[K] (MonoidAlgebra K G) →ₗ[K] MonoidAlgebra K G ⊗[K] A :=
  TensorProduct.lift (PhiBeta K G A)

/-- The bilinear map `(y, b) ↦ y • (b ⊗ 1)` underlying `Ψ`. -/
noncomputable def PsiAux (K : Type u) [Field K] (G : Type u) [Group G] (A : Type u) [AddCommGroup A]
    [Module K A] [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A] :
    MonoidAlgebra K G →ₗ[K] (A →ₗ[K] (A ⊗[K] MonoidAlgebra K G)) where
  toFun y := (diagRingHom A (MonoidAlgebra K G) y).comp
    ((TensorProduct.mk K A (MonoidAlgebra K G)).flip (1 : MonoidAlgebra K G))
  map_add' y y' := by
    ext b
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
      LinearMap.add_apply, map_add]
  map_smul' c y := by
    ext b
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
      LinearMap.smul_apply, diagRingHom_smul, RingHom.id_apply]

/-- The `K`-linear map `Ψ : K[G] ⊗[K] A → A ⊗[K] K[G]`, `y ⊗ b ↦ y • (b ⊗ 1)`, where `•` is the
diagonal action on `A ⊗[K] K[G]`. -/
noncomputable def Psi (K : Type u) [Field K] (G : Type u) [Group G] (A : Type u) [AddCommGroup A]
    [Module K A] [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A] :
    (MonoidAlgebra K G) ⊗[K] A →ₗ[K] (A ⊗[K] MonoidAlgebra K G) :=
  TensorProduct.lift (PsiAux K G A)

theorem PsiAux_apply (K : Type u) [Field K] (G : Type u) [Group G] (A : Type u) [AddCommGroup A]
    [Module K A] [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A]
    (y : MonoidAlgebra K G) (b : A) :
    PsiAux K G A y b =
      (diagRingHom A (MonoidAlgebra K G) y) (b ⊗ₜ[K] (1 : MonoidAlgebra K G)) := rfl

theorem Psi_tmul (K : Type u) [Field K] (G : Type u) [Group G] (A : Type u) [AddCommGroup A]
    [Module K A] [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A]
    (y : MonoidAlgebra K G) (b : A) :
    Psi K G A (y ⊗ₜ[K] b) = y • (b ⊗ₜ[K] (1 : MonoidAlgebra K G)) := by
  rw [Psi, TensorProduct.lift.tmul, PsiAux_apply, diag_smul_def]

theorem Psi_tmul_single (K : Type u) [Field K] (G : Type u) [Group G] (A : Type u) [AddCommGroup A]
    [Module K A] [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A]
    (g : G) (a : A) :
    Psi K G A ((MonoidAlgebra.single g (1 : K)) ⊗ₜ[K] a) =
      (gLin (K := K) (G := G) A g a) ⊗ₜ[K] (MonoidAlgebra.single g (1 : K)) := by
  rw [Psi_tmul, diag_smul_single_tmul]
  simp [gLin_apply]

theorem Phi_tmul_single (K : Type u) [Field K] (G : Type u) [Group G] (A : Type u) [AddCommGroup A]
    [Module K A] [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A]
    (g : G) (x : A) :
    Phi K G A (x ⊗ₜ[K] (MonoidAlgebra.single g (1 : K))) =
      (MonoidAlgebra.single g (1 : K)) ⊗ₜ[K] (gLin (K := K) (G := G) A g⁻¹ x) := by
  rw [Phi, TensorProduct.lift.tmul]
  change ((Module.Basis.constr (MonoidAlgebra.basis G K) K) (vphi K G A x))
    (MonoidAlgebra.basis G K g) = _
  rw [Module.Basis.constr_basis]
  rfl

theorem gLin_inv_apply (K : Type u) [Field K] (G : Type u) [Group G] (A : Type u) [AddCommGroup A]
    [Module K A] [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A]
    (g : G) (a : A) :
    gLin (K := K) (G := G) A g (gLin (K := K) (G := G) A g⁻¹ a) = a := by
  have h : (gLin (K := K) (G := G) A g).comp (gLin (K := K) (G := G) A g⁻¹) = LinearMap.id := by
    rw [← gLin_mul, mul_inv_cancel, gLin_one]
  exact LinearMap.congr_fun h a

theorem gLin_apply_inv (K : Type u) [Field K] (G : Type u) [Group G] (A : Type u) [AddCommGroup A]
    [Module K A] [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A]
    (g : G) (a : A) :
    gLin (K := K) (G := G) A g⁻¹ (gLin (K := K) (G := G) A g a) = a := by
  have h : (gLin (K := K) (G := G) A g⁻¹).comp (gLin (K := K) (G := G) A g) = LinearMap.id := by
    rw [← gLin_mul, inv_mul_cancel, gLin_one]
  exact LinearMap.congr_fun h a

/-! ## The two `K`-bases used to check the inverse identities -/

noncomputable def bb (K : Type u) [Field K] (A : Type u) [AddCommGroup A] [Module K A] :
    Module.Basis (Module.Free.ChooseBasisIndex K A) K A :=
  Module.Free.chooseBasis K A

noncomputable def bA (K : Type u) [Field K] (G : Type u) [Group G] (A : Type u) [AddCommGroup A]
    [Module K A] [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A] :
    Module.Basis (Module.Free.ChooseBasisIndex K A × G) K (A ⊗[K] (MonoidAlgebra K G)) :=
  (bb K A).tensorProduct (MonoidAlgebra.basis G K)

noncomputable def bK (K : Type u) [Field K] (G : Type u) [Group G] (A : Type u) [AddCommGroup A]
    [Module K A] [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A] :
    Module.Basis (G × Module.Free.ChooseBasisIndex K A) K ((MonoidAlgebra K G) ⊗[K] A) :=
  (MonoidAlgebra.basis G K).tensorProduct (bb K A)

theorem bA_apply (K : Type u) [Field K] (G : Type u) [Group G] (A : Type u) [AddCommGroup A]
    [Module K A] [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A]
    (i : Module.Free.ChooseBasisIndex K A) (g : G) :
    bA K G A (i, g) = bb K A i ⊗ₜ[K] (MonoidAlgebra.single g (1 : K)) := by
  rw [bA, Module.Basis.tensorProduct_apply, MonoidAlgebra.basis_apply]

theorem bK_apply (K : Type u) [Field K] (G : Type u) [Group G] (A : Type u) [AddCommGroup A]
    [Module K A] [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A]
    (g : G) (i : Module.Free.ChooseBasisIndex K A) :
    bK K G A (g, i) = (MonoidAlgebra.single g (1 : K)) ⊗ₜ[K] bb K A i := by
  rw [bK, Module.Basis.tensorProduct_apply, MonoidAlgebra.basis_apply]

/-! ## `Φ` and `Ψ` are mutually inverse -/

theorem Phi_comp_Psi (K : Type u) [Field K] (G : Type u) [Group G] (A : Type u) [AddCommGroup A]
    [Module K A] [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A] :
    (Phi K G A).comp (Psi K G A) =
      (LinearMap.id : ((MonoidAlgebra K G) ⊗[K] A) →ₗ[K] ((MonoidAlgebra K G) ⊗[K] A)) := by
  have h : ∀ (i : G × Module.Free.ChooseBasisIndex K A),
      ((Phi K G A).comp (Psi K G A)) (bK K G A i) = bK K G A i := by
    rintro ⟨g, i⟩
    rw [LinearMap.comp_apply, bK_apply, Psi_tmul_single, Phi_tmul_single, gLin_apply_inv]
  exact Module.Basis.ext (b := bK K G A) (f₁ := (Phi K G A).comp (Psi K G A))
    (f₂ := LinearMap.id) h

theorem Psi_comp_Phi (K : Type u) [Field K] (G : Type u) [Group G] (A : Type u) [AddCommGroup A]
    [Module K A] [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A] :
    (Psi K G A).comp (Phi K G A) =
      (LinearMap.id : (A ⊗[K] (MonoidAlgebra K G)) →ₗ[K] (A ⊗[K] (MonoidAlgebra K G))) := by
  have h : ∀ (i : Module.Free.ChooseBasisIndex K A × G),
      ((Psi K G A).comp (Phi K G A)) (bA K G A i) = bA K G A i := by
    rintro ⟨i, g⟩
    rw [LinearMap.comp_apply, bA_apply, Phi_tmul_single, Psi_tmul_single, gLin_inv_apply]
  exact Module.Basis.ext (b := bA K G A) (f₁ := (Psi K G A).comp (Phi K G A))
    (f₂ := LinearMap.id) h

end RegProj

/-- `TensorProduct K A (MonoidAlgebra K G)`, with the diagonal `K[G]`-action, is a projective (in
fact free) left `K[G]`-module: if `{vᵢ}` is a `K`-basis of `A` then `{vᵢ ⊗ 1}` is a `K[G]`-basis,
since `g • (v ⊗ 1) = (g v) ⊗ g`. -/
theorem diagTensor_regular_projective (K : Type u) [Field K] (G : Type u) [Group G]
    (A : Type u) [AddCommGroup A] [Module K A] [Module (MonoidAlgebra K G) A]
    [SMulCommClass K (MonoidAlgebra K G) A] :
    Module.Projective (MonoidAlgebra K G) (TensorProduct K A (MonoidAlgebra K G)) := by
  -- The source `K[G] ⊗[K] A` is given the `K[G]`-module structure acting on the first factor.
  letI instM : Module (MonoidAlgebra K G) ((MonoidAlgebra K G) ⊗[K] A) :=
    TensorProduct.leftModule (R := K) (R'' := MonoidAlgebra K G) (M := MonoidAlgebra K G) (N := A)
  letI sM : SMul (MonoidAlgebra K G) ((MonoidAlgebra K G) ⊗[K] A) := instM.toSMul
  -- `Ψ` is `K[G]`-linear for this structure.
  have hsmul : ∀ (r : MonoidAlgebra K G) (z : (MonoidAlgebra K G) ⊗[K] A),
      RegProj.Psi K G A (r • z) = r • RegProj.Psi K G A z := by
    intro r z
    induction z using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.smul_zero, map_zero, diag_smul_def]
    | tmul y b =>
        rw [TensorProduct.smul_tmul', RegProj.Psi_tmul, RegProj.Psi_tmul, smul_eq_mul,
          diag_smul_def, diag_smul_def, diag_smul_def, map_mul]
        rfl
    | add p q hp hq =>
        rw [TensorProduct.smul_add, map_add, hp, hq]
        simp only [diag_smul_def, map_add]
  -- Assemble the `K[G]`-linear isomorphism `K[G] ⊗[K] A ≃ A ⊗[K] K[G]`.
  let e : ((MonoidAlgebra K G) ⊗[K] A) ≃ₗ[MonoidAlgebra K G] (A ⊗[K] (MonoidAlgebra K G)) :=
    { toFun := RegProj.Psi K G A
      invFun := RegProj.Phi K G A
      left_inv := fun z => LinearMap.congr_fun (RegProj.Phi_comp_Psi K G A) z
      right_inv := fun z => LinearMap.congr_fun (RegProj.Psi_comp_Phi K G A) z
      map_add' := fun x y => (RegProj.Psi K G A).map_add x y
      map_smul' := hsmul }
  -- `K[G] ⊗[K] A` is free over `K[G]` as a base change of the free `K`-module `A`.
  haveI : Module.Projective (MonoidAlgebra K G) ((MonoidAlgebra K G) ⊗[K] A) :=
    Module.Projective.of_basis ((RegProj.bb K A).baseChange (MonoidAlgebra K G))
  exact Module.Projective.of_equiv' e

end Work.ORHomAlg.JL52
