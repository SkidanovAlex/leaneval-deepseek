import Mathlib
import Submission.Work.CohomologicalShrinking.Models
import Submission.Work.CohomologicalShrinking.Levels
import Submission.Work.Tate.CoindUp
import Submission.Work.CohomologicalShrinking.augIdeal_coeff_sum
import Submission.Work.CohomologicalShrinking.eq_sum_coeff_smul_single
import Submission.Work.CohomologicalShrinking.coeff_smul_monoidAlgebra
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking

open scoped TensorProduct
open scoped BigOperators

set_option maxHeartbeats 1600000

universe u₀

variable (p : ℕ) (G : Type*) [Group G] [Fintype G]

/-- The generator `g - 1` of the augmentation ideal `I_G`. -/
noncomputable def augGen (g : G) : augIdeal p G :=
  ⟨MonoidAlgebra.single g (1 : ZMod p) - 1, subset_augIdeal p G g⟩

@[simp] theorem coe_augGen (g : G) :
    ((augGen p G g : augIdeal p G) : MonoidAlgebra (ZMod p) G)
      = MonoidAlgebra.single g 1 - 1 := rfl

/-- Evaluation of the coefficient at `z`, as a linear functional on `𝔽_p[G]`. -/
noncomputable def coeffAt (z : G) : MonoidAlgebra (ZMod p) G →ₗ[ZMod p] ZMod p where
  toFun y := y.coeff z
  map_add' x y := by simp [MonoidAlgebra.coeff_add]
  map_smul' c y := by simp [MonoidAlgebra.coeff_smul]

@[simp] theorem coeffAt_apply (z : G) (y : MonoidAlgebra (ZMod p) G) :
    coeffAt p G z y = y.coeff z := rfl

theorem coeff_augGen (u z : G) :
    ((augGen p G u : augIdeal p G) : MonoidAlgebra (ZMod p) G).coeff z
      = (Finsupp.single u (1 : ZMod p)) z - (Finsupp.single (1 : G) (1 : ZMod p)) z := by
  rw [coe_augGen, MonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    MonoidAlgebra.coeff_single, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single]

section Coeff

theorem sum_coeff_inv (y : MonoidAlgebra (ZMod p) G) :
    (∑ z : G, y.coeff z⁻¹) = ∑ u : G, y.coeff u := by
  refine Finset.sum_bij (fun z _ => z⁻¹) (fun z _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro a _ b _ h
    simpa using congr_arg Inv.inv h
  · intro b _
    exact ⟨b⁻¹, Finset.mem_univ _, by simp⟩
  · intro a _
    simp

end Coeff

section Module

variable (A : Type u₀) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
  [SMulCommClass G (ZMod p) A]

/-- The underlying bilinear map of `Phi`. -/
noncomputable def phiInner (a : A) : (augIdeal p G) →ₗ[ZMod p] (G → A) where
  toFun y := fun z => coeffAt p G z⁻¹ (y : MonoidAlgebra (ZMod p) G) • (z • a)
  map_add' y y' := by
    funext z
    simp only [Submodule.coe_add, map_add, Pi.add_apply, add_smul]
  map_smul' c y := by
    funext z
    simp only [Submodule.coe_smul, map_smul, Pi.smul_apply, RingHom.id_apply]
    rw [smul_assoc]

@[simp] theorem phiInner_apply (a : A) (y : augIdeal p G) (z : G) :
    phiInner p G A a y z = coeffAt p G z⁻¹ (y : MonoidAlgebra (ZMod p) G) • (z • a) := rfl

noncomputable def phiBilin : A →ₗ[ZMod p] (augIdeal p G) →ₗ[ZMod p] (G → A) where
  toFun a := phiInner p G A a
  map_add' a a' := by
    ext y z
    simp only [phiInner_apply, LinearMap.add_apply, Pi.add_apply, smul_add]
  map_smul' c a := by
    ext y z
    change coeffAt p G z⁻¹ (y : MonoidAlgebra (ZMod p) G) • (z • (c • a))
      = c • (coeffAt p G z⁻¹ (y : MonoidAlgebra (ZMod p) G) • (z • a))
    rw [smul_comm z c a, smul_comm]

/-- The `𝔽_p`-linear map `A ⊗ I_G → (G → A)`, `a ⊗ y ↦ (z ↦ y(z⁻¹) · z·a)`. -/
noncomputable def Phi : A ⊗[ZMod p] (augIdeal p G) →ₗ[ZMod p] (G → A) :=
  TensorProduct.lift (phiBilin p G A)

@[simp] theorem Phi_tmul (a : A) (y : augIdeal p G) :
    Phi p G A (a ⊗ₜ[ZMod p] y)
      = fun z => coeffAt p G z⁻¹ (y : MonoidAlgebra (ZMod p) G) • (z • a) := by
  simp [Phi, phiBilin, phiInner, TensorProduct.lift.tmul]

/-- The `𝔽_p`-linear map `(G → A) → A ⊗ I_G`, `f ↦ ∑_u (u • f u⁻¹) ⊗ (u - 1)`. -/
noncomputable def PsiTilde : (G → A) →ₗ[ZMod p] A ⊗[ZMod p] (augIdeal p G) where
  toFun f := ∑ u : G, (u • f u⁻¹) ⊗ₜ[ZMod p] (augGen p G u)
  map_add' f f' := by
    simp only [Pi.add_apply, smul_add, TensorProduct.add_tmul, Finset.sum_add_distrib]
  map_smul' c f := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    simp only [Pi.smul_apply, smul_comm, TensorProduct.smul_tmul', RingHom.id_apply]

@[simp] theorem PsiTilde_apply (f : G → A) :
    PsiTilde p G A f = ∑ u : G, (u • f u⁻¹) ⊗ₜ[ZMod p] (augGen p G u) := rfl

theorem sum_coeff_smul_augGen (y : augIdeal p G) :
    (∑ u : G, ((y : MonoidAlgebra (ZMod p) G).coeff u) • augGen p G u) = y := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  have hterm : ∀ u : G,
      ((((y : MonoidAlgebra (ZMod p) G).coeff u) • augGen p G u : augIdeal p G)
          : MonoidAlgebra (ZMod p) G)
        = (y : MonoidAlgebra (ZMod p) G).coeff u • MonoidAlgebra.single u 1
          - (y : MonoidAlgebra (ZMod p) G).coeff u • (1 : MonoidAlgebra (ZMod p) G) := by
    intro u
    rw [Submodule.coe_smul, coe_augGen, smul_sub]
  simp only [hterm, Finset.sum_sub_distrib]
  rw [← eq_sum_coeff_smul_single p G (y : MonoidAlgebra (ZMod p) G), ← Finset.sum_smul,
    augIdeal_coeff_sum p G _ y.2, zero_smul, sub_zero]

theorem PsiTilde_Phi (u : A ⊗[ZMod p] (augIdeal p G)) :
    PsiTilde p G A (Phi p G A u) = u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    rw [Phi_tmul, PsiTilde_apply]
    have hterm : ∀ u : G,
        (u • (fun z => coeffAt p G z⁻¹ (y : MonoidAlgebra (ZMod p) G) • (z • a)) u⁻¹)
          = (y : MonoidAlgebra (ZMod p) G).coeff u • a := by
      intro u
      change u • (coeffAt p G (u⁻¹)⁻¹ (y : MonoidAlgebra (ZMod p) G) • (u⁻¹ • a))
        = (y : MonoidAlgebra (ZMod p) G).coeff u • a
      rw [inv_inv, smul_comm, ← mul_smul, mul_inv_cancel, one_smul, coeffAt_apply]
    have hterm2 : ∀ u : G,
        (((y : MonoidAlgebra (ZMod p) G).coeff u) • a) ⊗ₜ[ZMod p] (augGen p G u)
          = a ⊗ₜ[ZMod p] (((y : MonoidAlgebra (ZMod p) G).coeff u) • augGen p G u) :=
      fun u => TensorProduct.smul_tmul _ _ _
    simp only [hterm, hterm2]
    rw [← TensorProduct.tmul_sum a Finset.univ
      (fun u => ((y : MonoidAlgebra (ZMod p) G).coeff u) • augGen p G u)]
    rw [sum_coeff_smul_augGen]
  | add u v hu hv => simp [map_add, hu, hv]

theorem sum_smul_inv_eq_coindAug (f : G → A) :
    (∑ u : G, u • f u⁻¹) = Work.Tate.coindAug G A f := by
  rw [Work.Tate.coindAug_apply]
  refine Finset.sum_bij (fun u _ => u⁻¹) (fun u _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro a _ b _ h
    simpa using congr_arg Inv.inv h
  · intro b _
    exact ⟨b⁻¹, Finset.mem_univ _, by simp⟩
  · intro a _
    simp

theorem Phi_mem_coindUp (u : A ⊗[ZMod p] (augIdeal p G)) :
    Work.Tate.coindAug G A (Phi p G A u) = 0 := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    rw [Phi_tmul, Work.Tate.coindAug_apply]
    have hterm : ∀ z : G,
        z⁻¹ • (coeffAt p G z⁻¹ (y : MonoidAlgebra (ZMod p) G) • (z • a))
          = ((y : MonoidAlgebra (ZMod p) G).coeff z⁻¹) • a := by
      intro z
      rw [smul_comm z⁻¹ (coeffAt p G z⁻¹ (y : MonoidAlgebra (ZMod p) G)) (z • a),
        ← mul_smul z⁻¹ z a, inv_mul_cancel, one_smul, coeffAt_apply]
    simp only [hterm]
    rw [← Finset.sum_smul, sum_coeff_inv, augIdeal_coeff_sum p G _ y.2, zero_smul]
  | add u v hu hv => simp [map_add, hu, hv]

theorem Phi_Psi_apply (f : G → A) (z : G) :
    Phi p G A (PsiTilde p G A f) z
      = f z - ((Finsupp.single (1 : G) (1 : ZMod p)) z⁻¹)
          • (z • Work.Tate.coindAug G A f) := by
  have h1 : Phi p G A (PsiTilde p G A f) z
      = ∑ u : G, ((augGen p G u : augIdeal p G) : MonoidAlgebra (ZMod p) G).coeff (z⁻¹)
          • (z • (u • f u⁻¹)) := by
    rw [PsiTilde_apply, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl (fun u _ => by rw [Phi_tmul]; rfl)
  rw [h1]
  have h2 : ∀ u : G, ((augGen p G u : augIdeal p G) : MonoidAlgebra (ZMod p) G).coeff (z⁻¹)
      = (Finsupp.single u (1 : ZMod p)) z⁻¹ - (Finsupp.single (1 : G) (1 : ZMod p)) z⁻¹ :=
    fun u => coeff_augGen p G u z⁻¹
  simp only [h2]
  rw [Finset.sum_congr rfl (fun u _ => sub_smul _ _ _), Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_eq_single (z⁻¹)]
    · rw [Finsupp.single_eq_same, inv_inv, one_smul, ← mul_smul, mul_inv_cancel, one_smul]
    · intro b _ hb
      rw [Finsupp.single_eq_of_ne (Ne.symm hb), zero_smul]
    · intro h; exact absurd (Finset.mem_univ (z⁻¹)) h
  · rw [← Finset.smul_sum, ← Finset.smul_sum, sum_smul_inv_eq_coindAug]

theorem Phi_Psi_mem (f : ↥(Work.Tate.coindUp G A)) :
    Phi p G A (PsiTilde p G A (f : G → A)) = (f : G → A) := by
  funext z
  rw [Phi_Psi_apply, AddMonoidHom.mem_ker.mp f.2]
  simp

theorem Phi_equiv (γ : G) (u : A ⊗[ZMod p] (augIdeal p G)) :
    Phi p G A (γ • u) = γ • Phi p G A u := by
  induction u using TensorProduct.induction_on with
  | zero => simp [Work.Tate.coind_smul_zero]
  | tmul a y =>
    rw [Work.Shrinking.diagTensor_smul_tmul, Phi_tmul, Phi_tmul]
    funext z
    show coeffAt p G z⁻¹ (γ • y) • (z • (γ • a))
      = (γ • fun w => coeffAt p G w⁻¹ y • (w • a)) z
    rw [Work.Tate.coind_smul_eq]
    show (γ • y : MonoidAlgebra (ZMod p) G).coeff z⁻¹ • (z • (γ • a))
      = (y : MonoidAlgebra (ZMod p) G).coeff ((z * γ)⁻¹) • ((z * γ) • a)
    rw [coeff_smul_monoidAlgebra, mul_inv_rev, ← mul_smul]
  | add u v hu hv =>
    rw [smul_add, map_add, hu, hv, ← Work.Tate.coind_smul_add, map_add]

end Module

section Nat

variable (A : Type u₀) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
  [SMulCommClass G (ZMod p) A]
variable (B : Type u₀) [AddCommGroup B] [Module (ZMod p) B] [DistribMulAction G B]
  [SMulCommClass G (ZMod p) B]

theorem Phi_rTensor (φ : A →ₗ[ZMod p] B)
    (hφ : ∀ (γ : G) (a : A), φ (γ • a) = γ • φ a)
    (u : A ⊗[ZMod p] (augIdeal p G)) :
    Phi p G B (LinearMap.rTensor (augIdeal p G) φ u)
      = Work.Tate.coindMap (φ.toAddMonoidHom) (Phi p G A u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    rw [LinearMap.rTensor_tmul, Phi_tmul, Phi_tmul]
    funext z
    show coeffAt p G z⁻¹ y • (z • φ a) = φ (coeffAt p G z⁻¹ y • (z • a))
    rw [map_smul, hφ]
  | add u v hu hv => simp [map_add, hu, hv]

end Nat

section Equiv

variable (A : Type u₀) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
  [SMulCommClass G (ZMod p) A]

/-- `Phi`, with values in the kernel `A^♯ ⊆ (G → A)` of the twisted norm. -/
noncomputable def PhiKer : A ⊗[ZMod p] (augIdeal p G) →+ ↥(Work.Tate.coindUp G A) where
  toFun u := ⟨Phi p G A u, Phi_mem_coindUp p G A u⟩
  map_zero' := Subtype.ext (map_zero (Phi p G A))
  map_add' u v := Subtype.ext (map_add (Phi p G A) u v)

/-- `PsiTilde`, restricted to the kernel `A^♯`. -/
noncomputable def PsiKer : ↥(Work.Tate.coindUp G A) →+ A ⊗[ZMod p] (augIdeal p G) :=
  (PsiTilde p G A).toAddMonoidHom.comp (Work.Tate.coindUp G A).subtype

@[simp] theorem PsiKer_apply (x : ↥(Work.Tate.coindUp G A)) :
    PsiKer p G A x = PsiTilde p G A (x : G → A) := rfl

theorem PhiKer_PsiKer (x : ↥(Work.Tate.coindUp G A)) :
    PhiKer p G A (PsiKer p G A x) = x :=
  Subtype.ext (Phi_Psi_mem p G A x)

theorem PsiKer_PhiKer (u : A ⊗[ZMod p] (augIdeal p G)) :
    PsiKer p G A (PhiKer p G A u) = u :=
  PsiTilde_Phi p G A u

theorem PhiKer_injective : Function.Injective (PhiKer p G A) :=
  Function.LeftInverse.injective (PsiKer_PhiKer p G A)

/-- The `𝔽_p`-linear isomorphism `A^♯ = ker(∑ x⁻¹ · x) ≅ A ⊗ I_G`. -/
noncomputable def coindUpTensorEquiv :
    ↥(Work.Tate.coindUp G A) ≃+ A ⊗[ZMod p] (augIdeal p G) where
  toFun := PsiKer p G A
  invFun := PhiKer p G A
  left_inv x := PhiKer_PsiKer p G A x
  right_inv u := PsiKer_PhiKer p G A u
  map_add' := map_add (PsiKer p G A)

theorem PhiKer_smul (γ : G) (u : A ⊗[ZMod p] (augIdeal p G)) :
    PhiKer p G A (γ • u) = γ • PhiKer p G A u :=
  Subtype.ext (Phi_equiv p G A γ u)

theorem coindUpTensorEquiv_equivariant (γ : G) (u : ↥(Work.Tate.coindUp G A)) :
    coindUpTensorEquiv p G A (γ • u) = γ • coindUpTensorEquiv p G A u := by
  apply PhiKer_injective p G A
  show PhiKer p G A (PsiKer p G A (γ • u)) = PhiKer p G A (γ • PsiKer p G A u)
  rw [PhiKer_PsiKer, PhiKer_smul, PhiKer_PsiKer]

end Equiv

section EquivNat

variable (A : Type u₀) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
  [SMulCommClass G (ZMod p) A]
variable (B : Type u₀) [AddCommGroup B] [Module (ZMod p) B] [DistribMulAction G B]
  [SMulCommClass G (ZMod p) B]

/-- The underlying function of `coindUpMap` is `coindMap`, by definition. -/
theorem coindUpMap_coe (φ : A →ₗ[ZMod p] B)
    (hφ : ∀ (γ : G) (a : A), φ (γ • a) = γ • φ a) (f : ↥(Work.Tate.coindUp G A)) :
    ((Work.Tate.coindUpMap (φ.toAddMonoidHom) hφ f : ↥(Work.Tate.coindUp G B)) : G → B)
      = Work.Tate.coindMap (φ.toAddMonoidHom) (f : G → A) := rfl

theorem PhiKer_rTensor (φ : A →ₗ[ZMod p] B)
    (hφ : ∀ (γ : G) (a : A), φ (γ • a) = γ • φ a)
    (u : A ⊗[ZMod p] (augIdeal p G)) :
    PhiKer p G B (LinearMap.rTensor (augIdeal p G) φ u)
      = Work.Tate.coindUpMap (φ.toAddMonoidHom) hφ (PhiKer p G A u) := by
  apply Subtype.ext
  exact Phi_rTensor p G A B φ hφ u

/-- Naturality of `PsiTilde` in the coefficients. -/
theorem PsiTilde_coindMap (φ : A →ₗ[ZMod p] B)
    (hφ : ∀ (γ : G) (a : A), φ (γ • a) = γ • φ a) (g : G → A) :
    PsiTilde p G B (Work.Tate.coindMap (φ.toAddMonoidHom) g)
      = LinearMap.rTensor (augIdeal p G) φ (PsiTilde p G A g) := by
  rw [PsiTilde_apply, PsiTilde_apply, map_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Work.Tate.coindMap_apply, LinearMap.rTensor_tmul]
  change (u • φ (g u⁻¹)) ⊗ₜ[ZMod p] augGen p G u = φ (u • g u⁻¹) ⊗ₜ[ZMod p] augGen p G u
  rw [hφ u (g u⁻¹)]

theorem natural_pointwise (φ : A →ₗ[ZMod p] B)
    (hφ : ∀ (γ : G) (a : A), φ (γ • a) = γ • φ a) (f : ↥(Work.Tate.coindUp G A)) :
    coindUpTensorEquiv p G B (Work.Tate.coindUpMap (φ.toAddMonoidHom) hφ f)
      = LinearMap.rTensor (augIdeal p G) φ (coindUpTensorEquiv p G A f) :=
  Eq.trans (congrArg (PsiTilde p G B) (coindUpMap_coe p G A B φ hφ f))
    (PsiTilde_coindMap p G A B φ hφ (f : G → A))

theorem coindUpTensorEquiv_natural (φ : A →ₗ[ZMod p] B)
    (hφ : ∀ (γ : G) (a : A), φ (γ • a) = γ • φ a) :
    (coindUpTensorEquiv p G B).toAddMonoidHom.comp (Work.Tate.coindUpMap (φ.toAddMonoidHom) hφ)
      = ((LinearMap.rTensor (augIdeal p G) φ).toAddMonoidHom).comp
          (coindUpTensorEquiv p G A).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro f
  exact natural_pointwise p G A B φ hφ f

end EquivNat

theorem coindUpAddEquivTensor (p : ℕ) (G : Type*) [Group G] [Fintype G] :
    ∃ e : ∀ (A : Type u₀) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
        [SMulCommClass G (ZMod p) A],
        (Work.Tate.coindUp G A) ≃+ TensorProduct (ZMod p) A (augIdeal p G),
      (∀ (A : Type u₀) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
          [SMulCommClass G (ZMod p) A] (γ : G) (x : Work.Tate.coindUp G A),
        e A (γ • x) = γ • e A x) ∧
      (∀ (A : Type u₀) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
          [SMulCommClass G (ZMod p) A]
        (B : Type u₀) [AddCommGroup B] [Module (ZMod p) B] [DistribMulAction G B]
          [SMulCommClass G (ZMod p) B]
        (φ : A →ₗ[ZMod p] B) (hφ : ∀ (γ : G) (a : A), φ (γ • a) = γ • φ a),
        (e B).toAddMonoidHom.comp (Work.Tate.coindUpMap (φ.toAddMonoidHom) hφ)
          = ((LinearMap.rTensor (augIdeal p G) φ).toAddMonoidHom).comp (e A).toAddMonoidHom) := by
  refine ⟨fun A _ _ _ _ => coindUpTensorEquiv p G A, ?_, ?_⟩
  · intro A _ _ _ _ γ x
    exact coindUpTensorEquiv_equivariant p G A γ x
  · intro A _ _ _ _ B _ _ _ _ φ hφ
    exact coindUpTensorEquiv_natural p G A B φ hφ

end Work.CohomologicalShrinking
