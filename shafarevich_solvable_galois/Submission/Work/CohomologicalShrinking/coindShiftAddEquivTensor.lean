/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The natural equivariant equivalence `A^* = Coind(A)/A ≃+ A ⊗ I_G^{-1}`

The paper's dimension shifting `Ĥ^k(G, M) ≅ Ĥ^{-1}(G, M ⊗ A_k)`, `A_k = I_G^{-(k+1)}`, is
proved here from the short exact sequence `0 → A → Coind(A) → A^* → 0` (`Work.Tate.coindSES`)
together with the identification

`A^* = Coind(A)/A ≃+ A ⊗ I_G^{-1}`,  `I_G^{-1} = Hom_{𝔽_p}(I_G, 𝔽_p)`

of the right hand module with the twist by the dual of the augmentation ideal.  This file
constructs that identification, canonically (no choices of bases beyond the group basis of
`𝔽_p[G]`), and proves that it is

* `G`-**equivariant** (`coindShiftDualEquiv_equivariant`), and
* **natural** in the coefficient module: for a `G`-equivariant `φ : A → B` and *any* additive
  `ψ : A^* → B^*` compatible with `coindMap φ` under the projections, the square with
  `rTensor φ : A ⊗ I_G^{-1} → B ⊗ I_G^{-1}` commutes (`coindShiftDualEquiv_natural`).

## The construction

Writing `dGen z : I_G^{-1}` for the restriction to `I_G` of the coefficient functional at `z`,
and `augGen u = u - 1 ∈ I_G`, the two maps are

* `dPhi : A ⊗ I_G^{-1} → Coind(A)`, `a ⊗ f ↦ (z ↦ f (z⁻¹ - 1) • (z • a))`,
* `dPsiTilde : Coind(A) → A ⊗ I_G^{-1}`, `x ↦ ∑_u (u • x u⁻¹) ⊗ dGen u`.

The second one kills the diagonal `A ⊆ Coind(A)` — this is where `∑_u dGen u = 0`
(`sum_dGen`) enters — hence descends to `dPsiBar : A^* → A ⊗ I_G^{-1}`; the first one
descends by construction, `dPhiBar`.  The two are inverse: on pure tensors one uses
`∑_u f (augGen u) • dGen u = f` (`sum_dGen_augGen`, the "dual basis" relation for the basis
`{augGen u | u ≠ 1}` of `I_G`), and on `A^*` one uses
`dPhi (dPsiTilde x) = x - (z ↦ z • x 1) ∈ x + diag`.

Everything is `𝔽_p`-linear, and the equivariance of `dPsiTilde`
(`∑_u (u • x (u⁻¹δ)) ⊗ dGen u = δ • ∑_u (u • x u⁻¹) ⊗ dGen u`) uses `γ • dGen u = dGen (γ u)`.

This is the module `Submission.Work.CohomologicalShrinking.coindShiftAddEquivTensor`, whose
main theorem `coindShiftAddEquivTensor` packages the equivalence, its equivariance and its
naturality as required by the dimension shift `Ĥ²(G,A) ≅ Ĥ^{-1}(G, A ⊗ A_2)`.
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.Models
import Submission.Work.CohomologicalShrinking.Levels
import Submission.Work.Tate.DimensionShiftH
import Submission.Work.CohomologicalShrinking.coindUpAddEquivTensor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking

open scoped TensorProduct
open scoped BigOperators

attribute [local instance] Classical.decEq

set_option maxHeartbeats 1600000

universe u₀

variable (p : ℕ) (G : Type*) [Group G] [Fintype G]

/-- The coefficient functional at `z`, restricted to the augmentation ideal. -/
noncomputable def dGen (z : G) : igDual p G :=
  (coeffAt p G z).comp (augIdeal p G).subtype

@[simp] theorem dGen_apply (z : G) (y : augIdeal p G) :
    dGen p G z y = (y : MonoidAlgebra (ZMod p) G).coeff z := rfl

theorem dGen_augGen (z u : G) :
    dGen p G z (augGen p G u) =
      (Finsupp.single u (1 : ZMod p)) z - (Finsupp.single (1 : G) (1 : ZMod p)) z := by
  rw [dGen_apply, coeff_augGen]

theorem sum_dGen_augGen (f : igDual p G) :
    (∑ u : G, f (augGen p G u) • dGen p G u) = f := by
  refine LinearMap.ext fun y => ?_
  have h1 : (∑ u : G, f (augGen p G u) • dGen p G u) y
      = ∑ u : G, (f (augGen p G u)) * ((y : MonoidAlgebra (ZMod p) G).coeff u) := by
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun u _ => by rw [LinearMap.smul_apply, dGen_apply, smul_eq_mul]
  rw [h1]
  conv_rhs => rw [← sum_coeff_smul_augGen p G y]
  rw [map_sum]
  rw [show (∑ u : G, f (((y : MonoidAlgebra (ZMod p) G).coeff u) • augGen p G u))
      = ∑ u : G, (f (augGen p G u)) * ((y : MonoidAlgebra (ZMod p) G).coeff u) from
    Finset.sum_congr rfl fun u _ => by rw [map_smul, smul_eq_mul, mul_comm]]

theorem sum_dGen : (∑ u : G, dGen p G u) = 0 := by
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.sum_apply, LinearMap.zero_apply]
  rw [Finset.sum_congr rfl (fun u _ =>
    (rfl : dGen p G u y = (y : MonoidAlgebra (ZMod p) G).coeff u))]
  exact augIdeal_coeff_sum p G (y : MonoidAlgebra (ZMod p) G) y.2

theorem dGen_smul (δ u : G) : δ • dGen p G u = dGen p G (δ * u) := by
  refine LinearMap.ext fun y => ?_
  rw [smul_igDual_apply, dGen_apply, coe_smul_augIdeal, coeff_smul_monoidAlgebra, inv_inv,
    dGen_apply]

section Module

variable (A : Type u₀) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
  [SMulCommClass G (ZMod p) A]

noncomputable def dPhiInner (a : A) : igDual p G →ₗ[ZMod p] (G → A) where
  toFun f := fun z => f (augGen p G z⁻¹) • (z • a)
  map_add' f f' := by
    funext z
    rw [Pi.add_apply, LinearMap.add_apply, add_smul]
  map_smul' c f := by
    funext z
    simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul]

@[simp] theorem dPhiInner_apply (a : A) (f : igDual p G) (z : G) :
    dPhiInner p G A a f z = f (augGen p G z⁻¹) • (z • a) := rfl

noncomputable def dPhiBilin : A →ₗ[ZMod p] igDual p G →ₗ[ZMod p] (G → A) where
  toFun a := dPhiInner p G A a
  map_add' a a' := by
    ext f z
    simp only [dPhiInner_apply, LinearMap.add_apply, Pi.add_apply, smul_add]
  map_smul' c a := by
    ext f z
    change f (augGen p G z⁻¹) • (z • (c • a)) = c • (f (augGen p G z⁻¹) • (z • a))
    rw [smul_comm z c a, smul_comm]

noncomputable def dPhi : A ⊗[ZMod p] igDual p G →ₗ[ZMod p] (G → A) :=
  TensorProduct.lift (dPhiBilin p G A)

@[simp] theorem dPhi_tmul (a : A) (f : igDual p G) :
    dPhi p G A (a ⊗ₜ[ZMod p] f) = fun z => f (augGen p G z⁻¹) • (z • a) := by
  simp [dPhi, dPhiBilin, dPhiInner, TensorProduct.lift.tmul]

noncomputable def dPsiTilde : (G → A) →ₗ[ZMod p] A ⊗[ZMod p] igDual p G where
  toFun x := ∑ u : G, (u • x u⁻¹) ⊗ₜ[ZMod p] dGen p G u
  map_add' x x' := by
    simp only [Pi.add_apply, smul_add, TensorProduct.add_tmul, Finset.sum_add_distrib]
  map_smul' c x := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    simp only [Pi.smul_apply, smul_comm, TensorProduct.smul_tmul', RingHom.id_apply]

@[simp] theorem dPsiTilde_apply (x : G → A) :
    dPsiTilde p G A x = ∑ u : G, (u • x u⁻¹) ⊗ₜ[ZMod p] dGen p G u := rfl

theorem dPsiTilde_dPhi (u : A ⊗[ZMod p] igDual p G) : dPsiTilde p G A (dPhi p G A u) = u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a f =>
    rw [dPhi_tmul, dPsiTilde_apply]
    have hterm : ∀ u : G,
        (u • (fun z => f (augGen p G z⁻¹) • (z • a)) u⁻¹) = f (augGen p G u) • a := by
      intro u
      change u • (f (augGen p G u⁻¹⁻¹) • (u⁻¹ • a)) = f (augGen p G u) • a
      rw [inv_inv, smul_comm, ← mul_smul, mul_inv_cancel, one_smul]
    have hterm2 : ∀ u : G, (f (augGen p G u) • a) ⊗ₜ[ZMod p] dGen p G u
        = a ⊗ₜ[ZMod p] (f (augGen p G u) • dGen p G u) := fun u => TensorProduct.smul_tmul _ _ _
    simp only [hterm, hterm2]
    rw [← TensorProduct.tmul_sum a Finset.univ (fun u => f (augGen p G u) • dGen p G u)]
    rw [sum_dGen_augGen]
  | add u v hu hv => simp [map_add, hu, hv]

theorem dPhi_dPsiTilde (x : G → A) :
    dPhi p G A (dPsiTilde p G A x) = fun z => x z - z • x 1 := by
  funext z
  have h1 : dPhi p G A (dPsiTilde p G A x) z
      = ∑ u : G, (((augGen p G z⁻¹ : augIdeal p G) : MonoidAlgebra (ZMod p) G).coeff u)
          • (z • (u • x u⁻¹)) := by
    rw [dPsiTilde_apply, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl (fun u _ => by rw [dPhi_tmul]; rfl)
  rw [h1]
  have h2 : ∀ u : G, (((augGen p G z⁻¹ : augIdeal p G) : MonoidAlgebra (ZMod p) G).coeff u)
      = (Finsupp.single z⁻¹ (1 : ZMod p)) u - (Finsupp.single (1 : G) (1 : ZMod p)) u :=
    fun u => coeff_augGen p G z⁻¹ u
  simp only [h2]
  rw [Finset.sum_congr rfl (fun u _ => sub_smul _ _ _), Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_eq_single z⁻¹]
    · rw [Finsupp.single_eq_same, inv_inv, one_smul, ← mul_smul, mul_inv_cancel, one_smul]
    · intro b _ hb
      rw [Finsupp.single_eq_of_ne hb, zero_smul]
    · intro h; exact absurd (Finset.mem_univ z⁻¹) h
  · rw [Finset.sum_eq_single 1]
    · rw [Finsupp.single_eq_same, inv_one, one_smul, one_smul]
    · intro b _ hb
      rw [Finsupp.single_eq_of_ne hb, zero_smul]
    · intro h; exact absurd (Finset.mem_univ 1) h

theorem dPhi_dPsiTilde_sub_mem (x : G → A) :
    dPhi p G A (dPsiTilde p G A x) - x ∈ Work.Tate.coindDiag G A := by
  rw [dPhi_dPsiTilde, Work.Tate.mem_coindDiag_iff]
  refine ⟨-(x 1), ?_⟩
  funext z
  simp [Pi.sub_apply, smul_neg]

theorem dPsiTilde_eq_zero_of_mem (φ : G → A) (hφ : φ ∈ Work.Tate.coindDiag G A) :
    dPsiTilde p G A φ = 0 := by
  obtain ⟨a, rfl⟩ := (Work.Tate.mem_coindDiag_iff G A).mp hφ
  rw [dPsiTilde_apply]
  have hterm : ∀ u : G, (u • (fun z : G => z • a) u⁻¹) = a := by
    intro u
    show u • (u⁻¹ • a) = a
    rw [← mul_smul, mul_inv_cancel, one_smul]
  rw [Finset.sum_congr rfl (fun u _ => by rw [hterm u])]
  rw [← TensorProduct.tmul_sum a Finset.univ (fun u : G => dGen p G u), sum_dGen,
    TensorProduct.tmul_zero]

theorem dPsiTilde_equiv (δ : G) (x : G → A) :
    dPsiTilde p G A (δ • x) = δ • dPsiTilde p G A x := by
  have hL : dPsiTilde p G A (δ • x) = ∑ u : G, (u • x (u⁻¹ * δ)) ⊗ₜ[ZMod p] dGen p G u := by
    rw [dPsiTilde_apply]
    exact Finset.sum_congr rfl (fun u _ => by rw [Work.Tate.coind_smul_eq])
  have hR : δ • dPsiTilde p G A x = ∑ u : G, (u • x (u⁻¹ * δ)) ⊗ₜ[ZMod p] dGen p G u := by
    rw [dPsiTilde_apply, Finset.smul_sum]
    rw [show (∑ u : G, δ • ((u • x u⁻¹) ⊗ₜ[ZMod p] dGen p G u))
        = ∑ u : G, ((δ * u) • x u⁻¹) ⊗ₜ[ZMod p] dGen p G (δ * u) from
      Finset.sum_congr rfl (fun u _ => by
        rw [Work.Shrinking.diagTensor_smul_tmul, mul_smul, dGen_smul])]
    rw [Finset.sum_congr rfl (fun u _ => by
      rw [show x u⁻¹ = x ((δ * u)⁻¹ * δ) from by
        rw [show (δ * u)⁻¹ * δ = u⁻¹ by
          rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]]])]
    change (∑ u : G, (((Equiv.mulLeft δ) u) • x (((Equiv.mulLeft δ) u)⁻¹ * δ)) ⊗ₜ[ZMod p]
        dGen p G ((Equiv.mulLeft δ) u)) = ∑ v : G, (v • x (v⁻¹ * δ)) ⊗ₜ[ZMod p] dGen p G v
    rw [Equiv.sum_comp (Equiv.mulLeft δ)
      (fun v : G => (v • x (v⁻¹ * δ)) ⊗ₜ[ZMod p] dGen p G v)]
  rw [hL, hR]

end Module

section Quotient

variable (A : Type u₀) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
  [SMulCommClass G (ZMod p) A]

theorem coindProj_smul (γ : G) (φ : G → A) :
    γ • Work.Tate.coindProj G A φ = Work.Tate.coindProj G A (γ • φ) :=
  Work.Tate.quot_smul_mk' G A γ φ

/-- The `𝔽_p`-linear map `A ⊗ I_G^{-1} → A^* = Coind(A)/A` descending `dPhi`. -/
noncomputable def dPhiBar : A ⊗[ZMod p] igDual p G →+ Work.Tate.coindShift G A :=
  (Work.Tate.coindProj G A).comp (dPhi p G A).toAddMonoidHom

/-- The `𝔽_p`-linear map `A^* → A ⊗ I_G^{-1}` descending `dPsiTilde`. -/
noncomputable def dPsiBar : Work.Tate.coindShift G A →+ A ⊗[ZMod p] igDual p G :=
  QuotientAddGroup.lift (Work.Tate.coindDiag G A) (dPsiTilde p G A).toAddMonoidHom
    (fun φ hφ => by
      rw [AddMonoidHom.mem_ker]
      exact dPsiTilde_eq_zero_of_mem p G A φ hφ)

theorem dPsiBar_mk (x : G → A) :
    dPsiBar p G A (Work.Tate.coindProj G A x) = dPsiTilde p G A x := by
  rw [dPsiBar]
  exact QuotientAddGroup.lift_mk' _ _ x

theorem dPhiBar_comp_dPsiBar :
    (dPhiBar p G A).comp (dPsiBar p G A) = AddMonoidHom.id _ := by
  refine AddMonoidHom.ext fun y => ?_
  refine QuotientAddGroup.induction_on y (fun x => ?_)
  change dPhiBar p G A (dPsiBar p G A (Work.Tate.coindProj G A x))
      = Work.Tate.coindProj G A x
  rw [dPsiBar_mk]
  change Work.Tate.coindProj G A (dPhi p G A (dPsiTilde p G A x))
      = Work.Tate.coindProj G A x
  have h : Work.Tate.coindProj G A (dPhi p G A (dPsiTilde p G A x) - x) = 0 := by
    rw [Work.Tate.coindProj_eq_zero_iff]
    exact dPhi_dPsiTilde_sub_mem p G A x
  rw [map_sub] at h
  exact sub_eq_zero.mp h

theorem dPsiBar_comp_dPhiBar :
    (dPsiBar p G A).comp (dPhiBar p G A) = AddMonoidHom.id _ := by
  refine AddMonoidHom.ext fun u => ?_
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a f =>
      change dPsiBar p G A (Work.Tate.coindProj G A (dPhi p G A (a ⊗ₜ[ZMod p] f)))
        = a ⊗ₜ[ZMod p] f
      rw [dPsiBar_mk, dPsiTilde_dPhi]
  | add u v hu hv => simp [map_add, hu, hv]

/-- The additive isomorphism `A^* = Coind(A)/A ≃+ A ⊗ I_G^{-1}`. -/
noncomputable def coindShiftDualEquiv :
    Work.Tate.coindShift G A ≃+ A ⊗[ZMod p] igDual p G where
  toFun := dPsiBar p G A
  invFun := dPhiBar p G A
  left_inv y := DFunLike.congr_fun (dPhiBar_comp_dPsiBar p G A) y
  right_inv u := DFunLike.congr_fun (dPsiBar_comp_dPhiBar p G A) u
  map_add' := map_add (dPsiBar p G A)

theorem dPsiBar_equiv (δ : G) (y : Work.Tate.coindShift G A) :
    dPsiBar p G A (δ • y) = δ • dPsiBar p G A y := by
  refine QuotientAddGroup.induction_on y (fun x => ?_)
  change dPsiBar p G A (δ • Work.Tate.coindProj G A x)
      = δ • dPsiBar p G A (Work.Tate.coindProj G A x)
  rw [coindProj_smul, dPsiBar_mk, dPsiBar_mk, dPsiTilde_equiv]

end Quotient

section Nat

variable (A : Type u₀) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
  [SMulCommClass G (ZMod p) A]
variable (B : Type u₀) [AddCommGroup B] [Module (ZMod p) B] [DistribMulAction G B]
  [SMulCommClass G (ZMod p) B]

theorem dPsiTilde_rTensor (φ : A →ₗ[ZMod p] B)
    (hφ : ∀ (γ : G) (a : A), φ (γ • a) = γ • φ a) (x : G → A) :
    dPsiTilde p G B (Work.Tate.coindMap (φ.toAddMonoidHom) x)
      = LinearMap.rTensor (igDual p G) φ (dPsiTilde p G A x) := by
  rw [dPsiTilde_apply, dPsiTilde_apply, map_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Work.Tate.coindMap_apply, LinearMap.rTensor_tmul]
  exact congrArg (fun t => t ⊗ₜ[ZMod p] dGen p G u)
    (show u • φ.toAddMonoidHom (x u⁻¹) = φ (u • x u⁻¹) from (hφ u (x u⁻¹)).symm)

theorem dPsiBar_natural (φ : A →ₗ[ZMod p] B)
    (hφ : ∀ (γ : G) (a : A), φ (γ • a) = γ • φ a)
    (ψ : Work.Tate.coindShift G A →+ Work.Tate.coindShift G B)
    (hψ : ∀ x : G → A, ψ (Work.Tate.coindProj G A x)
      = Work.Tate.coindProj G B (Work.Tate.coindMap (φ.toAddMonoidHom) x)) :
    (coindShiftDualEquiv p G B).toAddMonoidHom.comp ψ
      = ((LinearMap.rTensor (igDual p G) φ).toAddMonoidHom).comp
          (coindShiftDualEquiv p G A).toAddMonoidHom := by
  refine AddMonoidHom.ext fun y => ?_
  refine QuotientAddGroup.induction_on y (fun x => ?_)
  change dPsiBar p G B (ψ (Work.Tate.coindProj G A x))
      = (LinearMap.rTensor (igDual p G) φ) (dPsiBar p G A (Work.Tate.coindProj G A x))
  rw [hψ x, dPsiBar_mk, dPsiBar_mk]
  exact dPsiTilde_rTensor p G A B φ hφ x

end Nat

theorem coindShiftAddEquivTensor (p : ℕ) (G : Type*) [Group G] [Fintype G] :
    ∃ e : ∀ (A : Type u₀) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
        [SMulCommClass G (ZMod p) A],
        (Work.Tate.coindShift G A) ≃+ TensorProduct (ZMod p) A (igDual p G),
      (∀ (A : Type u₀) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
          [SMulCommClass G (ZMod p) A] (γ : G) (x : Work.Tate.coindShift G A),
        e A (γ • x) = γ • e A x) ∧
      (∀ (A : Type u₀) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
          [SMulCommClass G (ZMod p) A]
        (B : Type u₀) [AddCommGroup B] [Module (ZMod p) B] [DistribMulAction G B]
          [SMulCommClass G (ZMod p) B]
        (φ : A →ₗ[ZMod p] B) (hφ : ∀ (γ : G) (a : A), φ (γ • a) = γ • φ a)
        (ψ : Work.Tate.coindShift G A →+ Work.Tate.coindShift G B)
        (hψproj : ∀ x : G → A, ψ (Work.Tate.coindProj G A x)
          = Work.Tate.coindProj G B (Work.Tate.coindMap (φ.toAddMonoidHom) x)),
        (e B).toAddMonoidHom.comp ψ
          = ((LinearMap.rTensor (igDual p G) φ).toAddMonoidHom).comp (e A).toAddMonoidHom) := by
  refine ⟨fun A _ _ _ _ => coindShiftDualEquiv p G A, ?_, ?_⟩
  · intro A _ _ _ _ γ x
    exact dPsiBar_equiv p G A γ x
  · intro A _ _ _ _ B _ _ _ _ φ hφ ψ hψ
    exact dPsiBar_natural p G A B φ hφ ψ hψ

end Work.CohomologicalShrinking
