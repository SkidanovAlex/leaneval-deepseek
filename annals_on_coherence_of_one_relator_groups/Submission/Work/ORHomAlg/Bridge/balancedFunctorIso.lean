import Mathlib
import Submission.Work.ORHomAlg.Bridge.BridgeDefs
import Submission.Work.ORCoherence.Tor

set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory Limits
open scoped TensorProduct

namespace Work.ORHomAlg.Bridge

universe u

/-! ## The two generating sets -/

/-- The generating set of the balanced relations of the `ORCoherence` chapter. -/
def bridgeGenOC {R S : Type u} [Ring R] [Ring S] (f : R →+* S) (N : Type u)
    [AddCommGroup N] [Module R N] : Set (S ⊗[ℤ] N) :=
  {x | ∃ (r : R) (s : S) (m : N), x = (s * f r) ⊗ₜ[ℤ] m - s ⊗ₜ[ℤ] (r • m)}

/-- The generating set of the balanced relations of the `ORHomAlg` chapter. -/
def bridgeGenBal (R : Type u) [Ring R] (S : Type u) [Ring S] [Module Rᵐᵒᵖ S]
    (N : Type u) [AddCommGroup N] [Module R N] : Set (S ⊗[ℤ] N) :=
  {x | ∃ (u : S) (r : R) (m : N), x = (MulOpposite.op r • u) ⊗ₜ[ℤ] m - u ⊗ₜ[ℤ] (r • m)}

theorem balancedRel_OC_eq_span {R S : Type u} [Ring R] [Ring S] (f : R →+* S) (N : Type u)
    [AddCommGroup N] [Module R N] :
    Work.ORCoherence.balancedRel f N = Submodule.span S (bridgeGenOC f N) := rfl

theorem balancedRel_bal_eq_span (R S : Type u) [Ring R] [Ring S] [Module Rᵐᵒᵖ S] (N : Type u)
    [AddCommGroup N] [Module R N] :
    Work.ORHomAlg.balancedRel R S N = Submodule.span ℤ (bridgeGenBal R S N) := rfl

theorem genBal_eq_genOC {R S : Type u} [Ring R] [Ring S] (f : R →+* S) [Module Rᵐᵒᵖ S]
    (h : ∀ (r : R) (s : S), (MulOpposite.op r) • s = s * f r) (N : Type u)
    [AddCommGroup N] [Module R N] :
    bridgeGenBal R S N = bridgeGenOC f N := by
  ext x
  constructor
  · rintro ⟨u, r, m, rfl⟩
    exact ⟨r, u, m, by rw [h]⟩
  · rintro ⟨r, u, m, rfl⟩
    exact ⟨u, r, m, by rw [h]⟩

/-! ## Closure of the spans under the `S`-action -/

theorem smul_mem_genOC {R S : Type u} [Ring R] [Ring S] (f : R →+* S) [Module Rᵐᵒᵖ S]
    (N : Type u) [AddCommGroup N] [Module R N] (t : S) {x : S ⊗[ℤ] N}
    (hx : x ∈ bridgeGenOC f N) : t • x ∈ bridgeGenOC f N := by
  obtain ⟨r, u, m, rfl⟩ := hx
  refine ⟨r, t * u, m, ?_⟩
  rw [smul_sub, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul,
    mul_assoc]

theorem int_smul_comm' {S : Type u} [Ring S] {N : Type u} [AddCommGroup N]
    (t : S) (c : ℤ) (x : S ⊗[ℤ] N) :
    t • (c • x) = c • (t • x) := by
  rw [← Int.cast_smul_eq_zsmul (R := S) c x, ← mul_smul,
    ← (Int.cast_commute c t).eq, mul_smul, Int.cast_smul_eq_zsmul (R := S) c (t • x)]

theorem smul_mem_span_genOC {R S : Type u} [Ring R] [Ring S] (f : R →+* S) [Module Rᵐᵒᵖ S]
    (N : Type u) [AddCommGroup N] [Module R N] (t : S) {x : S ⊗[ℤ] N}
    (hx : x ∈ Submodule.span ℤ (bridgeGenOC f N)) :
    t • x ∈ Submodule.span ℤ (bridgeGenOC f N) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span (smul_mem_genOC f N t hy)
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add a b ha hb iha ihb => rw [smul_add]; exact Submodule.add_mem _ iha ihb
  | smul c a ha iha =>
      rw [int_smul_comm' t c a]
      exact Submodule.smul_mem _ c iha

/-- The `S`-span and the `ℤ`-span of the `ORCoherence` relations have the same elements. -/
theorem span_genOC_eq {R S : Type u} [Ring R] [Ring S] (f : R →+* S) [Module Rᵐᵒᵖ S]
    (N : Type u) [AddCommGroup N] [Module R N] :
    ((Submodule.span S (bridgeGenOC f N) : Submodule S (S ⊗[ℤ] N)) : Set (S ⊗[ℤ] N)) =
      ((Submodule.span ℤ (bridgeGenOC f N) : Submodule ℤ (S ⊗[ℤ] N)) : Set (S ⊗[ℤ] N)) := by
  apply le_antisymm
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact Submodule.zero_mem _
    | add a b ha hb iha ihb => exact Submodule.add_mem _ iha ihb
    | smul t a ha iha => exact smul_mem_span_genOC f N t iha
  · intro x hx
    refine (Submodule.span_le (p := (Submodule.span S (bridgeGenOC f N)).restrictScalars ℤ)).mpr
      (fun y hy => Submodule.subset_span hy) hx

/-- As `ℤ`-submodules, the `ORCoherence` balanced relation is the `ℤ`-span of its generators. -/
theorem span_genOC_restrictScalars {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    [Module Rᵐᵒᵖ S] (N : Type u) [AddCommGroup N] [Module R N] :
    (Submodule.span S (bridgeGenOC f N)).restrictScalars ℤ =
      Submodule.span ℤ (bridgeGenOC f N) :=
  SetLike.ext (fun x => Set.ext_iff.mp (span_genOC_eq f N) x)

/-- The two balanced relations define the same `ℤ`-submodule of `S ⊗[ℤ] N`. -/
theorem balancedRel_restrictScalars_eq {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    [Module Rᵐᵒᵖ S] (h : ∀ (r : R) (s : S), (MulOpposite.op r) • s = s * f r) (N : Type u)
    [AddCommGroup N] [Module R N] :
    (Work.ORCoherence.balancedRel f N).restrictScalars ℤ = Work.ORHomAlg.balancedRel R S N := by
  rw [balancedRel_OC_eq_span f N, balancedRel_bal_eq_span R S N, genBal_eq_genOC f h N]
  exact span_genOC_restrictScalars f N

/-! ## The comparison isomorphism -/

/-- Two additive maps out of `S ⊗[R] N` which agree on the classes of pure tensors are equal. -/
theorem balanced_hom_ext {R S : Type u} [Ring R] [Ring S] (f : R →+* S) (N : Type u)
    [AddCommGroup N] [Module R N] {P : Type*} [AddCommGroup P]
    {φ ψ : Work.ORCoherence.Balanced f N →+ P}
    (h : ∀ (s : S) (m : N), φ (Work.ORCoherence.Balanced.tmul f s m) =
      ψ (Work.ORCoherence.Balanced.tmul f s m)) : φ = ψ := by
  refine AddMonoidHom.ext fun x => ?_
  refine Submodule.Quotient.induction_on (p := Work.ORCoherence.balancedRel f N) x ?_
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => exact h s m
  | add a b ha hb => rw [Submodule.Quotient.mk_add, map_add, map_add, ha, hb]

/-- The comparison isomorphism between the two balanced tensor products. -/
noncomputable def balancedTensorIso {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    [Module Rᵐᵒᵖ S] (h : ∀ (r : R) (s : S), (MulOpposite.op r) • s = s * f r) (N : Type u)
    [AddCommGroup N] [Module R N] :
    Work.ORCoherence.Balanced f N ≃ₗ[ℤ] Work.ORHomAlg.BalancedTensor R S N :=
  Submodule.quotEquivOfEq ((Work.ORCoherence.balancedRel f N).restrictScalars ℤ)
    (Work.ORHomAlg.balancedRel R S N) (balancedRel_restrictScalars_eq f h N)

@[simp]
theorem balancedTensorIso_tmul {R S : Type u} [Ring R] [Ring S] (f : R →+* S) [Module Rᵐᵒᵖ S]
    (h : ∀ (r : R) (s : S), (MulOpposite.op r) • s = s * f r) (N : Type u)
    [AddCommGroup N] [Module R N] (s : S) (m : N) :
    balancedTensorIso f h N (Work.ORCoherence.Balanced.tmul f s m) =
      Work.ORHomAlg.BalancedTensor.tmul R s m := by
  change Submodule.quotEquivOfEq ((Work.ORCoherence.balancedRel f N).restrictScalars ℤ)
      (Work.ORHomAlg.balancedRel R S N) (balancedRel_restrictScalars_eq f h N)
      (Submodule.Quotient.mk (p := (Work.ORCoherence.balancedRel f N).restrictScalars ℤ)
        (s ⊗ₜ[ℤ] m)) =
    Submodule.Quotient.mk (p := Work.ORHomAlg.balancedRel R S N) (s ⊗ₜ[ℤ] m)
  rw [Submodule.quotEquivOfEq_mk]

/-- The comparison isomorphism is natural in the second variable. -/
theorem balancedTensorIso_natural {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    [Module Rᵐᵒᵖ S] (h : ∀ (r : R) (s : S), (MulOpposite.op r) • s = s * f r) (N : Type u)
    [AddCommGroup N] [Module R N] {N' : Type u} [AddCommGroup N'] [Module R N']
    (g : N →ₗ[R] N') (x : Work.ORCoherence.Balanced f N) :
    balancedTensorIso f h N' (Work.ORCoherence.Balanced.map f g x) =
      Work.ORHomAlg.BalancedTensor.lTensor (M := S) g (balancedTensorIso f h N x) := by
  let φ : Work.ORCoherence.Balanced f N →+ Work.ORHomAlg.BalancedTensor R S N' :=
    { toFun := fun x => balancedTensorIso f h N' (Work.ORCoherence.Balanced.map f g x)
      map_zero' := by simp
      map_add' := by intro a b; simp [map_add] }
  let ψ : Work.ORCoherence.Balanced f N →+ Work.ORHomAlg.BalancedTensor R S N' :=
    { toFun := fun x => Work.ORHomAlg.BalancedTensor.lTensor (M := S) g
        (balancedTensorIso f h N x)
      map_zero' := by simp
      map_add' := by intro a b; simp [map_add] }
  have hφψ : φ = ψ := by
    apply balanced_hom_ext f N
    intro s m
    change balancedTensorIso f h N' (Work.ORCoherence.Balanced.map f g
        (Work.ORCoherence.Balanced.tmul f s m)) =
      Work.ORHomAlg.BalancedTensor.lTensor (M := S) g
        (balancedTensorIso f h N (Work.ORCoherence.Balanced.tmul f s m))
    rw [Work.ORCoherence.Balanced.map_tmul, balancedTensorIso_tmul, balancedTensorIso_tmul,
      Work.ORHomAlg.BalancedTensor.lTensor_tmul]
  exact congrFun (congrArg DFunLike.coe hφψ) x

/-! ## The natural isomorphism of functors -/

/-- The functor `N ↦ S ⊗[R] N` of the `ORCoherence` chapter, forgotten down to `ℤ`-modules,
and the functor `N ↦ S ⊠[R] N` of the `ORHomAlg` chapter are naturally isomorphic. -/
theorem balancedTensor_comp_forgetInt_iso {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    [Module Rᵐᵒᵖ S] (h : ∀ (r : R) (s : S), (MulOpposite.op r) • s = s * f r) :
    Nonempty (CategoryTheory.Functor.comp (Work.ORCoherence.tensorFunctor f) (forgetInt S) ≅
      Work.ORHomAlg.tensorLeftFunctor (R := R) S) := by
  refine ⟨?_⟩
  refine NatIso.ofComponents
    (fun X => LinearEquiv.toModuleIso (balancedTensorIso f h (X : Type u))) ?_
  intro X Y g
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact balancedTensorIso_natural f h (X : Type u) g.hom x

end Work.ORHomAlg.Bridge
