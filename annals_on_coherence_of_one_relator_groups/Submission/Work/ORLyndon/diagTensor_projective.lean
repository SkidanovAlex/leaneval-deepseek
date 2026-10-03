import Mathlib
import Submission.Work.ORLyndon.DiagTensor
import Submission.Work.ORLyndon.diagTensor_freeSetup
import Submission.Work.ORLyndon.diagTensor_einvE
import Submission.Work.ORLyndon.diagTensor_finsupp

/-!
# Projectivity of the diagonal tensor product

For a field `K`, a group `G` and a left `K[G]`-module `M`, tensoring with `M` over `K` (with the
diagonal `K[G]`-action of `DiagTensor.lean`) preserves projectivity: if `P` is a projective left
`K[G]`-module then so is `P ⊗[K] M`.

The proof is the standard one.  A projective module is a direct summand of a free module: `P →₀ K[G]`
is free and the canonical map `K[G]^{(P)} → P` splits (`Module.projective_def'`).  Tensoring this
splitting with `M` over `K` gives `P ⊗[K] M` as a direct summand of
`(P →₀ K[G]) ⊗[K] M ≃ₗ[K[G]] P →₀ (K[G] ⊗[K] M)` (`Work.ORLyndon.diagTensor_finsupp`), and
`K[G] ⊗[K] M` is a free `K[G]`-module, of rank `dim_K M`, because modules over a field are free
(`diagTensor_selfFree` below, using the diagonal-action infrastructure of
`Submission/Work/ORLyndon/diagTensor_freeSetup.lean`).
-/

open TensorProduct

attribute [-instance] TensorProduct.leftModule TensorProduct.leftDistribMulAction
  TensorProduct.leftHasSMul

namespace Work.ORLyndon

universe u v

/-- `K[G] ⊗[K] M` is a free `K[G]`-module for the diagonal action (of rank `dim_K M`). -/
theorem diagTensor_selfFree {K : Type v} [Field K] {G : Type u} [Group G] {M : Type (max u v)}
    [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
    [IsScalarTower K (MonoidAlgebra K G) M] :
    Module.Free (MonoidAlgebra K G) (TensorProduct K (MonoidAlgebra K G) M) := by
  have hbij : Function.Bijective (dsElin (K := K) (G := G) (M := M)) :=
    ⟨fun x y h => by
        have h2 := congrArg (dsEinv (K := K) (G := G) (M := M)) h
        simpa [dsElin_apply, diagTensor_einvE] using h2,
      fun y => ⟨dsEinv (K := K) (G := G) (M := M) y, by
        simpa [dsElin_apply] using dsE_einv (K := K) (G := G) (M := M) y⟩⟩
  have e : MonoidAlgebra K G ⊗[K] M ≃ₗ[MonoidAlgebra K G]
      (Module.Free.ChooseBasisIndex K M →₀ MonoidAlgebra K G) :=
    LinearEquiv.ofBijective (dsElin (K := K) (G := G) (M := M)) hbij
  exact Module.Free.of_equiv'
    (Module.Free.of_basis (Finsupp.basisSingleOne (R := MonoidAlgebra K G))) e.symm

theorem diagTensor_projective {K : Type v} [Field K] {G : Type u} [Group G] {M : Type (max u v)} [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M] [IsScalarTower K (MonoidAlgebra K G) M] (P : Type (max u v)) [AddCommGroup P] [Module K P] [Module (MonoidAlgebra K G) P] [IsScalarTower K (MonoidAlgebra K G) P] [Module.Projective (MonoidAlgebra K G) P] : Module.Projective (MonoidAlgebra K G) (TensorProduct K P M) := by
  classical
  -- `P` is a direct summand of the free module `P →₀ K[G]`.
  obtain ⟨s, hs⟩ := Module.projective_def'.mp
    (show Module.Projective (MonoidAlgebra K G) P from inferInstance)
  -- `K[G] ⊗[K] M` is free, hence a direct sum of copies of it is projective.
  haveI : Module.Free (MonoidAlgebra K G)
      (TensorProduct K (MonoidAlgebra K G) M) := diagTensor_selfFree
  haveI : Module.Projective (MonoidAlgebra K G)
      (P →₀ (TensorProduct K (MonoidAlgebra K G) M)) := inferInstance
  -- tensoring a finite-support family with `M` over `K` commutes with the diagonal action.
  obtain ⟨e⟩ := diagTensor_finsupp (K := K) (G := G) (M := M)
    (N := MonoidAlgebra K G) P
  haveI : Module.Projective (MonoidAlgebra K G)
      (TensorProduct K (P →₀ MonoidAlgebra K G) M) :=
    Module.Projective.of_equiv' e.symm
  -- tensor the splitting of `K[G]^{(P)} → P` with `M`.
  refine Module.Projective.of_split
    (i := diagTensorMap (M := M) s)
    (s := diagTensorMap (M := M)
      (Finsupp.linearCombination (MonoidAlgebra K G) (id : P → P))) ?_
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul p m =>
      rw [LinearMap.comp_apply, diagTensorMap_tmul, diagTensorMap_tmul, LinearMap.id_apply]
      have hp : Finsupp.linearCombination (MonoidAlgebra K G) (id : P → P) (s p) = p := by
        rw [← LinearMap.comp_apply, hs, LinearMap.id_apply]
      rw [hp]

end Work.ORLyndon
