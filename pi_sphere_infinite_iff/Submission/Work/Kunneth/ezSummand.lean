import Mathlib
import Submission.Work.Kunneth.Basic
import Submission.Work.KunnethEZ.Defs
import Submission.Work.KunnethEZ.ezChain_isCycle

namespace Work.Kunneth

/-- The `ℤ`-action on a space of linear maps coming from its additive group structure is
pointwise. -/
theorem zsmul_linearMap_apply {M P : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup P]
    [Module ℤ P] (g : M →ₗ[ℤ] P) (c : ℤ) (x : M) : (c • g) x = c • g x := by
  let ev : (M →ₗ[ℤ] P) →+ P :=
    { toFun := fun h => h x, map_zero' := rfl, map_add' := fun a b => rfl }
  exact map_zsmul ev c g

theorem ezSummand (X Y : SSet) (p q : ℕ) :
    ∃ f : Work.Kunneth.tpSummand (Work.Kunneth.sChain X) (Work.Kunneth.sChain Y) p q →ₗ[ℤ]
        ↥((Work.Kunneth.sChain (Work.Kunneth.sProd X Y)).X (p + q)),
      ∀ (σ : X.obj (Opposite.op (SimplexCategory.mk p))) (τ : Y.obj (Opposite.op (SimplexCategory.mk q))),
        f (TensorProduct.tmul ℤ ((X.ιChainComplex (R := Work.Kunneth.zz) σ).hom 1)
            ((Y.ιChainComplex (R := Work.Kunneth.zz) τ).hom 1))
          = Work.KunnethEZ.ezChain p q X Y ((X.ιChainComplex (R := Work.Kunneth.zz) σ).hom 1)
              ((Y.ιChainComplex (R := Work.Kunneth.zz) τ).hom 1) := by
  refine ⟨TensorProduct.lift (LinearMap.mk₂ ℤ
    (fun a b => ((Work.KunnethEZ.ezBilin p q X Y) ((Work.Cohomology.Crux33.coords X p) a))
        ((Work.Cohomology.Crux33.coords Y q) b))
    ?_ ?_ ?_ ?_), ?_⟩
  · intro a a' b
    simp only [map_add, LinearMap.add_apply]
  · intro c a b
    simp only [map_smul]
    rw [← Work.KunnethEZ.zsmulToSMul_eq (↥((sChain (sProd X Y)).X (p + q)))]
    exact zsmul_linearMap_apply
      ((Work.KunnethEZ.ezBilin p q X Y) ((Work.Cohomology.Crux33.coords X p) a)) c
      ((Work.Cohomology.Crux33.coords Y q) b)
  · intro a b b'
    simp only [map_add]
  · intro c a b
    simp only [map_smul]
    rw [← Work.KunnethEZ.zsmulToSMul_eq (↥((sChain (sProd X Y)).X (p + q)))]
    exact map_zsmul
      (((Work.KunnethEZ.ezBilin p q X Y) ((Work.Cohomology.Crux33.coords X p) a)).toAddMonoidHom) c
      ((Work.Cohomology.Crux33.coords Y q) b)
  · intro σ τ
    rw [TensorProduct.lift.tmul]
    exact (Work.KunnethEZ.ezChain_eq_ezBilin p q X Y _ _).symm

end Work.Kunneth
