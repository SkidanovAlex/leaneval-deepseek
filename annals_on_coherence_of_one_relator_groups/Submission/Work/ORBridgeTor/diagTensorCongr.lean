import Mathlib
import Submission.Work.ORHomAlg.JL52.DiagTensorDefs

namespace Work.ORBridgeTor

open scoped TensorProduct

universe u

/-- **`id_S ⊗ f` is `K[G]`-linear for the diagonal `K[G]`-module structures** of
`Submission/Work/ORHomAlg/JL52/DiagTensorDefs.lean`.

If `f : X →ₗ[K] Y` is moreover `K[G]`-linear, then the `K`-linear map
`TensorProduct.map (LinearMap.id) f = LinearMap.lTensor S f` commutes with the diagonal action of
`K[G]` on `S ⊗[K] X` and `S ⊗[K] Y`.

Note that no `IsScalarTower K (K[G]) X`/`IsScalarTower K (K[G]) Y` hypothesis is needed: the
statement never transports the `K`-scalar action of `X`/`Y`, only the `K`-linearity of the map on
pure tensors. -/
theorem lTensor_diag_smul {K : Type u} [Field K] {G : Type u} [Group G]
    {S : Type u} [Ring S] [Algebra K S] [Module (MonoidAlgebra K G) S]
    [SMulCommClass K (MonoidAlgebra K G) S]
    {X Y : Type u} [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X]
    [AddCommGroup Y] [Module K Y] [Module (MonoidAlgebra K G) Y]
    [SMulCommClass K (MonoidAlgebra K G) Y]
    (f : X →ₗ[K] Y)
    (hf : ∀ (r : MonoidAlgebra K G) (x : X), f (r • x) = r • f x) :
    ∀ (r : MonoidAlgebra K G) (z : TensorProduct K S X),
      TensorProduct.map (LinearMap.id : S →ₗ[K] S) f (r • z) =
        r • TensorProduct.map (LinearMap.id : S →ₗ[K] S) f z := by
  intro r
  induction r using MonoidAlgebra.induction_on with
  | of m =>
    intro z
    rw [MonoidAlgebra.of_apply, Work.ORHomAlg.JL52.diag_smul_def,
        Work.ORHomAlg.JL52.diag_smul_def,
        Work.ORHomAlg.JL52.diagRingHom_single, Work.ORHomAlg.JL52.diagRingHom_single]
    change TensorProduct.map (LinearMap.id : S →ₗ[K] S) f
        (Work.ORHomAlg.JL52.diagElem S X m z)
      = Work.ORHomAlg.JL52.diagElem S Y m (TensorProduct.map (LinearMap.id : S →ₗ[K] S) f z)
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp only [Work.ORHomAlg.JL52.diagElem_tmul, TensorProduct.map_tmul, LinearMap.id_apply, hf]
    | add p q hp hq => simp only [map_add, hp, hq]
  | add r s hr hs =>
    intro z
    rw [add_smul, map_add, hr z, hs z, add_smul]
  | smul c r hr =>
    intro z
    simp only [Work.ORHomAlg.JL52.diag_smul_def, Work.ORHomAlg.JL52.diagRingHom_smul,
      LinearMap.smul_apply, LinearMap.map_smul]
    simp only [← Work.ORHomAlg.JL52.diag_smul_def, hr]

theorem diagTensorCongr (K : Type u) [Field K] (G : Type u) [Group G]
    (S : Type u) [Ring S] [Algebra K S] [Module (MonoidAlgebra K G) S]
    [SMulCommClass K (MonoidAlgebra K G) S]
    (X Y : Type u) [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X]
    [AddCommGroup Y] [Module K Y] [Module (MonoidAlgebra K G) Y]
    [SMulCommClass K (MonoidAlgebra K G) Y]
    (f : X →ₗ[K] Y) (g : Y →ₗ[K] X)
    (hf : ∀ (r : MonoidAlgebra K G) (x : X), f (r • x) = r • f x)
    (hg : ∀ (r : MonoidAlgebra K G) (y : Y), g (r • y) = r • g y)
    (hfg : ∀ x : X, g (f x) = x) (hgf : ∀ y : Y, f (g y) = y) :
    Nonempty ((TensorProduct K S X) ≃ₗ[MonoidAlgebra K G] (TensorProduct K S Y)) := by
  have hA : ∀ (r : MonoidAlgebra K G) (z : TensorProduct K S X),
      LinearMap.lTensor S f (r • z) = r • LinearMap.lTensor S f z :=
    fun r z => lTensor_diag_smul f hf r z
  have hB : ∀ (r : MonoidAlgebra K G) (z : TensorProduct K S Y),
      LinearMap.lTensor S g (r • z) = r • LinearMap.lTensor S g z :=
    fun r z => lTensor_diag_smul g hg r z
  have hcomp1 : (LinearMap.lTensor S g).comp (LinearMap.lTensor S f) = LinearMap.id := by
    have h : g.comp f = (LinearMap.id : X →ₗ[K] X) := LinearMap.ext hfg
    rw [← LinearMap.lTensor_comp (M := S) g f, h, LinearMap.lTensor_id]
  have hcomp2 : (LinearMap.lTensor S f).comp (LinearMap.lTensor S g) = LinearMap.id := by
    have h : f.comp g = (LinearMap.id : Y →ₗ[K] Y) := LinearMap.ext hgf
    rw [← LinearMap.lTensor_comp (M := S) f g, h, LinearMap.lTensor_id]
  exact ⟨{ toLinearMap :=
             { toFun := LinearMap.lTensor S f
               map_add' := fun a b => (LinearMap.lTensor S f).map_add a b
               map_smul' := hA }
           invFun := LinearMap.lTensor S g
           left_inv := fun z => by
             have h := congrArg (fun φ => φ z) hcomp1
             simpa using h
           right_inv := fun z => by
             have h := congrArg (fun φ => φ z) hcomp2
             simpa using h }⟩

end Work.ORBridgeTor
