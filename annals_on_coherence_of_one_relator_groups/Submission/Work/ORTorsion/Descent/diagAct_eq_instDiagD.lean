import Mathlib
import Submission.Work.ORTorsion.Defs
import Submission.Work.ORTorsion.Descent.DiagAct

namespace Work.ORTorsion.Descent

open scoped TensorProduct

/-- On a ring `A` viewed as a module over itself, multiplication by `a` (the `Module A A`-action
used by `smulEnd`) coincides with `LinearMap.mulLeft K a`. -/
theorem smulEnd_eq_mulLeft {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A] (a : A) :
    (smulEnd (K := K) a : A →ₗ[K] A) = LinearMap.mulLeft K a := by
  ext m
  simp [smulEnd, LinearMap.mulLeft_apply]

/-- The diagonal group action `diagActGroup` on `V ⊗[K] ↥(L.D H)` agrees with the group action
`diagGroupHom` underlying the instance `instDiagD`. -/
theorem diagActGroup_eq_diagGroupHom {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*}
    [Ring U] [Algebra K U] (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (H : Subgroup G) :
    diagActGroup L H ↥(L.D H) = diagGroupHom (K := K) (V := V) H.subtype (L.genD H) := by
  apply MonoidHom.ext
  intro h
  show (TensorProduct.map (gAct (K := K) (V := V) (h : G))
        (smulEnd (K := K) (M := ↥(L.D H)) (L.genD H h)) :
          V ⊗[K] ↥(L.D H) →ₗ[K] V ⊗[K] ↥(L.D H))
      = TensorProduct.map (gAct (K := K) (V := V) (h : G))
          (LinearMap.mulLeft K (L.genD H h))
  rw [smulEnd_eq_mulLeft]

theorem diagAct_eq_instDiagD {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*}
    [Ring U] [Algebra K U] (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (H : Subgroup G) (x : MonoidAlgebra K H) (y : V ⊗[K] ↥(L.D H)) :
    diagAct L H ↥(L.D H) x y = x • y := by
  have hgrp := diagActGroup_eq_diagGroupHom (K := K) (V := V) L H
  have halg : diagAct L H ↥(L.D H)
      = MonoidAlgebra.lift K (Module.End K (V ⊗[K] ↥(L.D H))) H
          (diagGroupHom (K := K) (V := V) H.subtype (L.genD H)) := by
    simp only [diagAct, hgrp]
  rw [halg]
  rfl

end Work.ORTorsion.Descent
