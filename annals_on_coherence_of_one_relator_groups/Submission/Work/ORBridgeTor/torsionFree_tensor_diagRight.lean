import Mathlib
import Submission.Work.ORBridgeTor.Defs
import Submission.Work.ORBridgeTor.Mirror
import Submission.Work.ORTorsion.Main
import Submission.Work.ORTorsion.Defs
import Submission.Work.ORFlatness.DiagonalRight

namespace Work.ORBridgeTor

/-!
This is `Work.ORBridgeTor.torsionFree_diagRight_of_diagLeft` (in
`Submission/Work/ORBridgeTor/Mirror.lean`) instantiated at
`S := ↥(L.D ⊤)`, `φ := MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop`,
`N := Subgroup.normalClosure {L.u}`, with its abstract hypothesis `hleft` discharged by node N8's
`Work.ORTorsion.torsionFree_tensor`.

Proof work to expect: the left action of `torsionFree_tensor` is the `SMul` instance
`Work.ORTorsion.TorsionData.instDiagTopSmul` (priority 2000), whose value on `m` is
`Work.ORTorsion.diagRingHom (V := V) (MonoidHom.id G) L.genTop γ m` (see
`Work.ORTorsion.TorsionData.instDiagTopSmul_apply`).  It agrees with
`Work.ORBridgeTor.diagLeftAct K G ↥(L.D ⊤) φ V γ m` because the underlying group actions agree
(`Work.ORBridgeTor.diagRingHomV_single_tmul` versus
`Work.ORTorsion.diagElem_apply_tmul` and
`Work.ORFlatness.gElemR K G ↥(L.D ⊤) φ g = L.genTop g`, which holds by `MonoidAlgebra.lift_single`
and `one_smul`); prove the two `MonoidAlgebra.lift`s of `G →* Module.End` equal and conclude with
`TensorProduct.induction_on` on pure tensors.
-/
open TensorProduct MulOpposite

universe u

set_option maxHeartbeats 1000000

section Helpers

variable (K : Type u) [Field K] (G : Type u) [Group G] (U : Type u) [Ring U] [Algebra K U]
variable (L : Work.ORTorsion.TorsionData K G U)

/-- The element of `↥(L.D ⊤)` attached to `g` by `φ = MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop`
is `L.genTop g`. -/
theorem gElemR_lift_genTop (g : G) :
    Work.ORFlatness.gElemR K G ↥(L.D ⊤)
      (MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop) g = L.genTop g := by
  rw [Work.ORFlatness.gElemR, MonoidAlgebra.lift_single, one_smul]

variable (V : Type u) [AddCommGroup V] [Module K V] [Module (MonoidAlgebra K G) V]
variable [IsScalarTower K (MonoidAlgebra K G) V] [SMulCommClass K (MonoidAlgebra K G) V]

/-- The diagonal group action of `G` on `V ⊗[K] ↥(L.D ⊤)` coming from `Work.ORTorsion` (acting on
`V` through `K[G]` and on `↥(L.D ⊤)` through `L.genTop`) coincides with the one used by
`Work.ORBridgeTor.diagLeftAct`, which acts through `φ = MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop`:
the two underlying group actions act on the left tensor factor in the same way and map `g` to
`L.genTop g` on the right tensor factor (`Work.ORFlatness.gElemR` evaluated on the lift). -/
theorem diagGroupHom_id_genTop_eq_diagMonoidHomV :
    Work.ORTorsion.diagGroupHom (K := K) (V := V) (M := ↥(L.D ⊤)) (MonoidHom.id G) L.genTop
      = diagMonoidHomV K G ↥(L.D ⊤)
          (MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop) V := by
  ext g : 1
  apply LinearMap.ext
  intro z
  show Work.ORTorsion.diagElem (K := K) (V := V) (MonoidHom.id G) L.genTop g z
      = diagLinV K G ↥(L.D ⊤)
          (MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop) V g z
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul v s =>
      rw [Work.ORTorsion.diagElem_apply_tmul, diagLinV_tmul,
        gElemR_lift_genTop K G U L g, MonoidHom.id_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- On `V ⊗[K] ↥(L.D ⊤)`, the diagonal action `Work.ORBridgeTor.diagLeftAct` attached to
`φ = MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop` is definitionally the diagonal action of node N8
(`Work.ORTorsion.TorsionData.instDiagTopSmul`).  This is the comparison that lets
`Work.ORTorsion.torsionFree_tensor` discharge the `hleft` slot of
`Work.ORBridgeTor.torsionFree_diagRight_of_diagLeft`. -/
theorem diagLeftAct_lift_genTop_eq_smul (γ : MonoidAlgebra K G) (m : V ⊗[K] ↥(L.D ⊤)) :
    diagLeftAct K G ↥(L.D ⊤)
      (MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop) V γ m = γ • m := by
  have hgroup := diagGroupHom_id_genTop_eq_diagMonoidHomV K G U L V
  show ((MonoidAlgebra.lift K (Module.End K (V ⊗[K] ↥(L.D ⊤))) G
      (diagMonoidHomV K G ↥(L.D ⊤)
        (MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop) V)) γ) m
    = ((MonoidAlgebra.lift K (Module.End K (V ⊗[K] ↥(L.D ⊤))) G
      (Work.ORTorsion.diagGroupHom (K := K) (V := V) (M := ↥(L.D ⊤))
        (MonoidHom.id G) L.genTop)).toRingHom γ) m
  rw [hgroup]
  rfl

end Helpers

/-- **Lemma 5.1′ in the right-module form for `S = D(⊤)`.**  This is
`Work.ORBridgeTor.torsionFree_diagRight_of_diagLeft` with its abstract left-module hypothesis
`hleft` discharged by node N8's `Work.ORTorsion.torsionFree_tensor`: the two diagonal actions on
`V ⊗[K] ↥(L.D ⊤)` agree (`Work.ORBridgeTor.diagLeftAct_lift_genTop_eq_smul`), so N8's statement
supplies the `hleft` slot verbatim. -/
theorem torsionFree_tensor_diagRight (K : Type u) [Field K] (G : Type u) [Group G]
    (U : Type u) [Ring U] [Algebra K U] (L : Work.ORTorsion.TorsionData K G U)
    (ι : Work.ORBridgeTor.AntiAut K ↥(L.D ⊤))
    (hι : ∀ g : G, ι (Work.ORFlatness.gElemR K G ↥(L.D ⊤)
        (MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop) g) =
      Work.ORFlatness.gElemR K G ↥(L.D ⊤)
        (MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop) g⁻¹)
    (X : Type u) [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [IsScalarTower K (MonoidAlgebra K G) X] [SMulCommClass K (MonoidAlgebra K G) X]
    (β : MonoidAlgebra K G)
    (hβ : Set.InjOn (QuotientGroup.mk (s := Subgroup.normalClosure {L.u})) β.coeff.support)
    (hβ0 : β ≠ 0) :
    letI := Work.ORFlatness.diagRightModule K G ↥(L.D ⊤)
      (MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop) X
    Function.Injective (fun z : TensorProduct K (↥(L.D ⊤)) X => (MulOpposite.op β) • z) := by
  refine torsionFree_diagRight_of_diagLeft (K := K) (G := G)
    (S := ↥(L.D ⊤)) (φ := MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop)
    (N := Subgroup.normalClosure {L.u}) ?_ ι hι X β hβ hβ0
  intro V _ _ _ _ _ γ hγ hγ0
  have hfun : (fun m : V ⊗[K] ↥(L.D ⊤) => diagLeftAct K G ↥(L.D ⊤)
        (MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop) V γ m)
      = (fun m : V ⊗[K] ↥(L.D ⊤) => γ • m) :=
    funext fun m => diagLeftAct_lift_genTop_eq_smul K G U L V γ m
  rw [hfun]
  exact Work.ORTorsion.torsionFree_tensor L V γ hγ hγ0

end Work.ORBridgeTor
