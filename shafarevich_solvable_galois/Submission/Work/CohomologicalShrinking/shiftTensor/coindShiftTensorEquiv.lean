import Mathlib
import Submission.Work.CohomologicalShrinking.Models
import Submission.Work.Tate.DimensionShiftH
import Submission.Work.CohomologicalShrinking.coindShiftAddEquivTensor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u₀

namespace Work.CohomologicalShrinking.shiftTensor

theorem coindShiftTensorEquiv (p : ℕ) (G : Type*) [Group G] [Fintype G] :
    ∃ e : ∀ (A : Type u₀) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
        [SMulCommClass G (ZMod p) A],
        (Work.Tate.coindShift G A) ≃+ TensorProduct (ZMod p) A (Work.CohomologicalShrinking.igDual p G),
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
          = ((LinearMap.rTensor (Work.CohomologicalShrinking.igDual p G) φ).toAddMonoidHom).comp (e A).toAddMonoidHom) :=
  Work.CohomologicalShrinking.coindShiftAddEquivTensor p G

end Work.CohomologicalShrinking.shiftTensor
