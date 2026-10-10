import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
import Submission.Work.CohomologicalShrinking.bridge.exists_bridge_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking

theorem exists_bridge (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] (i j : ℕ)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] :
    ∃ γ : ∀ m : ℕ, (↑(groupHomology.H1 (flowRepG p G m i j T)) : Type) →+
      Work.Tate.Hm1 G (TensorProduct (ZMod p) (E p G m i j)
        (TensorProduct (ZMod p) T (augIdeal p G))),
      (∀ m, Function.Injective (γ m)) ∧ (∀ m, Function.Surjective (γ m)) ∧
      (∀ ⦃m n : ℕ⦄ (Φ : OperatorMap G m n)
        (y : (↑(groupHomology.H1 (flowRep p G m i j T)) : Type)),
        (Φ.hm1Map p G (TensorProduct (ZMod p) T (augIdeal p G)))
            (γ m (flowHSβ p G i j T m y))
          = γ n (flowHSβ p G i j T n (flowZMap (p := p) G i j Φ T y))) :=
  bridge.exists_bridge_aux p G i j T

end Work.CohomologicalShrinking
