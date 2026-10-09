import Mathlib
import Submission.Work.SSGRoute.PT.pt_canonical_assembly
import Submission.Work.SSGRoute.PT.finite_H1loc
import Submission.Work.SSGRoute.PT.pt_counting_assembly
import Submission.Work.SSGRoute.PT.finite_primalClasses_general
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finiteness of the primal and Tate-dual local class spaces

Both halves of the statement are instances of the same finiteness theorem for the local class
space `primalClasses p k Ω K X S C`, namely `Work.SSGRoute.PT.finite_primalClasses_general`:
the product of the local `H¹`-spaces at the decomposition groups of the finite places of `S`
(finite by local Tate duality, `Work.SSGRoute.PT.finite_H1loc`) and at the groups `⟨c⟩` generated
by the involutions of `C` (finite because `⟨c⟩` has order `≤ 2`), for a *finite* coefficient
module `X`.

* primal side: `X = M`, and `Finite M` is a hypothesis;
* dual side: `X = DualMod p (M ⊗[ZMod p] T)` is the Tate dual `M^∨(1)`.  Its finiteness is the
  composition of the two Mathlib-level facts already established in the workspace,
  `Work.SSGRoute.finite_tensor` (`Finite (M ⊗[ZMod p] T)` from `Finite M`, `Finite T` — tensor
  products of finite modules over the finite ring `ZMod p` are finite) and
  `Work.SSGRoute.finite_dualMod` (`Finite (DualMod p X)` from `Finite X` — the `𝔽_p`-linear dual
  embeds into the finite function space `X → ZMod p`).
-/

open scoped TensorProduct

set_option linter.style.haveILetI false

namespace Work.SSGRoute.PT

theorem pt_classes_finite
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (C : Finset (Ω ≃ₐ[k] Ω)) (hCinv : ∀ c ∈ C, c ^ 2 = 1) :
    _root_.Work.SSGRoute.PT.PrimalClassesFinite p k Ω K M S C ∧
      _root_.Work.SSGRoute.PT.DualClassesFinite p k Ω K T M S C := by
  -- the coefficient module of the Tate dual is finite: `M ⊗[ZMod p] T` and then its `𝔽_p`-dual
  haveI hMT : Finite (TensorProduct (ZMod p) M T) := SSGRoute.finite_tensor M T
  haveI hD : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
    SSGRoute.finite_dualMod _
  exact ⟨finite_primalClasses_general p k Ω K M S hSfin C hCinv,
    finite_primalClasses_general p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S hSfin C hCinv⟩

end Work.SSGRoute.PT
