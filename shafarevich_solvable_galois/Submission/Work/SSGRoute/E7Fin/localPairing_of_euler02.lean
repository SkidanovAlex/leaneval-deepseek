import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.H1Pair.Clauses
import Submission.Work.SSGRoute.LTDDefs.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped TensorProduct

set_option maxHeartbeats 1000000

namespace Work.SSGRoute

open H1Pair

/-- **The two local `H¹`-spaces of a decomposition group have the same dimension.** -/
theorem finrank_H1loc_eq_finrank_H1loc_tateDual
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hE : ∃ ε : ℕ, ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Module.Finite (ZMod p) (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A)) ∧
        Module.finrank (ZMod p) (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A)) =
          Module.finrank (ZMod p) (Work.SSGRoute.H0loc p k Ω K M (SSGRoute.decomp k A)) +
            Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) +
            ε * Module.finrank (ZMod p) M)
    (h02 : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) =
        Module.finrank (ZMod p) (Work.SSGRoute.H0loc p k Ω K
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) ∧
      Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) =
        Module.finrank (ZMod p) (Work.SSGRoute.H0loc p k Ω K M (SSGRoute.decomp k A))) :
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Module.finrank (ZMod p) (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A)) =
        Module.finrank (ZMod p) (Work.SSGRoute.H1loc p k Ω K
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) := by
  intro M _ _ _ _ _
  obtain ⟨ε, hε⟩ := hE
  have hdT : Module.finrank (ZMod p) T = 1 := hT.1
  haveI : Finite T := finite_of_finrank_eq_one T hdT
  haveI : Finite (M ⊗[ZMod p] T) := finite_tensor M T
  haveI : Finite (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) :=
    finite_dualMod (M ⊗[ZMod p] T)
  have hdim : Module.finrank (ZMod p) (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) =
      Module.finrank (ZMod p) M := by
    rw [finrank_dualMod (M ⊗[ZMod p] T), finrank_tensor_rankOne M T hdT]
  have h1 := (hε M).2
  have h2 := (hε (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))).2
  have h3 := (h02 M).1
  have h4 := (h02 M).2
  rw [h1, h2, h3, h4, hdim]
  ring

end Work.SSGRoute
