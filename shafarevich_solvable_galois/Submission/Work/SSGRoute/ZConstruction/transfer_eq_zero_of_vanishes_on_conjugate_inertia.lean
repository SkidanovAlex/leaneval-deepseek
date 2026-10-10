import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZConstruction.Reduction
import Submission.Work.SSGRoute.place_basics
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZConstruction

open scoped Pointwise

theorem transfer_eq_zero_of_vanishes_on_conjugate_inertia {p : ℕ} [Fact p.Prime] {k Ω : Type}
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [Normal k K] [Fintype (K ≃ₐ[k] K)]
    {E : Type} [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]
    {z : (Ω ≃ₐ[k] Ω) → E} {sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)}
    (hsec : ∀ s : K ≃ₐ[k] K, SSGRoute.res k K (sec s) = s)
    (B : ValuationSubring Ω) (hsplitK : SSGRoute.IsSplitIn k K B)
    (hvan : ∀ (s : K ≃ₐ[k] K) (τ : Ω ≃ₐ[k] Ω), τ ∈ K.fixingSubgroup →
      SSGRoute.IsInertia k ((sec s)⁻¹ • B) τ → z τ = 0) :
    ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k B → SSGRoute.IsInertia k B σ →
      Work.SSGRoute.transfer z sec σ = 0 := by
  intro σ hσd hσI
  unfold Work.SSGRoute.transfer
  refine Finset.sum_eq_zero fun s _ => ?_
  -- the conjugate of `σ` by `sec s` lies in `G_K`
  have hmem : (sec s)⁻¹ * σ * sec s ∈ K.fixingSubgroup :=
    conj_sec_mem_fixingSubgroup hsec s (hsplitK hσd)
  -- and it is an inertia element of the conjugate place `(sec s)⁻¹ • B`
  have hin : SSGRoute.IsInertia k ((sec s)⁻¹ • B) ((sec s)⁻¹ * σ * sec s) :=
    (isInertia_conj B (sec s)⁻¹ σ).mpr hσI
  rw [hvan s ((sec s)⁻¹ * σ * sec s) hmem hin, smul_zero]

end Work.SSGRoute.ZConstruction
