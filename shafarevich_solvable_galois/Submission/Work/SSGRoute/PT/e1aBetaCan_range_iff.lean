import Mathlib
import Submission.Work.SSGRoute.PT.e1a_beta_can
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `e1aBetaCan_image`, step 1: the range form

`e1aBetaCan` is `(e1aChainRangeEquiv).symm ∘ φ.codRestrict` and `e1aChainC` is injective, so for
every class `y` of `Ext²_G(E',Kˣ)`,

  `(∃ b, e1aBetaCan … hmem b = y)  ↔  e1aChainC … y ∈ range φ`,   `φ = Classical.choose
  (sha2_to_H2AK …)`.

This is the first step of the target `PT/e1aBetaCan_image.lean` and identifies its conclusion,
verbatim, with the E1a image clause `range φ = e1aChainC '' ker extToIdeles`; see
`PT/NOTE_e1aBetaCan_image_analysis.md` for the exact remaining input (the chain–localisation
comparison, i.e. the degree-two local dictionary).
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

noncomputable section

/-- **The range form of `e1aBetaCan`.** -/
theorem e1aBetaCan_eq_iff_chainC_mem_range (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (hmem : ∀ b : Work.SSGRoute.Sha2 p k Ω K E,
      (Classical.choose (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K E)) b ∈
        (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E).range) :
    ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
      (∃ b : Work.SSGRoute.Sha2 p k Ω K E,
          Work.SSGRoute.PT.e1aBetaCan p k Ω K ζ hζ hζK T hT E hmem b = y) ↔
        Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y ∈
          (Classical.choose (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K E)).range := by
  intro y
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, (e1aBetaCan_chainC p k Ω K ζ hζ hζK T hT E hmem b).symm⟩
  · rintro ⟨b, hb⟩
    refine ⟨b, e1aChainC_injective p k Ω K ζ hζ hζK T hT E ?_⟩
    rw [e1aBetaCan_chainC p k Ω K ζ hζ hζK T hT E hmem b, hb]

end

end Work.SSGRoute.PT
