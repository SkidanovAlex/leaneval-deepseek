import Mathlib
import Submission.Work.SSGRoute.PT.e1a_beta_can
import Submission.Work.SSGRoute.PT.e1aBetaCan_aux
import Submission.Work.SSGRoute.PT.e1aBetaCan_localDictionary_fin_compat
import Submission.Work.SSGRoute.ShaCocycles
import Submission.Work.SSGRoute.PT.e1a_sha2_mem_deltaRange_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cocycle-level hypothesis of the E1a comparison square, in continuous form

The finite-place comparison square of the E1a landing clause consumes the *continuous* vanishing

  `akRes_{D_A} (e1aChainC y) = 0`

of the canonical chain class at the decomposition group, while the hypothesis of the target
(`comparisonSquareFin`, i.e. `PT.e1aChainC_localComparison`) is the *cocycle-level* statement

  `∃ c ∈ Z²_c(Ω≐k, E),  H2π c = e1aChainC y  ∧  c|D_A ∈ B²_c(D_A)`.

This module proves the implication between them, **directly** — without any injectivity of the
forgetful map `akToGCH2` into the abstract cohomology model (which is the gap recorded in
`PT/e1aBetaCan_localDictionary_fin_compat.lean` and is *not* needed on this route): the restricted
cocycle `c|D_A` is an honest continuous coboundary, so its class in `H²_c(D_A,E)` vanishes, and
`akRes_H2π` computes `akRes`.
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

/-- **The continuous vanishing from the cocycle-level hypothesis.** -/
theorem akRes_e1aChainC_eq_zero_of_coboundary
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (c : @Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) E _ _ _
      (DistribMulAction.compHom E (SSGRoute.res k K)))
    (hc : @Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
        (DistribMulAction.compHom E (SSGRoute.res k K)) c =
      Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y)
    (hcob : SSGRoute.IsCoboundary2On (SSGRoute.res k K) (SSGRoute.decomp k A)
      (fun g h => c.1 (g, h))) :
    @Work.AbsoluteKummer.akRes (Ω ≃ₐ[k] Ω) _ _ (SSGRoute.decomp k A) E _
        (DistribMulAction.compHom E (SSGRoute.res k K))
        (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y) = 0 := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  rw [← hc, Work.AbsoluteKummer.akRes_H2π (SSGRoute.decomp k A) E c.1 c.2]
  rw [Work.AbsoluteKummer.H2π_eq_zero_iff, Work.AbsoluteKummer.mem_B2_iff]
  obtain ⟨b, hbloc, hbeq⟩ := hcob
  refine ⟨fun u : ↥(SSGRoute.decomp k A) => b (u : Ω ≃ₐ[k] Ω), ?_, ?_⟩
  · exact Work.SSGRoute.PT.isLocallyConstant_subtype_of_isLocConstOn (SSGRoute.decomp k A) hbloc
  · ext q
    obtain ⟨g, h⟩ := q
    show (g : ↥(SSGRoute.decomp k A)) • b (h : Ω ≃ₐ[k] Ω)
        - b ((g * h : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) + b (g : Ω ≃ₐ[k] Ω)
      = c.1 ((g : Ω ≃ₐ[k] Ω), (h : Ω ≃ₐ[k] Ω))
    rw [show c.1 ((g : Ω ≃ₐ[k] Ω), (h : Ω ≃ₐ[k] Ω))
        = (fun g h => c.1 (g, h)) (g : Ω ≃ₐ[k] Ω) (h : Ω ≃ₐ[k] Ω) from rfl,
      hbeq (g : Ω ≃ₐ[k] Ω) g.2 (h : Ω ≃ₐ[k] Ω) h.2]
    simp only [Subgroup.coe_mul]
    rfl

end Work.SSGRoute.E1aClean
