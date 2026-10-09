import Mathlib
import Submission.Work.SSGRoute.SSGStage.e1aLandingFinCompat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The finite-place landing clause from the *continuous* crux (a second route)

`SSGStage.e1aLandingFinCompat` is the finite-place half of the E1a landing clause.  Its only
unproved input on disk is the abstract-hypothesis node `PT.e1aBetaCan_localDictionary_fin_compat`
(untouched since 2026-09-30, two `sorry`s).  This file records the **continuous** route to the same
statement, whose single input is the honest `CRUX-a` of
`PT/NOTE_e1aChainC_localComparison_session12.md` §2 —

    resH1_{decomp k A} (e1cEquiv R z) = 0
      ⟹  (extRes_{decompK q} z).comp (mk₀ (unitsToLocalUnits k K (ofFinite q))) = 0,

stated on disk (statement-only, `sorry`) as
`Work.SSGRoute.PT.extRes_e1cEquiv_eq_zero_of_resH1_e1cEquiv_eq_zero`.  That file's import cone
currently fails to build (`E1aClean/localExtTransport_PhiEgen.lean` times out at 4M heartbeats), so
the crux is taken here as an **explicit hypothesis** — the statement is reproduced verbatim, and the
assembly below is independent of that lane's build state.

The assembly is exactly the chain of `PT/NOTE_e1aChainC_localComparison_session12.md` §1:

    akRes_{D_A}(e1aChainC y) = 0
      → resH1_{D_A}(e1cEquiv R ((e1aSyzShift N)⁻¹ y)) = 0     [SSGStage, proved]
      → (extRes_{D_q} z).comp (mk₀ (unitsToLocalUnits)) = 0    [CRUX-a]
      → extLoc_q (extToIdeles y) = 0                           [PT brick (F), proved]

so the whole finite-place landing clause becomes a single named input.  `ExtChain.e1aLandingClause_fixed`
is the whole landing clause on top of this and of the archimedean leaf; see
`ExtChain/NOTE_A1_A2_session_2026-10-01b.md` §8/§9/§10.
-/

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

/-- **The finite-place landing clause, via `CRUX-a`.**  The statement is verbatim that of
`Work.SSGRoute.SSGStage.e1aLandingFinCompat`; the extra argument `hcruxA` is exactly
`Work.SSGRoute.PT.extRes_e1cEquiv_eq_zero_of_resH1_e1cEquiv_eq_zero`, reproduced so that this file
does not depend on that lane's (currently non-building) import cone. -/
theorem e1aLandingFinCompat_via_cruxA (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    [hRfin : Module.Finite ℤ ↑(CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))).V]
    (hcruxA : ∀ (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
        [Module.Finite ℤ ↑(CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)).V]
        (z : CategoryTheory.Abelian.Ext.{0}
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))
          (SSGRoute.PTExt.unitsK k K) 1),
      Work.SSGRoute.PT.H2Fin.resH1 (SSGRoute.decomp k A)
          (Work.SSGRoute.homCoind k Ω K
            (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)))
          (Work.SSGRoute.ExtChain.e1cEquiv
            (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) z) = 0 →
        (SSGRoute.PTExt.extRes
            (SSGRoute.PTExt.decompK (k := k)
              (NK.GlobalCFT.Place.ofFinite q)).subtype z).comp
          (CategoryTheory.Abelian.Ext.mk₀
            (NK.HassePrinciple.unitsToLocalUnits k K (NK.GlobalCFT.Place.ofFinite q)))
          (add_zero 1) = 0) :
    ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
      @Work.AbsoluteKummer.akRes (Ω ≃ₐ[k] Ω) _ _ (SSGRoute.decomp k A) E _
        (DistribMulAction.compHom E (SSGRoute.res k K))
        (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y) = 0 →
      SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofFinite q)
        (SSGRoute.PTExt.extToIdeles (k := k) y) = 0 := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  intro y hy
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI hNfin : Finite (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  have h1 := Work.SSGRoute.SSGStage.resH1_e1cEquiv_eq_zero_of_akRes_e1aChainC_eq_zero
    p k Ω K ζ hζ hζK T hT E (SSGRoute.decomp k A) (Work.SSGRoute.HS.isClosed_decomp A) y hy
  have h2 := hcruxA (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
    ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
      (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))).symm y) h1
  rw [← AddEquiv.apply_symm_apply (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
    (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))) y]
  exact Work.SSGRoute.SSGStage.extLoc_extToIdeles_e1aSyzShift_eq_zero K
    (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
    (NK.GlobalCFT.Place.ofFinite q)
    ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
      (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))).symm y) h2

end

end Work.SSGRoute.ExtChain
