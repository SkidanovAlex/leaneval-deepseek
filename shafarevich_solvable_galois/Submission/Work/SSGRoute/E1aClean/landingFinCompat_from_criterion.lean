import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PTdualControl.extExact
import Submission.Work.SSGRoute.SSGStage.e1aLandingFinCompat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The finite-place landing clause from the local criterion

`Work.SSGRoute.SSGStage.e1aLandingFinCompat` (the finite-place half of the E1a landing clause) is
proved from `Work.SSGRoute.E1aClean.finLocalCriterion` — the *sharp form* of the per-place
comparison, in which the restriction hypothesis is written on the `E1c`-dictionary class at the
canonical syzygy:

* `akRes_{D_A} (e1aChainC y) = 0` ⟹ `resH1_{D_A} (e1cEquiv R z) = 0` with
  `z = (e1aSyzShift N)⁻¹ y`, `R = ker (freeCover N)`, `N = E' = DualMod p (E ⊗ T)`
  (`SSGStage.resH1_e1cEquiv_eq_zero_of_akRes_e1aChainC_eq_zero`, proved);
* the criterion turns this into the vanishing of the *localised* degree-one class
  `(extRes_{D_q} z) ∘ mk₀ (unitsToLocalUnits) = 0`;
* the degree reduction `SSGStage.extLoc_extToIdeles_e1aSyzShift_eq_zero` turns the vanishing of the
  localised degree-one class into the conclusion `extLoc_q (extToIdeles y) = 0`.

Nothing here is new mathematics: this is exactly the wiring of
`SSGStage/e1aLandingFinCompat.lean` (whose last line is the unproved
`PT.e1aBetaCan_localDictionary_fin_compat`) with the criterion in place of the dictionary.
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.style.haveILetI false

-- The finiteness of the canonical syzygy `ker (freeCover X)` from the finiteness of `X`
-- (the idiom of `SSGStage/e1aLandingFinCompat.lean`).
attribute [local instance] Work.SSGRoute.freeCoverSES_finite

noncomputable section

/-- **Finite-place landing clause from the local criterion.**  `SSGStage.e1aLandingFinCompat`
proved by way of `E1aClean.finLocalCriterion`. -/
theorem e1aLandingFinCompat_of_criterion
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1) :
    ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
      @Work.AbsoluteKummer.akRes (Ω ≃ₐ[k] Ω) _ _ (SSGRoute.decomp k A) E _
        (DistribMulAction.compHom E (SSGRoute.res k K))
        (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y) = 0 →
      SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofFinite q)
        (SSGRoute.PTExt.extToIdeles (k := k) y) = 0 := by
  intro y hy
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI hNfin : Finite (SSGRoute.SSGStage.e1aN0 p k Ω K T E).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  -- the degree-one class whose localisation is the conclusion
  set z : CategoryTheory.Abelian.Ext.{0}
      (CategoryTheory.Limits.kernel
        (Work.SSGRoute.freeCover (SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
      (SSGRoute.PTExt.unitsK k K) 1 :=
    (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
      (SSGRoute.SSGStage.e1aN0 p k Ω K T E)).symm y with hz
  -- the `E1c`-dictionary form of the hypothesis
  have h1 : Work.SSGRoute.PT.H2Fin.resH1 (SSGRoute.decomp k A)
      (Work.SSGRoute.homCoind k Ω K (CategoryTheory.Limits.kernel
        (Work.SSGRoute.freeCover (SSGRoute.SSGStage.e1aN0 p k Ω K T E))))
      (Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K)
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (SSGRoute.SSGStage.e1aN0 p k Ω K T E))) z) = 0 := by
    rw [hz]
    exact Work.SSGRoute.SSGStage.resH1_e1cEquiv_eq_zero_of_akRes_e1aChainC_eq_zero
      p k Ω K ζ hζ hζK T hT E (SSGRoute.decomp k A)
      (Work.SSGRoute.HS.isClosed_decomp A) y hy
  -- the local criterion
  have h2 := finLocalCriterion (k := k) (Ω := Ω) (K := K)
    (SSGRoute.SSGStage.e1aN0 p k Ω K T E) A hA q hAq z h1
  -- the degree reduction
  have h3 := Work.SSGRoute.SSGStage.extLoc_extToIdeles_e1aSyzShift_eq_zero (k := k) K
    (SSGRoute.SSGStage.e1aN0 p k Ω K T E) (NK.GlobalCFT.Place.ofFinite q) z h2
  rw [hz, AddEquiv.apply_symm_apply] at h3
  exact h3

end

end Work.SSGRoute.E1aClean
