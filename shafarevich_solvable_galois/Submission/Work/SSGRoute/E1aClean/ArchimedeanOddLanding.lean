import Mathlib
import Submission.Work.SSGRoute.E1aClean.ArchimedeanOdd
import Submission.Work.SSGRoute.PT.e1a_beta_can
import Submission.Work.SSGRoute.PT.e1a_assembly
import Submission.Work.SSGRoute.glue_infinite_place
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The archimedean place of the E1a landing clause at odd coefficients

For an odd prime `p` the archimedean component of the landing clause holds *unconditionally*: the
local group `Ext²_{D_w}(E^∨(1)|, K_wˣ)` is a subsingleton
(`Work.SSGRoute.E1aClean.archimedeanExt2Subsingleton`), so `extLoc_w (extToIdeles y) = 0` for every
class `y`.  This file records that reduction, so that the archimedean crux of the E1a node is the
`p = 2` case alone.
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

/-- The coefficient `E^∨(1) = DualMod p (E ⊗ T)` of the E1a chain is `p`-torsion. -/
theorem psmul_e1aCoeff_eq_zero (p : ℕ) (E T : Type) [AddCommGroup E] [Module (ZMod p) E]
    [AddCommGroup T] [Module (ZMod p) T]
    (x : (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) : p • x = 0 := by
  apply LinearMap.ext
  intro m
  show p • (x m) = 0
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- **The archimedean landing clause at an odd prime.**  If `p ≠ 2`, the archimedean component of
the landing clause holds without any hypothesis on the continuous restriction of the chain class. -/
theorem archimedeanLanding_odd (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (w : NumberField.InfinitePlace ↥K) :
    ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
      SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofInfinite w)
        (SSGRoute.PTExt.extToIdeles (k := k) y) = 0 := by
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI hNfin : Finite (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  haveI hsub : Subsingleton (CategoryTheory.Abelian.Ext.{0}
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w)).subtype
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
      (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofInfinite w)) 2) :=
    archimedeanExt2Subsingleton p hp2 k ↥K
      (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
      (fun x => psmul_e1aCoeff_eq_zero p E T x) w
  intro y
  exact Subsingleton.elim _ _

end Work.SSGRoute.E1aClean
