import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.levelPair_unramified_eq_zero
import Submission.Work.SSGRoute.PT.vfShared
import Submission.Work.SSGRoute.local_phi_realization_in
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The off-`S'` local vanishing of clause (7)

At a finite place `q'` of a level `L ⊇ K` whose inertia subgroup is trivial, the local component
`extLoc q' (levelPair (galRes) (idleRepMap) X h)` of the *global* level pairing vanishes whenever the
localisation `extLoc u X` of the global class `X` at the place `u` of `K` below `q'` is unramified.
This is clause (6) of `G1⁺` in the global spelling (the off-`S'` terms of the reciprocity sum are
killed by it).

The proof is two steps and uses only proved material:
* `Work.SSGRoute.levelPair_extLoc_eq_push` (`local_phi_realization_in.lean`) computes the
  localisation of the level pairing as the level pairing of the localisations, with the transparent
  place glue `decompKRestrict` and the canonical local-units map `localUnitsMap`;
* `Work.SSGRoute.PT.levelPair_unramified_eq_zero` (`levelPair_unramified_eq_zero.lean`) kills the
  pairing of an unramified local class at a place with trivial inertia.

This brick was previously only available inside `PT/G1plusOwn/reciprocityFiniteClause.lean`
(`rfcExtLocH_eq_zero_of_good`), which does not compile (`Unknown identifier hKL` plus `whnf`
heartbeat timeouts); the version here is stated for an *abstract* global class `X`, so it is free of
the `finZB`/`finZF` vocabulary whose unfolding is expensive.
-/

namespace Work.SSGRoute.PT.G1plusOwn

open scoped TensorProduct
open SSGRoute.PTExt CategoryTheory

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

/-- **The local component of the global level pairing vanishes at an unramified place.**  For a
finite place `q'` of `L` over `u` whose inertia in `Gal(L/k)` is trivial (`hunr`) and at which the
local class `extLoc u X` is unramified, the `q'`-component of the level pairing of `X` with the
level class `h` vanishes. -/
theorem extLoc_levelPair_galRes_eq_zero_of_unramified
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hψ : ∀ g h : ↥L ≃ₐ[k] ↥L,
      b₀ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • b₀ h + b₀ g)
    (X : CategoryTheory.Abelian.Ext
      (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))
      (SSGRoute.PTExt.idelesK k ↥K) 1)
    (u : NK.GlobalCFT.Place ↥K)
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hw : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') u)
    (hunr : ∀ σ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt q' σ → σ = 1)
    (hy : SSGRoute.PTExt.IsUnramifiedExt u
      (SSGRoute.PTExt.extLoc (k := k) (K := ↥K) u X)) :
    SSGRoute.PTExt.extLoc (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')
        (SSGRoute.PTExt.levelPair (SSGRoute.PTExt.galRes k (↥K) (↥L))
          (Work.SSGRoute.idleRepMap k (↥K) (↥L)) X
          (Work.SSGRoute.PT.levelClassOf (p := p) (k := k) (Ω := Ω) (K := K) (L := L)
            (T := T) (M := M) b₀ hψ)) = 0 := by
  rw [← Work.SSGRoute.levelPair_extLoc_eq_push (k := k) (K := ↥K) (L := ↥L) X
    (Work.SSGRoute.PT.levelClassOf (p := p) (k := k) (Ω := Ω) (K := K) (L := L)
      (T := T) (M := M) b₀ hψ) u (NK.GlobalCFT.Place.ofFinite q') hw]
  exact Work.SSGRoute.PT.levelPair_unramified_eq_zero k ↥K
    (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))
    u ↥L q' hw hunr
    (Work.SSGRoute.decompKRestrict k (↥K) (↥L) u (NK.GlobalCFT.Place.ofFinite q') hw)
    (Work.SSGRoute.decompKRestrict_coe k (↥K) (↥L) u (NK.GlobalCFT.Place.ofFinite q') hw)
    (Work.SSGRoute.localUnitsMap k (↥K) (↥L) u (NK.GlobalCFT.Place.ofFinite q') hw)
    (Work.SSGRoute.localUnitsMap_spec k (↥K) (↥L) u (NK.GlobalCFT.Place.ofFinite q') hw)
    (SSGRoute.PTExt.extLoc (k := k) (K := ↥K) u X) hy
    (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite q'))
      (Work.SSGRoute.PT.levelClassOf (p := p) (k := k) (Ω := Ω) (K := K) (L := L)
        (T := T) (M := M) b₀ hψ))

end

end Work.SSGRoute.PT.G1plusOwn
