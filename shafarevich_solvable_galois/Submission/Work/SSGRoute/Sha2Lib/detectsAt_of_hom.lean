import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.Sha2Lib.detectorInterface
import Submission.Work.SSGRoute.Sha2Lib.detector_of_submodule
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

open CategoryTheory

/-!
# Detecting a class after pushing the coefficients forward along a homomorphism

`detectsAt_of_hom` is the hypothesis-free form of `Work.SSGRoute.Sha2Lib.detector_of_submodule`:
if the coefficient class `φ` pushed forward along `ι : N ⟶ M` at the decomposition group `D_w` is
nonzero, and `N` is an unramified detector, then `φ` itself is detected at `M` (at the *same*
level and place produced by the detector for `N`).

The point is naturality of the level pairing in the coefficient module
(`levelPair_pushforward_coeff`): pushing `h` forwards along `res(ι)` at the level, or pushing `φ`
forwards along `res_{D_w}(ι)`, gives the same value of the pairing.  No finiteness or triviality
hypothesis on `M`, `N` is needed -- this is why the argument is stated separately from
`detector_of_submodule`, whose proof body in fact only uses `hdetN`, `ι` and `hφN`.
-/

theorem detectsAt_of_hom (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (N M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (hdetN : Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq N)
    (ι : N ⟶ M)
    (φ : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M)
      (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) 1)
    (hφN : (CategoryTheory.Abelian.Ext.mk₀
        (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype ι)).comp φ
        (zero_add 1) ≠ 0) :
    Work.SSGRoute.Sha2Lib.DetectsAt p k K Ω w q hwq M φ := by
  unfold IsUnramifiedDetector at hdetN
  unfold DetectsAt
  unfold DetectsAt at hdetN
  -- The detector for `N`, applied to the class `φN` obtained by pushing `φ` forward along `ι`
  -- (at the decomposition group `D_w`), returns a level `L`, a place `q'` over `w` and a class
  -- `hN' ∈ H¹(Gal(L/k), res N)` detecting `φN` there.
  obtain ⟨L, hLnf, hLfd, hLgal, q', hq', hN', hU, hcop, hpairN⟩ :=
    hdetN ((CategoryTheory.Abelian.Ext.mk₀
        (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype ι)).comp φ
        (zero_add 1)) hφN
  haveI : NumberField ↥L := hLnf
  haveI : FiniteDimensional k ↥L := hLfd
  haveI : IsGalois k ↥L := hLgal
  -- The same level/place detects `φ`: push `hN'` forward along `ι`.
  refine ⟨L, hLnf, hLfd, hLgal, q', hq', ?_, ?_, hcop, ?_⟩
  · exact hN'.comp (CategoryTheory.Abelian.Ext.mk₀
      (Rep.resMap (SSGRoute.PTExt.galRes k K L) ι)) (add_zero 1)
  · -- Unramifiedness is preserved by the pushforward (`hU`).
    intro D hD
    rw [extHRestrict_pushforward D hN' (Rep.resMap (SSGRoute.PTExt.galRes k K L) ι)]
    rw [hU D hD]
    exact Abelian.Ext.zero_comp _ _ _ _ _
  · -- At the level `D_{q'}` the two pairings agree, by naturality in the coefficient module.
    have hkey := levelPair_pushforward_coeff (f := Work.SSGRoute.decompKRestrict k K ↥L w
        (NK.GlobalCFT.Place.ofFinite q') hq')
      (M := Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype N)
      (M' := Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M)
      (π := Rep.resMap (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype ι)
      (A := SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
      (B := SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite q')))
      (ι := SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L w
        (NK.GlobalCFT.Place.ofFinite q') hq') SSGRoute.PTExt.Coeff)
      (y := φ)
      (h := SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite q')) hN') (r := 1) (s := 1)
    have hgoal : SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
        (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L w
          (NK.GlobalCFT.Place.ofFinite q') hq') SSGRoute.PTExt.Coeff)
        φ
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
          (NK.GlobalCFT.Place.ofFinite q'))
          (hN'.comp (CategoryTheory.Abelian.Ext.mk₀
            (Rep.resMap (SSGRoute.PTExt.galRes k K L) ι)) (add_zero 1)))
        = SSGRoute.PTExt.levelPair
          (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
          (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L w
            (NK.GlobalCFT.Place.ofFinite q') hq') SSGRoute.PTExt.Coeff)
          ((CategoryTheory.Abelian.Ext.mk₀
            (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype ι)).comp φ
            (zero_add 1))
          (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
            (NK.GlobalCFT.Place.ofFinite q')) hN') := by
      rw [extHRestrict_pushforward (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite q')) hN' (Rep.resMap (SSGRoute.PTExt.galRes k K L) ι)]
      exact hkey.symm
    rw [hgoal]
    exact hpairN

end Work.SSGRoute.Sha2Lib
