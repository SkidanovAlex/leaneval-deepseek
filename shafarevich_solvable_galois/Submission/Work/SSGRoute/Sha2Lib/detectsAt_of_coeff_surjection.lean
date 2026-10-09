import Mathlib
import Submission.Work.SSGRoute.Sha2Lib.detectorInterface
import Submission.Work.SSGRoute.Sha2Lib.detector_of_submodule
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.SSGRoute.Sha2Lib

open CategoryTheory SSGRoute.PTExt

/-- **The detector is insensitive to a surjection of coefficients.**

If `c : M' ⟶ M` is a surjection of `Gal(K/k)`-modules (at this point only the underlying map is
used), if `φ' = c_* φ ∈ Ext¹_{D_w}(res M', ℤ)` is detected at a level `L ⊇ K` / place `q' | q` in
the sense of `DetectsAt`, then `φ` itself is detected at the *same* level and place: namely by the
pushforward `c_* h'` of the detecting class `h' ∈ H¹(Gal(L/k), res M')`.

Indeed, unramifiedness is preserved by pushforward along a coefficient map, and the level pairing
is natural in the coefficient module (`levelPair_pushforward_coeff`), so the nonvanishing of
`⟪φ', h'⟫` transfers to `⟪φ, c_* h'⟫ = ⟪c_* φ, h'⟫`.  -/
theorem detectsAt_of_coeff_surjection (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (M M' : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (c : M' ⟶ M) (hc : Function.Surjective c.hom)
    (φ : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M)
      (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) 1)
    (hdet : Work.SSGRoute.Sha2Lib.DetectsAt p k K Ω w q hwq M'
      ((CategoryTheory.Abelian.Ext.mk₀
        (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype c)).comp φ (zero_add 1))) :
    Work.SSGRoute.Sha2Lib.DetectsAt p k K Ω w q hwq M φ := by
  -- Unfold the detector for `M'`: a level `L`, a place `q' | q` and a class `h'` detecting `c_* φ`.
  obtain ⟨L, hLnf, hLfd, hLgal, q', hq', h', hU, hcop, hpair⟩ := hdet
  haveI : NumberField ↥L := hLnf
  haveI : FiniteDimensional k ↥L := hLfd
  haveI : IsGalois k ↥L := hLgal
  -- The same level and place detect `φ`, with the pushed-forward class `c_* h'`.
  refine ⟨L, hLnf, hLfd, hLgal, q', hq', ?_, ?_, hcop, ?_⟩
  · exact h'.comp (CategoryTheory.Abelian.Ext.mk₀
      (Rep.resMap (SSGRoute.PTExt.galRes k K L) c)) (add_zero 1)
  · -- Unramifiedness is preserved by the pushforward (`hU`).
    intro D hD
    rw [extHRestrict_pushforward D h' (Rep.resMap (SSGRoute.PTExt.galRes k K L) c)]
    rw [hU D hD]
    exact Abelian.Ext.zero_comp _ _ _ _ _
  · -- At the level `D_{q'}` the two pairings agree, by naturality in the coefficient module.
    have hkey := levelPair_pushforward_coeff (f := Work.SSGRoute.decompKRestrict k K ↥L w
        (NK.GlobalCFT.Place.ofFinite q') hq')
      (M := Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M')
      (M' := Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M)
      (π := Rep.resMap (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype c)
      (A := SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
      (B := SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite q')))
      (ι := SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L w
        (NK.GlobalCFT.Place.ofFinite q') hq') SSGRoute.PTExt.Coeff)
      (y := φ)
      (h := SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite q')) h') (r := 1) (s := 1)
    have hgoal : SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
        (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L w
          (NK.GlobalCFT.Place.ofFinite q') hq') SSGRoute.PTExt.Coeff)
        φ
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
          (NK.GlobalCFT.Place.ofFinite q'))
          (h'.comp (CategoryTheory.Abelian.Ext.mk₀
            (Rep.resMap (SSGRoute.PTExt.galRes k K L) c)) (add_zero 1)))
        = SSGRoute.PTExt.levelPair
          (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
          (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L w
            (NK.GlobalCFT.Place.ofFinite q') hq') SSGRoute.PTExt.Coeff)
          ((CategoryTheory.Abelian.Ext.mk₀
            (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype c)).comp φ
            (zero_add 1))
          (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
            (NK.GlobalCFT.Place.ofFinite q')) h') := by
      rw [extHRestrict_pushforward (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite q')) h' (Rep.resMap (SSGRoute.PTExt.galRes k K L) c)]
      exact hkey.symm
    rw [hgoal]
    exact hpair

end Work.SSGRoute.Sha2Lib
