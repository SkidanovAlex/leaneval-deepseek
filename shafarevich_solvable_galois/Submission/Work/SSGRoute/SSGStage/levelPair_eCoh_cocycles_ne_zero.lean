import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Submission.Work.E7cOmega.subsingleton_ext_unitRep_ratRep
import Submission.Work.SSGRoute.E7cOmega.levelPair_ratDivSES_mk0_ne_zero_iff
import Submission.Work.SSGRoute.E7cOmega.unramifiedDetector_dwQuotient
import Submission.Work.SSGRoute.SSGStage.detectorFixedAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The detection half of the detector, at the `D_{q'}`-module (route (ii))

This is the repair of `SSGStage/levelPair_extHRestrict_coordKer_ne_zero.lean` recommended by its own
header: the detecting class is placed directly at the module
`Rep.res (decompKRestrict …) (Rep.res (decompK w).subtype M)`, i.e. at the level `↥(decompK q')`,
so that the criterion `levelPair_ratDivSES_mk0_ne_zero_iff` consumes it *literally* and the
non-definitional identification `Rep.res D.subtype (Rep.res (galRes k K L) M) ≃
Rep.res f (Rep.res (decompK w).subtype M)` (via `decompKRestrict_res_res`) is off the critical path.
A class at the level `Gal(L/k)` is converted into one here by the on-disk naturality

`extHRestrict D (eCoh 1 Γ A (H1π z)) = eCoh 1 D (res A) (H1π (mapCocycles₁ D.subtype z))`

(`E7cOmega/unramifiedDetector_dwQuotient.extHRestrict_eCoh_one`).

Proof: the criterion reduces the goal to `(eCoh 1 ↥D A (H1π z)).comp (mk₀ (resMap f μ)) ≠ 0`;
`eCoh_one_comp_mk0` (same file) rewrites the composite as `eCoh 1 ↥D (res divRep) (H1π z')` for the
coefficientwise image cocycle `z'`, whose coefficients are trivial (`isTrivial_res`), so
`eCoh_map_ne_zero` turns the single nonzero value `μ (z d)` given by `hval` into non-vanishing.
-/

namespace Work.SSGRoute.SSGStage

set_option maxHeartbeats 2000000

attribute [local instance 10000] Rep.hV2 Rep.hV1

theorem levelPair_eCoh_cocycles_ne_zero (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M.V, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (L : IntermediateField K Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (z : ↥(groupCohomology.cocycles₁
      (Rep.res (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M))))
    (hval : ∃ d : ↥(SSGRoute.PTExt.decompK (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite q')),
      μ.hom ((z : ↥(SSGRoute.PTExt.decompK (k := k) (K := ↥L)
          (NK.GlobalCFT.Place.ofFinite q')) → M.V) d) ≠ 0) :
    SSGRoute.PTExt.levelPair
      (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
      (SSGRoute.PTExt.trivResInv
        (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
        SSGRoute.PTExt.Coeff)
      ((CategoryTheory.Abelian.Ext.mk₀ μ).comp
        (CategoryTheory.ShortComplex.ShortExact.extClass
          (Work.SSGRoute.E7cOmega.ratDivSES_shortExact
            (G := SSGRoute.PTExt.decompK (k := k) (K := K) w))) (zero_add 1))
      (SSGRoute.PTExt.eCoh 1
        ↥(SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q'))
        (Rep.res (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M))
        ((groupCohomology.H1π (Rep.res
            (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
            (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M))).hom z)) ≠ 0 := by
  classical
  haveI : Fintype ↥(SSGRoute.PTExt.decompK (k := k) (K := ↥L)
      (NK.GlobalCFT.Place.ofFinite q')) := Fintype.ofFinite _
  refine (Work.SSGRoute.E7cOmega.levelPair_ratDivSES_mk0_ne_zero_iff
    (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq') μ
    (SSGRoute.PTExt.eCoh 1
      ↥(SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q'))
      (Rep.res (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M))
      ((groupCohomology.H1π (Rep.res
          (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M))).hom z))
    (Work.E7cOmega.subsingleton_ext_unitRep_ratRep
      ↥(SSGRoute.PTExt.decompK (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite q')))).mpr ?_
  haveI : (Rep.res (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
      (Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))).IsTrivial :=
    isTrivial_res _ _
  have hkey := Work.SSGRoute.E7cOmega.eCoh_one_comp_mk0
    ↥(SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q'))
    (Rep.res (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M))
    (Rep.res (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
      (Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)))
    (Rep.resMap (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq') μ)
    z (groupCohomology.mapCocycles₁ (MonoidHom.id _)
      (Rep.resMap (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq') μ) z)
    (fun g => rfl)
  rw [hkey, ← groupCohomology.H1π_comp_map_apply]
  exact Work.SSGRoute.SSGStage.eCoh_map_ne_zero (MonoidHom.id _)
    (Rep.res (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M))
    (Rep.res (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
      (Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)))
    (Rep.resMap (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq') μ)
    z hval

end Work.SSGRoute.SSGStage
