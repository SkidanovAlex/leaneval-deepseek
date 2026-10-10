import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.isUnramifiedExt_of_levelPair_unramified
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The unramified clause of `local_phi_realization_in`, from the detector `C6` as a *hypothesis*

`Submission/Work/SSGRoute/isUnramifiedExt_of_levelPair_unramified.lean` proves the statement of
`Work.SSGRoute.isUnramifiedExt_of_levelPair_unramified_aux` (the third clause of
`local_phi_realization_in`) from the single input

  `Work.SSGRoute.E7cOmega.exists_level_unramified_detecting_class`   (node `C6`),

which is a `sorry` in a file of the E7cΩ lane.  The proof below is *the same proof*, with that one
call replaced by an explicit hypothesis `hdet` (whose type is verbatim the `Π`-type of the `C6`
statement) — i.e. with `C6` *abstracted*.  Consequently this declaration is **sorry‑free**, and it
can be instantiated at **any** provider of `C6`: the E7cΩ lane's
`E7cOmega.exists_level_unramified_detecting_class`, the `E7cC`/`SSGStage` versions, or the detector
dispatched from the `sha2_image_of_Hm2` lane.  In particular the E9 input of `sha2_image_of_Hm2`
becomes clean, without touching another lane's file, as soon as *any* of them lands.
-/

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt
open NK.GlobalCFT (Place)
open scoped NumberField

/-- **The unramified half of local Tate duality in class-formation form, from `C6` as a
hypothesis.**  Identical statement to `Work.SSGRoute.isUnramifiedExt_of_levelPair_unramified`
(= `Work.SSGRoute.isUnramifiedExt_of_levelPair_unramified_aux`), with the detector `C6` passed in
in the exact shape of `Work.SSGRoute.E7cOmega.exists_level_unramified_detecting_class`. -/
theorem isUnramifiedExt_of_levelPair_unramified_of_detector
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (hI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m)
    (hdet : ∀ (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M],
      (∀ m : M, p • m = 0) →
      (∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m) →
      ∀ φ : CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M)
          (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) 1,
        φ ≠ 0 →
        ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
          (_ : IsGalois k ↥L)
          (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
          (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
          (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K ↥L) M) 1),
          SSGRoute.PTExt.IsUnramifiedClassAt q' h ∧
          Nat.Coprime (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) p ∧
          SSGRoute.PTExt.levelPair
            (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
            (SSGRoute.PTExt.trivResInv
              (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
              SSGRoute.PTExt.Coeff)
            φ
            (SSGRoute.PTExt.extHRestrict
              (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
                (NK.GlobalCFT.Place.ofFinite q')) h) ≠ 0)
    (y : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M)
      (SSGRoute.PTExt.localUnitsK (k := k) w) 1)
    (hy : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
      (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
      (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K L) M) 1),
      SSGRoute.PTExt.IsUnramifiedClassAt q' h →
        SSGRoute.PTExt.levelPair
          (Work.SSGRoute.decompKRestrict k K L w (NK.GlobalCFT.Place.ofFinite q') hq')
          (Work.SSGRoute.localUnitsMap k K L w (NK.GlobalCFT.Place.ofFinite q') hq') y
          (SSGRoute.PTExt.extHRestrict
            (SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')) h) = 0) :
    SSGRoute.PTExt.IsUnramifiedExt w y := by
  classical
  subst hwq
  by_contra hy'
  set φ : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofFinite q)).subtype M)
      (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofFinite q))) 1 :=
    y.comp (CategoryTheory.Abelian.Ext.mk₀
      (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) q)) (add_zero 1) with hφdef
  have hφ : φ ≠ 0 := by
    intro h0
    exact hy' ((isUnramifiedExt_iff_valPush_eq_zero (k := k) (K := K) q y).mpr
      (hφdef ▸ h0))
  obtain ⟨L, hLnf, hLfd, hLgal, q', hq', h, hunr, hcop, hkey⟩ :=
    hdet M hM hI φ hφ
  let rh : SSGRoute.PTExt.extH (Rep.res (Work.SSGRoute.decompKRestrict k K ↥L
      (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofFinite q)).subtype M)) 1 :=
    SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
      (NK.GlobalCFT.Place.ofFinite q')) h
  have hzero : SSGRoute.PTExt.levelPair
      (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
        (NK.GlobalCFT.Place.ofFinite q') hq')
      (Work.SSGRoute.localUnitsMap k K ↥L (NK.GlobalCFT.Place.ofFinite q)
        (NK.GlobalCFT.Place.ofFinite q') hq') y rh = 0 :=
    hy L q' hq' h hunr
  have hkey' : SSGRoute.PTExt.levelPair
      (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
        (NK.GlobalCFT.Place.ofFinite q') hq')
      (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
        (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
        SSGRoute.PTExt.Coeff) φ rh ≠ 0 := hkey
  have hpush' : (SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
        (Work.SSGRoute.localUnitsMap k K ↥L (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite q') hq') y rh).comp
      (CategoryTheory.Abelian.Ext.mk₀
        (NK.HassePrinciple.localUnitsValHom (K := k) (L := ↥L) q')) (add_zero 2)
      = (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) •
        (SSGRoute.PTExt.levelPair
          (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
            (NK.GlobalCFT.Place.ofFinite q') hq')
          (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
            (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
            SSGRoute.PTExt.Coeff) φ rh) := by
    rw [levelPair_comp_valHom_general k K ↥L M q q' hq' y h, hφdef]
  have hVe : (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) •
      (SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
        (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
          (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
          SSGRoute.PTExt.Coeff) φ rh) = 0 := by
    rw [← hpush', hzero]
    exact CategoryTheory.Abelian.Ext.zero_comp _ _ _ _ _
  have hpφ : p • φ = 0 := by
    rw [hφdef, ← nsmul_comp_coeff p y
      (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) q))
      (add_zero 1)]
    rw [ext_nsmul_p_torsion_left
      (X := Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofFinite q)).subtype M)
      (Y := SSGRoute.PTExt.localUnitsK (k := k) (K := K) (NK.GlobalCFT.Place.ofFinite q))
      p (fun m => hM m) y, CategoryTheory.Abelian.Ext.zero_comp]
  have hVp : p •
      (SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
        (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
          (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
          SSGRoute.PTExt.Coeff) φ rh) = 0 := by
    rw [← levelPair_nsmul_x
      (f := Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
        (NK.GlobalCFT.Place.ofFinite q') hq')
      (M := Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofFinite q)).subtype M)
      (A := SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofFinite q)))
      (B := SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite q')))
      (ι := SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
        (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
        SSGRoute.PTExt.Coeff) (n := p) (x := φ) (h := rh)]
    rw [hpφ]
    exact levelPair_zero
      (f := Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
        (NK.GlobalCFT.Place.ofFinite q') hq')
      (M := Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofFinite q)).subtype M)
      (A := SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofFinite q)))
      (B := SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite q')))
      (ι := SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
        (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
        SSGRoute.PTExt.Coeff) rh
  have hdvd : addOrderOf (SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
        (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
          (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
          SSGRoute.PTExt.Coeff) φ rh) ∣ 1 := by
    have hg : addOrderOf (SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
        (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
          (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
          SSGRoute.PTExt.Coeff) φ rh) ∣
        Nat.gcd (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) p :=
      Nat.dvd_gcd (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hVe)
        (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hVp)
    rwa [show Nat.gcd (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) p = 1
      from hcop] at hg
  exact hkey' (AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd))

end Work.SSGRoute
