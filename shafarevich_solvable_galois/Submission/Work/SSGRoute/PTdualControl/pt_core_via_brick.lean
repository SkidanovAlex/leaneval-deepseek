import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.Sha2Lib.pt_core_via_c6
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Poitou--Tate core `E9` from the rank-one brick of `C6`

This file re-derives the chain `Work.SSGRoute.pt_sha2_core_clean`
(`pt_sha2_core_clean` <- `local_phi_realization_in_clean` <-
`isUnramifiedExt_of_levelPair_unramified` <- `E7cOmega.exists_level_unramified_detecting_class` <-
node `C6`) with the node `C6` replaced by the *proved* reduction
`Work.SSGRoute.PTdualControl.unramifiedDetector_of_rankOneBrick`, i.e. with the single remaining
arithmetic brick `RankOneBrick p k Ω` as an explicit hypothesis.  The point is that the `sorry`
of `Submission/Work/Sha2Lib/unramifiedDetector.lean` is then no longer in the proof term: the
target `Work.SSGRoute.PTdualControl.sha2_dual_control_alt` can be proved from the brick alone.
-/

namespace Work.SSGRoute.PTdualControl

open CategoryTheory SSGRoute.PTExt
open scoped NumberField

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

theorem exists_level_unramified_detecting_class_clean (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (hbrick : RankOneBrick p k Ω)
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (hI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m)
    (φ : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M)
      (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) 1)
    (hφ : φ ≠ 0) :
    ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
      (_ : IsGalois k ↥L)
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
      (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
      (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K ↥L) M) 1),
      SSGRoute.PTExt.IsUnramifiedClassAt q' h ∧
      Nat.Coprime (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) p ∧
      SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
        (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq') SSGRoute.PTExt.Coeff)
        φ
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')) h) ≠ 0 := by
  exact Work.SSGRoute.E7cOmega.exists_level_unramified_detecting_class_of_detectorInterface
    p k K Ω M hM w q hwq hpq hI
    (unramifiedDetector_of_rankOneBrick p k Ω hbrick K w q hwq hpq M hM hI) φ hφ


theorem isUnramifiedExt_of_levelPair_unramified_via_brick (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (hbrick : RankOneBrick p k Ω)
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (hI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m)
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
    exists_level_unramified_detecting_class_clean p k K Ω hbrick M hM
      (NK.GlobalCFT.Place.ofFinite q) q rfl hpq hI φ hφ
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

theorem local_phi_realization_in_clean_via_brick (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]
    (hbrick : RankOneBrick p k Ω)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (lam : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      extH (Rep.res (galRes k K L) M) 1 →+ extH (classesK k L) 2)
    (hp : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (h : extH (Rep.res (galRes k K L) M) 1), p • lam L h = 0)
    (hcompat : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L] (L' : IntermediateField K Ω) [NumberField L'] [FiniteDimensional k L'] [IsGalois k L'] (hLL : L ≤ L')
      (h : extH (Rep.res (galRes k K L) M) 1),
      inflCIn (k := k) hLL (lam L h) = lam L' (inflHIn (k := k) hLL h))
    (hloc : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      ∃ w' : NK.GlobalCFT.Place L, NK.GlobalCFT.Place.LiesOver w' w ∧
        ∀ h : extH (Rep.res (galRes k K L) M) 1,
          extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h = 0 → lam L h = 0) :
    ∃ z : Abelian.Ext M (idelesK k K) 1,
      (∀ u : NK.GlobalCFT.Place K, (∀ σ : K ≃ₐ[k] K, σ • w ≠ u) → extLoc u z = 0) ∧
      (∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (h : extH (Rep.res (galRes k K L) M) 1),
        phiAt (k := k) (K := K) (L := L) (extToClasses z) h = lam L h) ∧
      ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        w = NK.GlobalCFT.Place.ofFinite q →
        ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal) →
        (∀ σ : K ≃ₐ[k] K, IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m) →
        (∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
          (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
          (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
          (h : extH (Rep.res (galRes k K L) M) 1),
          IsUnramifiedClassAt q' h → lam L h = 0) →
        IsUnramifiedExt w (extLoc w z) := by
  classical
  obtain ⟨z, hz1, hz2⟩ :=
    local_phi_realization_in_aux (p := p) (k := k) (K := K) (Ω := Ω) ζ hζ M hM w lam hp
      hcompat hloc
  refine ⟨z, hz1, hz2, ?_⟩
  intro q hwq hpq hI hkill
  refine isUnramifiedExt_of_levelPair_unramified_via_brick (p := p) (k := k) (K := K) (Ω := Ω)
    (hbrick := hbrick) M hM
    w q hwq hpq hI (extLoc (k := k) (K := K) w z) ?_
  intro L hnf hfd hgal q' hq' h hunr
  have hphi : phiAt (k := k) (K := K) (L := L) (extToClasses z) h = 0 := by
    rw [hz2 L h]
    exact hkill L q' hq' h hunr
  rw [levelPair_extLoc_eq_push (k := k) (K := K) (L := ↥L) (M := M) z h w
    (NK.GlobalCFT.Place.ofFinite q') hq']
  refine extLoc_eq_zero_of_locTrivial_off_orbit k ↥L (NK.GlobalCFT.Place.ofFinite q') _ ?_ ?_
  · intro v hv
    rw [extLoc_levelPair_idleRepMap_eq (k := k) (K := K) (L := ↥L) M z h v]
    obtain ⟨u, hu⟩ := exists_place_under (L := K) (L' := ↥L) v
    have hzu : extLoc (k := k) (K := K) u z = 0 := by
      refine hz1 u (fun σ hσ => ?_)
      have hlies : NK.GlobalCFT.Place.LiesOver v (σ • w) := by rw [hσ]; exact hu
      obtain ⟨τ, hτ⟩ := SSG.exists_smul_eq_of_liesOver_under (k := k) (K := K) (Ω := Ω) L w
        (NK.GlobalCFT.Place.ofFinite q') hq' v (σ • w) hlies σ rfl
      exact hv τ hτ
    have hpush : extLoc (k := k) (K := ↥L) v
        ((extRes (galRes k K ↥L) z).comp (Abelian.Ext.mk₀ (idleRepMap k K ↥L))
          (add_zero 1)) = 0 :=
      e9c_transport_zero z u v hu hzu
    rw [hpush]
    exact yonedaPair_zero_right _
  · have hkey := phiAt_extToClasses_eq_idleRepMap (k := k) (K := K) (L := ↥L) M z h
    rw [hkey] at hphi
    simpa only [extToClasses] using hphi

theorem pt_sha2_core_clean_via_brick (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    (hbrick : RankOneBrick p k (AlgebraicClosure K))
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (x : Abelian.Ext M (classesK k K) 1)
    (hx : ∀ h : extH M 1, IsLocTrivial h → pairK x h = 0) :
    ∃ z : Abelian.Ext M (idelesK k K) 1, extToClasses z = x := by
  classical
  obtain ⟨S₀, hS₀arch, hS₀bad, hS₀van⟩ :=
    e9_vanish_off_finite p k K (AlgebraicClosure K) ζ hζ M hM x hx
  -- enlarge `S₀` to a `Gal(K/k)`-stable finite set; all the properties of E9a's output are
  -- monotone in the place set, so they transfer to the closure
  obtain ⟨S, hS₀S, hSstab⟩ := exists_galois_stable_superset k K S₀
  have hSarch : ∀ v : NK.GlobalCFT.Place K,
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        v ≠ NK.GlobalCFT.Place.ofFinite q) → v ∈ S :=
    fun v hv => hS₀S (hS₀arch v hv)
  have hSbad : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      NK.GlobalCFT.Place.ofFinite q ∉ S →
        (p : NumberField.RingOfIntegers K) ∉ q.asIdeal ∧
        ∀ σ : K ≃ₐ[k] K, IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m :=
    fun q hq => hS₀bad q (fun hmem => hq (hS₀S hmem))
  have hSvan : ∀ (L : IntermediateField K (AlgebraicClosure K)) [NumberField L]
      [FiniteDimensional k L] [IsGalois k L]
      (h : extH (Rep.res (galRes k K L) M) 1),
      (∀ w' : NK.GlobalCFT.Place L, (∃ v ∈ S, NK.GlobalCFT.Place.LiesOver w' v) →
        extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h = 0) →
      (∀ q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
        IsUnramifiedClassAt q' h) →
      phiAt (k := k) (K := K) (L := L) x h = 0 :=
    fun L _ _ _ h h1 h2 => hS₀van L h (fun w' hw' => h1 w' (by
      obtain ⟨v, hv, hl⟩ := hw'
      exact ⟨v, hS₀S hv, hl⟩)) h2
  obtain ⟨R, hR⟩ := pts2_exists_orbit_transversal k K
  obtain ⟨lam, hlam_p, hlam_compat, hlam_loc, hlam_unr, hlam_sum⟩ :=
    e9_local_decomposition (p := p) (k := k) (K := K) (Ω := AlgebraicClosure K) (ζ := ζ)
      (hζ := hζ) (M := M) (hM := hM) (R := R) (hR := hR) (x := x) (S := S)
      (hSarch := hSarch) (hSbad := hSbad) (hSstab := hSstab) (hS := hSvan)
  -- E7cΩ: each local family is realised by an idèle class supported on the orbit of `v`
  have hzv : ∀ v : R, ∃ z : Abelian.Ext M (idelesK k K) 1,
      (∀ u : NK.GlobalCFT.Place K, (∀ σ : K ≃ₐ[k] K, σ • v.1 ≠ u) → extLoc u z = 0) ∧
      (∀ (L : IntermediateField K (AlgebraicClosure K)) [NumberField L]
        [FiniteDimensional k L] [IsGalois k L]
        (h : extH (Rep.res (galRes k K L) M) 1),
        phiAt (k := k) (K := K) (L := L) (extToClasses z) h = lam v L h) ∧
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        v.1 = NK.GlobalCFT.Place.ofFinite q →
        ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal) →
        (∀ σ : K ≃ₐ[k] K, IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m) →
        (∀ (L : IntermediateField K (AlgebraicClosure K)) [NumberField L]
          [FiniteDimensional k L] [IsGalois k L]
          (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
          (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') v.1)
          (h : extH (Rep.res (galRes k K L) M) 1),
          IsUnramifiedClassAt q' h → lam v L h = 0) →
        IsUnramifiedExt v.1 (extLoc v.1 z)) := by
    intro v
    exact local_phi_realization_in_clean_via_brick p k K (AlgebraicClosure K) hbrick ζ hζ M hM v.1
      (fun L => lam v L) (hlam_p v) (hlam_compat v) (hlam_loc v)
  choose zv hsupp hpair hunr0 using hzv
  -- E2: glue the local components into a global idèle class
  obtain ⟨glue, hglue_comp, hglue_recon⟩ := PT.exists_glue_extLoc k K M 1 R hR
  have hfinS : {w : R | w.1 ∈ (S : Set (NK.GlobalCFT.Place K))}.Finite :=
    S.finite_toSet.preimage (f := fun w : R => w.1) (fun a _ b _ h => Subtype.ext h)
  -- E7cΩ's unramified clause: `zv v` is unramified at `v` for `v ∉ S`
  have hunr : ∀ v : R, v.1 ∉ S → IsUnramifiedExt v.1 (extLoc v.1 (zv v)) := by
    intro v hv
    have hlr := hlam_unr v
    have hc := hunr0 v
    have hex : ∃ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        v.1 = NK.GlobalCFT.Place.ofFinite q := by
      by_contra h
      exact hv (hSarch v.1 (fun q hq => h ⟨q, hq⟩))
    obtain ⟨q₀, hq₀⟩ := hex
    rw [hq₀] at hv hlr hc ⊢
    exact hc q₀ rfl (hSbad q₀ hv).1 (hSbad q₀ hv).2
      (fun L _ _ _ q' hq' h hunr' => hlr hv L q' hq' h hunr')
  have hfin : {w : R | ¬ IsUnramifiedExt (k := k) w.1
      (extLoc (k := k) w.1 (zv w))}.Finite :=
    hfinS.subset (fun w hw => by
      by_contra hwS
      exact hw (hunr w hwS))
  let z : Abelian.Ext M (idelesK k K) 1 := glue (fun w => extLoc w.1 (zv w))
  have hz : ∀ v : R, extLoc v.1 z = extLoc v.1 (zv v) :=
    fun v => hglue_comp (fun w => extLoc w.1 (zv w)) hfin v
  -- the corrected class has vanishing level values, so E6Ω forces it to vanish
  have hvanish : PhiOneVanishesIn (AlgebraicClosure K) (x - extToClasses z) := by
    intro L _ _ _ h
    have hxsum := (hlam_sum L h).2
    have hzsum := (e9_glue_phiAt p k K (AlgebraicClosure K) M hM R hR S hSarch
      (fun q hq => (hSbad q hq).2) zv hsupp hunr z hz L h).2
    rw [phiAt_sub_aux, hxsum, hzsum, sub_eq_zero]
    exact finsum_congr (fun v => (hpair v L h).symm)
  have h0 : x - extToClasses z = 0 :=
    phi1_mono_sylow_in p k K (AlgebraicClosure K) ζ hζ M hM (x - extToClasses z) hvanish
  exact ⟨z, (sub_eq_zero.mp h0).symm⟩

end Work.SSGRoute.PTdualControl
