import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.e7comega_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.SSGRoute.Sha2Lib

open CategoryTheory SSGRoute.PTExt

/-! ## Local helper lemmas

Two naturality lemmas for the Yoneda/level pairing, proved here from the `Ext` API so that this file
stays independent of the heavier `Ext`-chapter modules.  They are the statements of
`Work.SSGRoute.extHRestrict_comp` and `Work.SSGRoute.levelPair_coeff_naturality` (both present in
this workspace, with these proofs), restated in the form used below. -/

/-- **Restriction commutes with pushing forward the coefficients.**  Restricting an `Ext`-class to
a subgroup `D` and then pushing it along a coefficient homomorphism `φ` is the same as first pushing
along `φ` and then restricting (along the restriction of `φ` to `D`). -/
theorem extHRestrict_pushforward {G : Type} [Group G] (D : Subgroup G) {A C : Rep.{0} Coeff G}
    {n : ℕ} (x : extH A n) (φ : A ⟶ C) :
    extHRestrict D (x.comp (Abelian.Ext.mk₀ φ) (add_zero n)) =
      (extHRestrict D x).comp (Abelian.Ext.mk₀ (Rep.resMap D.subtype φ)) (add_zero n) := by
  rw [extHRestrict, extHRestrict, extHMap, extHMap]
  simp only [Abelian.Ext.comp_mk₀_id]
  rw [extRes]
  rw [Abelian.Ext.mapExactFunctor_comp (Rep.resFunctor D.subtype)
      (X := unitRep G) (Y := A) (Z := C),
      Abelian.Ext.mapExactFunctor_mk₀ (Rep.resFunctor D.subtype)]
  rw [extRes]
  exact (Abelian.Ext.comp_assoc_of_third_deg_zero (Abelian.Ext.mk₀ (unitRes D.subtype))
    (x.mapExactFunctor (Rep.resFunctor D.subtype))
    (Abelian.Ext.mk₀ ((Rep.resFunctor D.subtype).map φ)) (zero_add n)).symm

/-- **Naturality of the level pairing in the coefficient module.**  The pullback `π^* y` of a class
`y ∈ Ext^r_G(M', A)` along `π : M ⟶ M'` pairs with `h ∈ H^s(H, res_f M)` exactly as `y` pairs with
the pushforward `π_* h`. -/
theorem levelPair_pushforward_coeff {H G : Type} [Group H] [Group G] (f : H →* G)
    {M M' : Rep.{0} Coeff G} (π : M ⟶ M') {A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H}
    (ι : Rep.res f A ⟶ B) {r s : ℕ} (y : Abelian.Ext.{0} M' A r)
    (h : extH (Rep.res f M) s) :
    levelPair f ι ((Abelian.Ext.mk₀ π).comp y (zero_add r)) h =
      levelPair f ι y (h.comp (Abelian.Ext.mk₀ (Rep.resMap f π)) (add_zero s)) := by
  simp only [levelPair, extRes, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.comp_assoc_of_third_deg_zero]

theorem detector_of_submodule (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (M N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] [Finite N]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (hM : ∀ m : M, p • m = 0) (hN : ∀ m : N, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (hI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m)
    (ι : N ⟶ M)
    (hdetN : ∀ φN : CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype N)
        (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) 1,
      φN ≠ 0 →
      ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
        (_ : IsGalois k ↥L)
        (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
        (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
        (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K L) N) 1),
        SSGRoute.PTExt.IsUnramifiedClassAt q' h ∧
        Nat.Coprime (q.asIdeal.ramificationIdx' q'.asIdeal) p ∧
        SSGRoute.PTExt.levelPair
          (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
          (SSGRoute.PTExt.trivResInv
            (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
            SSGRoute.PTExt.Coeff)
          φN
          (SSGRoute.PTExt.extHRestrict
            (SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')) h) ≠ 0)
    (φ : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M)
      (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) 1)
    (hφ : φ ≠ 0)
    (hφN : (CategoryTheory.Abelian.Ext.mk₀
        (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype ι)).comp φ
        (zero_add 1) ≠ 0) :
    ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
      (_ : IsGalois k ↥L)
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
      (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
      (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K L) M) 1),
      SSGRoute.PTExt.IsUnramifiedClassAt q' h ∧
      Nat.Coprime (q.asIdeal.ramificationIdx' q'.asIdeal) p ∧
      SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
        (SSGRoute.PTExt.trivResInv
          (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
          SSGRoute.PTExt.Coeff)
        φ
        (SSGRoute.PTExt.extHRestrict
          (SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')) h) ≠ 0 := by
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
