import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.NK.NUV2.ARL.HR.locUnits_inflation_eq_zero_iff
import Submission.Work.SSGRoute.eb_crux_index_eq_ef
import Submission.Work.SSGRoute.eb_crux_ncard_eq_ef
import Submission.Work.SSGRoute.eb_locUnits_resToGal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.SSGRoute

open CategoryTheory NumberField

/-- **The order of a finite group annihilates `H²` of any `Rep.ofDistribMulAction`.**

For a finite group `G`, a commutative ring `R` and an `R[G]`-module `V` (given as a
`DistribMulAction` compatible with the `R`-action), every element of `H²(G, V)` is annihilated by
`Nat.card G`.  This is the `R`-linear form of
`Commons.RepresentationTheory.GroupCohomology.natCard_nsmul_H2_eq_zero` (proved for `R = ℤ`),
obtained by transporting along the coefficient-ring transfer
`NK.NUV2.LC.nonempty_addEquiv_groupCohomology_two_coeffTransfer`. -/
theorem natCard_nsmul_H2_eq_zero_of_distribMulAction
    {R G V : Type} [CommRing R] [Group G] [Fintype G] [AddCommGroup V] [Module R V]
    [DistribMulAction G V] [SMulCommClass G R V]
    (x : groupCohomology (Rep.ofDistribMulAction R G V) 2) : Nat.card G • x = 0 := by
  obtain ⟨e⟩ := NK.NUV2.LC.nonempty_addEquiv_groupCohomology_two_coeffTransfer
    (k := R) (k' := ℤ) (G := G) (V := V)
  have h : e (Nat.card G • x) = 0 := by
    rw [map_nsmul]
    exact Commons.RepresentationTheory.GroupCohomology.natCard_nsmul_H2_eq_zero
      (Rep.ofDistribMulAction ℤ G V) (e x)
  exact e.injective (by rw [h, map_zero])


/-- Specialisation of `natCard_nsmul_H2_eq_zero_of_distribMulAction` to the Hasse--Brauer--Noether
local units representation. -/
theorem natCard_nsmul_localUnitsRep_eq_zero {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (w : NK.GlobalCFT.Place L)
    (x : groupCohomology (NK.HassePrinciple.localUnitsRep K L w) 2) :
    Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w) • x = 0 := by
  haveI : Fintype (MulAction.stabilizer (L ≃ₐ[K] L) w) := Fintype.ofFinite _
  exact natCard_nsmul_H2_eq_zero_of_distribMulAction x

/-- **The local-degree core of `eb_crux` (abstract form).**

Let `G' →* G` be an injective group homomorphism, `A` a representation of `G` over a commutative
ring, and suppose

* `H²(G, A)` is cyclic of order `Nat.card G` (`hcardG`, `hgenG`);
* `H²(G', A)` is cyclic of order `Nat.card G'` (`hcardS`, `hgenS`).

Then any `x ∈ H²(G, A)` annihilated by the index `φ.range.index` of `G'` in `G` satisfies
`res(x) = 0`.

Proof.  Write `H²(G, A) = ℤ/m` with `m = Nat.card G`, so `x = k • u`.  The index `n₁` of `φ` is
`m / Nat.card G'`, and `n₁ • x = 0` gives `(m/n₁) | k`, i.e. `Nat.card G' | k`.  On the other
hand `res u` lies in the cyclic group `H²(G', A) = ℤ/Nat.card G'`, so `addOrderOf (res u)` divides
`Nat.card G'`, hence divides `k`; therefore `res x = k • res u = 0`. -/
theorem res_eq_zero_of_card_dvd
    {k : Type} [CommRing k] {G G' : Type} [Group G] [Group G'] [Fintype G] [Fintype G']
    (φ : G' →* G) (hφ : Function.Injective φ) {A : Rep k G}
    (hcardG : Nat.card (groupCohomology A 2) = Nat.card G)
    (hgenG : ∃ u : groupCohomology A 2, addOrderOf u = Nat.card (groupCohomology A 2))
    (hcardS : Nat.card (groupCohomology (Rep.res φ A) 2) = Nat.card G')
    (hgenS : ∃ v : groupCohomology (Rep.res φ A) 2,
      addOrderOf v = Nat.card (groupCohomology (Rep.res φ A) 2))
    (x : groupCohomology A 2) (hx : φ.range.index • x = 0) :
    (ConcreteCategory.hom ((groupCohomology.resNatTrans k (G := G') (H := G) φ 2).app A)) x = 0 := by
  classical
  obtain ⟨u, hu⟩ := hgenG
  obtain ⟨v, hv⟩ := hgenS
  have hGne : Nat.card G ≠ 0 := by rw [Nat.card_eq_fintype_card]; exact Fintype.card_ne_zero
  have hG'ne : Nat.card G' ≠ 0 := by rw [Nat.card_eq_fintype_card]; exact Fintype.card_ne_zero
  haveI hfinA : Finite (groupCohomology A 2) :=
    (Nat.card_ne_zero.mp (by rw [hcardG]; exact hGne)).2
  haveI hfinB : Finite (groupCohomology (Rep.res φ A) 2) :=
    (Nat.card_ne_zero.mp (by rw [hcardS]; exact hG'ne)).2
  have hrange : Nat.card ↥φ.range = Nat.card G' := by
    have hset : (φ.range : Set G) = Set.range φ := by ext y; simp
    change Nat.card ↥(φ.range : Set G) = Nat.card G'
    rw [Nat.card_congr (Set.equivOfEq hset), Nat.card_congr (Equiv.ofInjective φ hφ)]
  have htop : AddSubgroup.zmultiples u = ⊤ := by
    apply AddSubgroup.eq_of_le_of_card_ge le_top
    have h1 : Nat.card ↥(AddSubgroup.zmultiples u) = Nat.card (groupCohomology A 2) := by
      rw [Nat.card_zmultiples, hu]
    have h2 : Nat.card ↥(⊤ : AddSubgroup (groupCohomology A 2)) = Nat.card (groupCohomology A 2) := by simp
    rw [h1, h2]
  have hxmem : x ∈ AddSubgroup.zmultiples u := htop ▸ AddSubgroup.mem_top x
  obtain ⟨kk, hkk⟩ := AddSubgroup.mem_zmultiples_iff.mp hxmem
  set r := (ConcreteCategory.hom ((groupCohomology.resNatTrans k (G := G') (H := G) φ 2).app A))
    with hr
  have hq : addOrderOf (r u) ∣ Nat.card G' := by
    have hvtop : AddSubgroup.zmultiples v = ⊤ := by
      apply AddSubgroup.eq_of_le_of_card_ge le_top
      have h1 : Nat.card ↥(AddSubgroup.zmultiples v) = Nat.card (groupCohomology (Rep.res φ A) 2) := by
        rw [Nat.card_zmultiples, hv]
      have h2 : Nat.card ↥(⊤ : AddSubgroup (groupCohomology (Rep.res φ A) 2))
          = Nat.card (groupCohomology (Rep.res φ A) 2) := by simp
      rw [h1, h2]
    have hmem : r u ∈ AddSubgroup.zmultiples v := hvtop ▸ AddSubgroup.mem_top _
    have h2 := addOrderOf_dvd_of_mem_zmultiples hmem
    have h3 : addOrderOf v = Nat.card G' := hv.trans hcardS
    exact h3 ▸ h2
  have hidx : Nat.card G = Nat.card G' * φ.range.index := by
    rw [← hrange]; exact (Subgroup.card_mul_index φ.range).symm
  have hn1 : (φ.range.index : ℤ) ≠ 0 := by
    have h : φ.range.index ≠ 0 := by
      intro hh; rw [hh, mul_zero] at hidx; exact hGne hidx
    exact_mod_cast h
  have hkey : ((addOrderOf u : ℕ) : ℤ) ∣ ((φ.range.index : ℤ) * kk) := by
    rw [addOrderOf_dvd_iff_zsmul_eq_zero]
    rw [mul_zsmul, hkk, natCast_zsmul, hx]
  have hkey' : ((Nat.card G : ℤ)) ∣ ((φ.range.index : ℤ) * kk) := by
    rwa [hu, hcardG] at hkey
  have hG'dvd : (Nat.card G' : ℤ) ∣ kk := by
    have h1 : ((Nat.card G : ℤ)) = (φ.range.index : ℤ) * (Nat.card G' : ℤ) := by
      rw [hidx]; push_cast; ring
    rw [h1] at hkey'
    exact (Int.mul_dvd_mul_iff_left hn1).mp hkey'
  have hqdvd : (addOrderOf (r u) : ℤ) ∣ kk :=
    dvd_trans (Int.natCast_dvd_natCast.mpr hq) hG'dvd
  have hres : r x = 0 := by
    have h1 : r x = kk • r u := by
      have h2 := map_zsmul r kk u
      rw [hkk] at h2
      exact h2
    rw [h1, ← addOrderOf_dvd_iff_zsmul_eq_zero]
    exact hqdvd
  exact hres

/-- The inclusion `Stab_{Gal(E/M)}(ŵ) →* Stab_{Gal(E/k)}(ŵ)` of stabilisers is injective. -/
theorem stabIncl_injective {k M E : Type} [Field k] [NumberField k] [Field M] [NumberField M]
    [Field E] [NumberField E] [Algebra k M] [Algebra k E] [Algebra M E] [IsScalarTower k M E]
    (ŵ : NK.GlobalCFT.Place E) :
    Function.Injective (stabIncl (k := k) (M := M) ŵ) := by
  intro σ τ h
  refine Subtype.ext (AlgEquiv.ext fun x => ?_)
  have := congrArg (fun (f : MulAction.stabilizer (E ≃ₐ[k] E) ŵ) => f.1 x) h
  simpa [stabIncl] using this




/-- **The local degree step of `brauer_single_place` (E8', step P2).** -/
theorem eb_crux (k L M E : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Field M] [NumberField M] [Field E] [NumberField E] [Algebra k L] [Algebra k M] [Algebra k E] [Algebra L E] [Algebra M E] [IsScalarTower k L E] [IsScalarTower k M E] [FiniteDimensional k L] [FiniteDimensional k M] [FiniteDimensional k E] [IsGalois k L] [IsGalois k M] [IsGalois k E] [FiniteDimensional M E] [IsGalois M E] (hgen : Algebra.adjoin k (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤) (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) (N : ℕ) : Work.SSGRoute.EB_Crux k L M E hgen v₀ N := by
  intro hM hL ŵ hŵ a
  -- places of `L` and `M` below `ŵ`
  let r : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) :=
    ⟨ŵ.asIdeal.under (NumberField.RingOfIntegers L), inferInstance,
      Ideal.under_ne_bot (NumberField.RingOfIntegers L) ŵ.ne_bot⟩
  let W : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M) :=
    ⟨ŵ.asIdeal.under (NumberField.RingOfIntegers M), inferInstance,
      Ideal.under_ne_bot (NumberField.RingOfIntegers M) ŵ.ne_bot⟩
  have hŵr : ŵ.asIdeal.LiesOver r.asIdeal := by
    change ŵ.asIdeal.LiesOver (ŵ.asIdeal.under (NumberField.RingOfIntegers L))
    exact Ideal.over_under ŵ.asIdeal
  have hŵW : ŵ.asIdeal.LiesOver W.asIdeal := by
    change ŵ.asIdeal.LiesOver (ŵ.asIdeal.under (NumberField.RingOfIntegers M))
    exact Ideal.over_under ŵ.asIdeal
  have hrL : r.asIdeal.LiesOver v₀.asIdeal :=
    Ideal.LiesOver.tower_bot ŵ.asIdeal r.asIdeal v₀.asIdeal
  have hWL : W.asIdeal.LiesOver v₀.asIdeal :=
    Ideal.LiesOver.tower_bot ŵ.asIdeal W.asIdeal v₀.asIdeal
  have hwr : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite ŵ)
      (NK.GlobalCFT.Place.ofFinite r) := NK.GlobalCFT.Place.liesOver_ofFinite hŵr
  haveI : IsGalois L E := IsGalois.tower_top_of_isGalois k L E
  -- Step 1: rewrite the target as a restriction
  rw [Work.SSGRoute.eb_locUnits_resToGal (k := k) (M := M) (E := E)
    (NK.GlobalCFT.Place.ofFinite ŵ)
    ((NK.NUV2.ARL.HR.inflation (K := k) (L := L) (E := E)).hom a)]
  set Aval : groupCohomology (NK.HassePrinciple.localUnitsRep k E
      (NK.GlobalCFT.Place.ofFinite ŵ)) 2 :=
    (NK.HassePrinciple.locUnits k E (NK.GlobalCFT.Place.ofFinite ŵ)).hom
      ((NK.NUV2.ARL.HR.inflation (K := k) (L := L) (E := E)).hom a) with hAval
  -- cardinality / cyclicity inputs
  have hcardG := (Work.SSGRoute.eb_loc_card k k E ŵ).1
  have hgenG := (Work.SSGRoute.eb_loc_card k k E ŵ).2
  have hcardS : Nat.card (groupCohomology (Rep.res
      (Work.SSGRoute.stabIncl (k := k) (M := M) (NK.GlobalCFT.Place.ofFinite ŵ))
      (NK.HassePrinciple.localUnitsRep k E (NK.GlobalCFT.Place.ofFinite ŵ))) 2) =
      Nat.card (MulAction.stabilizer (E ≃ₐ[M] E) (NK.GlobalCFT.Place.ofFinite ŵ)) := by
    rw [Work.SSGRoute.res_stabIncl_localUnitsRep_eq (k := k) (M := M) (E := E) (NK.GlobalCFT.Place.ofFinite ŵ)]
    exact (Work.SSGRoute.eb_loc_card k M E ŵ).1
  have hgenS : ∃ v : groupCohomology (Rep.res
      (Work.SSGRoute.stabIncl (k := k) (M := M) (NK.GlobalCFT.Place.ofFinite ŵ))
      (NK.HassePrinciple.localUnitsRep k E (NK.GlobalCFT.Place.ofFinite ŵ))) 2,
      addOrderOf v = Nat.card (groupCohomology (Rep.res
      (Work.SSGRoute.stabIncl (k := k) (M := M) (NK.GlobalCFT.Place.ofFinite ŵ))
      (NK.HassePrinciple.localUnitsRep k E (NK.GlobalCFT.Place.ofFinite ŵ))) 2) := by
    rw [Work.SSGRoute.res_stabIncl_localUnitsRep_eq (k := k) (M := M) (E := E) (NK.GlobalCFT.Place.ofFinite ŵ)]
    exact (Work.SSGRoute.eb_loc_card k M E ŵ).2
  -- Fintype instances
  haveI : Fintype (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite r)) :=
    Fintype.ofFinite _
  haveI : Fintype (Work.SSGRoute.stabIncl (k := k) (M := M)
      (NK.GlobalCFT.Place.ofFinite ŵ)).range := Fintype.ofFinite _
  haveI : Fintype (MulAction.stabilizer (E ≃ₐ[k] E) (NK.GlobalCFT.Place.ofFinite ŵ)) :=
    Fintype.ofFinite _
  haveI : Fintype (MulAction.stabilizer (E ≃ₐ[M] E) (NK.GlobalCFT.Place.ofFinite ŵ)) :=
    Fintype.ofFinite _
  -- the class at level E is n₂-torsion
  have hα : Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite r)) •
      ((NK.HassePrinciple.locUnits k L (NK.GlobalCFT.Place.ofFinite r)).hom a) = 0 :=
    natCard_nsmul_localUnitsRep_eq_zero (NK.GlobalCFT.Place.ofFinite r) _
  have hloc := congrArg (fun f => (ConcreteCategory.hom f) a)
    (NK.NUV2.ARL.HR.locUnits_inflation_eq (K := k) (M := L) (E := E)
      (NK.GlobalCFT.Place.ofFinite r) (NK.GlobalCFT.Place.ofFinite ŵ) hwr)
  simp only [ConcreteCategory.comp_apply] at hloc
  have hA0 : Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite r)) •
      Aval = 0 := by
    rw [hAval, hloc, ← map_nsmul, hα, map_zero]
  -- n₂ divides the index
  have hdvd : Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite r)) ∣
      (Work.SSGRoute.stabIncl (k := k) (M := M)
        (NK.GlobalCFT.Place.ofFinite ŵ)).range.index := by
    rw [eb_crux_ncard_eq_ef k L v₀ r hrL, eb_crux_index_eq_ef k M E v₀ W ŵ hŵW hWL]
    obtain ⟨h1, h2⟩ := hM W hWL
    have h2' : N ∣ W.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) *
        W.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
      rw [h1, one_mul]; exact h2
    exact dvd_trans (hL r hrL) h2'
  refine Work.SSGRoute.res_eq_zero_of_card_dvd
    (φ := Work.SSGRoute.stabIncl (k := k) (M := M) (NK.GlobalCFT.Place.ofFinite ŵ))
    (hφ := Work.SSGRoute.stabIncl_injective (k := k) (M := M)
      (NK.GlobalCFT.Place.ofFinite ŵ))
    (A := NK.HassePrinciple.localUnitsRep k E (NK.GlobalCFT.Place.ofFinite ŵ))
    (hcardG := hcardG) (hgenG := hgenG) (hcardS := hcardS) (hgenS := hgenS) (hx := ?_)
  obtain ⟨c, hc⟩ := hdvd
  calc (Work.SSGRoute.stabIncl (k := k) (M := M) (NK.GlobalCFT.Place.ofFinite ŵ)).range.index • Aval
      = (Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite r)) * c) • Aval := by
        rw [hc]
    _ = c • (Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite r)) • Aval) := by
        rw [mul_nsmul]
    _ = c • 0 := by rw [hA0]
    _ = 0 := by rw [smul_zero]

end Work.SSGRoute
