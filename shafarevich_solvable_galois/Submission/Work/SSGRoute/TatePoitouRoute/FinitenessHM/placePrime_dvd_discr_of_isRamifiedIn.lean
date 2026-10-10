import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Submission.Work.SSGRoute.dvd_discr_of_isRamifiedIn
import Submission.Work.SSGRoute.place_basics
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Ramification in a *non-Galois* finite extension and the discriminant

`Work.SSGRoute.dvd_discr_of_isRamifiedIn` proves that a finite place of `ℚ̄` that is ramified in a
finite *Galois* extension `Λ/ℚ` lies over a rational prime dividing `discr Λ`; its proof uses the
restriction `Gal(ℚ̄/ℚ) → Gal(Λ/ℚ)` and therefore needs `[IsGalois ℚ Λ]`.

Here we remove the Galois hypothesis.  The place `B` of `ℚ̄` fixes a prime `P = B ∩ 𝓞 Λ` of `𝓞 Λ`,
and `IsRamifiedIn ℚ Λ B` says that the inertia subgroup `I_B ≤ Gal(ℚ̄/ℚ)` is *not* contained in
`Gal(ℚ̄/Λ)`, i.e. that the ramification index `e(P/p)` of `P` over the rational prime `p` below `B`
is `> 1`.  The proof passes to the Galois closure `N` of `Λ` inside `ℚ̄`: the image of `I_B` under
`Gal(ℚ̄/ℚ) → Gal(N/ℚ)` is the inertia subgroup `J = Ideal.inertia Gal(N/ℚ) Q` of the prime `Q | B`
of `𝓞 N`, while the elements of `I_B` fixing `Λ` pointwise map onto `J ⊓ Gal(N/Λ)`.  A witness
`σ ∈ I_B` that does not fix `Λ` therefore makes `J ⊓ Gal(N/Λ)` a *proper* subgroup of `J`; taking
cardinalities (`#I_Q = e(Q/ℚ)`, `#(I_Q ⊓ Gal(N/Λ)) = e(Q/P)`) and the tower formula
`e(Q/ℚ) = e(P/ℚ) · e(Q/P)` shows `e(P/ℚ) ≠ 1`, and `NumberField.not_dvd_discr_iff_forall_mem`
turns this into `p ∣ discr Λ`.

Also proved here, as the mathematical heart of the above, is the standalone statement
`ramificationIdx_ne_one_of_isRamifiedIn` (a place ramified in a finite extension cuts out a prime
that is ramified over `ℤ`).
-/

open scoped NumberField Pointwise
open _root_.SSGRoute

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

/-- **An inertia element of a place that does not fix `Λ` forces the prime of `𝓞 Λ` below it to be
ramified over `ℤ`.**

This is the Galois-free form of the ramification bookkeeping: `Λ/ℚ` is only assumed finite.  The
Galois closure `N` of `Λ` is used as an auxiliary level, and the inertia count
`e(P/ℤ) = [I_Q : I_Q ⊓ Gal(N/Λ)]` is computed from the cardinalities of the inertia subgroups
(`Ideal.card_inertia_eq_ramificationIdxIn`) together with the tower formula
`Ideal.ramificationIdx_tower`. -/
theorem ramificationIdx_ne_one_of_isRamifiedIn (Λ : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ Λ] (B : ValuationSubring SSGRoute.QBar)
    (hB : SSGRoute.IsFinPlace ℚ B) (h : SSGRoute.IsRamifiedIn ℚ Λ B) :
    (NK.Reconstruct.primeOfLevel B Λ (Work.SSGRoute.comap_level_ne_top' B hB Λ)).asIdeal.ramificationIdx
      ℤ ≠ 1 := by
  haveI : NumberField ↥Λ := NumberField.of_module_finite ℚ ↥Λ
  -- the Galois closure of `Λ` inside `ℚ̄`
  let N : IntermediateField ℚ SSGRoute.QBar := IntermediateField.normalClosure ℚ (↥Λ) SSGRoute.QBar
  haveI hfd : FiniteDimensional ℚ ↥N := normalClosure.is_finiteDimensional ℚ ↥Λ SSGRoute.QBar
  haveI hgal : IsGalois ℚ ↥N := IsGalois.normalClosure ℚ ↥Λ SSGRoute.QBar
  haveI hnorm : Normal ℚ ↥N := IsGalois.to_normal
  haveI hnf : NumberField ↥N := NumberField.of_module_finite ℚ ↥N
  have hΛN : Λ ≤ N := IntermediateField.le_normalClosure Λ
  letI : Algebra ↥Λ ↥N := (IntermediateField.inclusion hΛN).toRingHom.toAlgebra
  haveI hST : IsScalarTower ℚ ↥Λ ↥N :=
    IsScalarTower.of_algebraMap_eq (fun x => ((IntermediateField.inclusion hΛN).commutes x))
  haveI hfinG : Finite (↥N ≃ₐ[ℚ] ↥N) := Finite.of_fintype _
  -- the subgroup of `Gal(N/ℚ)` fixing `Λ` pointwise, i.e. `Gal(N/Λ)`
  let Stab : Subgroup (↥N ≃ₐ[ℚ] ↥N) :=
    fixingSubgroup (↥N ≃ₐ[ℚ] ↥N) (Set.range (algebraMap ↥Λ ↥N))
  haveI hSG : IsGaloisGroup Stab ↥Λ ↥N := IsGaloisGroup.of_isScalarTower (↥N ≃ₐ[ℚ] ↥N) ℚ ↥N (↥Λ)
  haveI hSGring : IsGaloisGroup Stab (𝓞 ↥Λ) (𝓞 ↥N) :=
    IsGaloisGroup.of_isFractionRing Stab (𝓞 ↥Λ) (𝓞 ↥N) ↥Λ ↥N
  -- the primes of `𝓞 N` and `𝓞 Λ` below `B`
  let Q : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥N) :=
    NK.Reconstruct.primeOfLevel B N (NK.Reconstruct.comap_level_ne_top hB N)
  haveI hQprime : Q.asIdeal.IsPrime := Q.isPrime
  let P : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥Λ) :=
    NK.Reconstruct.primeOfLevel B Λ (NK.Reconstruct.comap_level_ne_top hB Λ)
  haveI hPprime : P.asIdeal.IsPrime := P.isPrime
  -- `P` is the prime of `𝓞 Λ` below `Q`
  have hquq : IsDedekindDomain.HeightOneSpectrum.under (𝓞 ↥Λ) Q = P := by
    have hcomp : (algebraMap ↥N SSGRoute.QBar).comp (algebraMap ↥Λ ↥N) =
        algebraMap ↥Λ SSGRoute.QBar := by
      ext x; rfl
    have hspecQ : B.comap (algebraMap ↥N SSGRoute.QBar) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥N Q :=
      NK.Reconstruct.primeOfLevel_spec B N (NK.Reconstruct.comap_level_ne_top hB N)
    have hspecP : B.comap (algebraMap ↥Λ SSGRoute.QBar) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥Λ P :=
      NK.Reconstruct.primeOfLevel_spec B Λ (NK.Reconstruct.comap_level_ne_top hB Λ)
    have h1 : (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥N Q).comap
        (algebraMap ↥Λ ↥N) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥Λ
          (IsDedekindDomain.HeightOneSpectrum.under (𝓞 ↥Λ) Q) :=
      Commons.RingTheory.Valuation.comap_valuationSubringAtPrime _ Q
        (Ideal.LiesOver.mk (by rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]))
    have h2 : (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥N Q).comap
        (algebraMap ↥Λ ↥N) = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥Λ P := by
      rw [← hspecQ, ValuationSubring.comap_comap, hcomp, hspecP]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (h1.symm.trans h2)
  have hP_eq : P.asIdeal = Q.asIdeal.under (𝓞 ↥Λ) := by
    rw [← hquq, IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
  haveI hlies : Q.asIdeal.LiesOver P.asIdeal := by
    rw [hP_eq]; exact Ideal.LiesOver.mk rfl
  -- the witness `σ` of ramification and its image in `Gal(N/ℚ)`
  obtain ⟨σ, hσin, hσfix⟩ := h
  have hτmem : AlgEquiv.restrictNormalHom ↥N σ ∈
      Ideal.inertia (↥N ≃ₐ[ℚ] ↥N) Q.asIdeal := by
    have h1 := Work.SSGRoute.mem_inertia_of_isInertia N B hB hσin
    simpa using h1
  have hτnot : AlgEquiv.restrictNormalHom ↥N σ ∉ Stab := by
    intro hτ
    apply hσfix
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hfix := (mem_fixingSubgroup_iff (↥N ≃ₐ[ℚ] ↥N)).mp hτ (algebraMap ↥Λ ↥N ⟨x, hx⟩)
      (Set.mem_range_self _)
    rw [AlgEquiv.smul_def] at hfix
    have key := AlgEquiv.restrictNormal_commutes σ ↥N (algebraMap ↥Λ ↥N ⟨x, hx⟩)
    rw [show (AlgEquiv.restrictNormalHom ↥N σ) (algebraMap ↥Λ ↥N ⟨x, hx⟩)
        = (σ.restrictNormal ↥N) (algebraMap ↥Λ ↥N ⟨x, hx⟩) from rfl] at hfix
    rw [hfix] at key
    exact key.symm
  -- the inertia subgroup `J` of `Q` in `Gal(N/ℚ)` and the cardinality bookkeeping
  let J : Subgroup (↥N ≃ₐ[ℚ] ↥N) := Ideal.inertia (↥N ≃ₐ[ℚ] ↥N) Q.asIdeal
  have hcardQ : Nat.card ↥J = Q.asIdeal.ramificationIdx ℤ := by
    have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := ↥N ≃ₐ[ℚ] ↥N) (R := ℤ) (S := 𝓞 ↥N)
      (Q.asIdeal.under ℤ) Q.asIdeal
    rw [hcard, Ideal.ramificationIdxIn_eq_ramificationIdx (G := ↥N ≃ₐ[ℚ] ↥N)
      (Q.asIdeal.under ℤ) Q.asIdeal]
  have hcardP : Nat.card ↥(Ideal.inertia Stab Q.asIdeal) = Q.asIdeal.ramificationIdx (𝓞 ↥Λ) := by
    have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := Stab) (R := 𝓞 ↥Λ) (S := 𝓞 ↥N)
      P.asIdeal Q.asIdeal
    rw [hcard, Ideal.ramificationIdxIn_eq_ramificationIdx (G := Stab) P.asIdeal Q.asIdeal]
  have hsub : J.subgroupOf Stab = Ideal.inertia Stab Q.asIdeal :=
    AddSubgroup.subgroupOf_inertia (I := Q.asIdeal.toAddSubgroup) Stab
  have hcard_inf : Nat.card ↥(J ⊓ Stab) = Q.asIdeal.ramificationIdx (𝓞 ↥Λ) := by
    rw [← hcardP, ← hsub]
    have heq : (J ⊓ Stab).subgroupOf Stab = J.subgroupOf Stab := by
      ext x; simp [Subgroup.mem_subgroupOf]
    rw [← heq]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
  -- `σ` lies in `J` but not in `Stab`, so `J ⊓ Stab` is a proper subgroup of `J` of index `> 1`
  have hHne : (J ⊓ Stab).subgroupOf J ≠ ⊤ := by
    intro hh
    have hmem : (⟨AlgEquiv.restrictNormalHom ↥N σ, hτmem⟩ : ↥J) ∈ (J ⊓ Stab).subgroupOf J := by
      rw [hh]; trivial
    exact hτnot ((Subgroup.mem_subgroupOf.mp hmem).2)
  have hidx : 1 < ((J ⊓ Stab).subgroupOf J).index := Subgroup.one_lt_index_of_ne_top hHne
  -- the tower formula and the conclusion
  have htower : Q.asIdeal.ramificationIdx ℤ =
      P.asIdeal.ramificationIdx ℤ * Q.asIdeal.ramificationIdx (𝓞 ↥Λ) :=
    Ideal.ramificationIdx_tower (R := ℤ) (S := 𝓞 ↥Λ) (T := 𝓞 ↥N) P.asIdeal Q.asIdeal
  have hmain : Q.asIdeal.ramificationIdx (𝓞 ↥Λ) * ((J ⊓ Stab).subgroupOf J).index
      = Q.asIdeal.ramificationIdx ℤ := by
    have hcm := Subgroup.card_mul_index ((J ⊓ Stab).subgroupOf J)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : J ⊓ Stab ≤ J)).toEquiv,
      hcard_inf, hcardQ] at hcm
    exact hcm
  have hpos : 0 < Q.asIdeal.ramificationIdx (𝓞 ↥Λ) :=
    Ideal.ramificationIdx_pos (R := 𝓞 ↥Λ) Q.asIdeal
  rintro h1eq
  have heq1 : ((J ⊓ Stab).subgroupOf J).index = 1 := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [mul_one, hmain, htower, h1eq, one_mul]
  rw [heq1] at hidx
  exact lt_irrefl 1 hidx

/-- **A place at which `Λ/ℚ` ramifies lies over a prime dividing `discr Λ`** — the Galois-free form of `Work.SSGRoute.dvd_discr_of_isRamifiedIn` (whose proof uses `AlgEquiv.restrictNormalHom` and therefore needs `[IsGalois ℚ Λ]`).  Here `Λ/ℚ` is only assumed finite: for a place `B | p` of `ℚ̄`, `IsRamifiedIn ℚ Λ B ⟺ I_B ⊄ Gal(ℚ̄/Λ) ⟺ e(P/p) > 1` for `P = B ∩ 𝓞 Λ` (the inertia count `e = [I_B : I_B ∩ Gal(ℚ̄/Λ)]`, via the Galois closure of `Λ`), and `e > 1 ⟹ p | discr Λ` by `NumberField.not_dvd_discr_iff_forall_mem`.  This is the input that confines the support of the discriminant to an explicitly known finite set of rational primes when the base field is an arbitrary number field. -/
theorem placePrime_dvd_discr_of_isRamifiedIn (Λ : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ Λ] (B : ValuationSubring SSGRoute.QBar)
    (hB : SSGRoute.IsFinPlace ℚ B) (h : SSGRoute.IsRamifiedIn ℚ Λ B) :
    (Work.SSGRoute.placePrime B hB).1 ∣ (NumberField.discr Λ).natAbs := by
  have hramIdx : (NK.Reconstruct.primeOfLevel B Λ
      (Work.SSGRoute.comap_level_ne_top' B hB Λ)).asIdeal.ramificationIdx ℤ ≠ 1 :=
    ramificationIdx_ne_one_of_isRamifiedIn Λ B hB h
  -- the rational prime below `B` lies in the prime of `𝓞 Λ` below `B`
  have hmemP : ((Work.SSGRoute.placePrime B hB).1 : 𝓞 ↥Λ) ∈
      (NK.Reconstruct.primeOfLevel B Λ (Work.SSGRoute.comap_level_ne_top' B hB Λ)).asIdeal := by
    rw [Work.SSGRoute.primeOfLevel_mem_iff Λ B hB]
    simpa using Work.SSGRoute.placePrime_val_lt_one B hB
  -- `p ∣ discr Λ`, by the ramification criterion for the discriminant
  have hpZ : Prime ((Work.SSGRoute.placePrime B hB).1 : ℤ) :=
    Nat.prime_iff_prime_int.mp (Work.SSGRoute.placePrime B hB).2
  have hkey : ((Work.SSGRoute.placePrime B hB).1 : ℤ) ∣ NumberField.discr Λ := by
    by_contra hnd
    rw [NumberField.not_dvd_discr_iff_forall_mem Λ (𝓞 ↥Λ) hpZ] at hnd
    have hU : Algebra.IsUnramifiedAt ℤ
        (NK.Reconstruct.primeOfLevel B Λ (Work.SSGRoute.comap_level_ne_top' B hB Λ)).asIdeal :=
      hnd _ (NK.Reconstruct.primeOfLevel B Λ
        (Work.SSGRoute.comap_level_ne_top' B hB Λ)).isPrime hmemP
    haveI := hU
    exact hramIdx (Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := ℤ) (S := 𝓞 ↥Λ)
      (p := (NK.Reconstruct.primeOfLevel B Λ
        (Work.SSGRoute.comap_level_ne_top' B hB Λ)).asIdeal))
  have hfin := (Int.natAbs_dvd_natAbs (a := ((Work.SSGRoute.placePrime B hB).1 : ℤ))
    (b := NumberField.discr Λ)).mpr hkey
  rwa [Int.natAbs_natCast] at hfin

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
