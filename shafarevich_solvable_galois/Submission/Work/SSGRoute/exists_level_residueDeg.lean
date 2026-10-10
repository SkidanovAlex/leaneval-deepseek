import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.CFTLib.IdeleHasse.Descent.dvd_localDegree_of_isPrimitiveRoot
import Submission.Work.SSGRoute.RamifiedPlacesAux
import Submission.Work.SSGRoute.isPrimitiveRoot_quotient_mk
import Submission.Work.SSGRoute.local_lifting_setup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A level whose residue degree at a finite place of `ℚ̄` is divisible by any prescribed `d`

For a finite place `A` of `ℚ̄` and any `d > 0` we produce a finite normal number field `L ⊆ ℚ̄`
whose residue degree at the place below `A` is divisible by `d`.

The construction is the cyclotomic one: let `p` be the rational prime below `A` and take
`L = ℚ(ζ_m)` for `m = p ^ d - 1`.  Since `p ∤ m`, the place `A ∩ L` is unramified over `ℚ`, the
reduction of `ζ_m` to the residue field `κ = 𝓞 L ⧸ P` is a primitive `m`-th root of unity, and
`m ∣ #κ - 1 = p ^ f - 1` where `f` is the residue degree.  The arithmetic fact that
`p ^ d - 1 ∣ p ^ f - 1` forces `d ∣ f` then gives the claim.

The auxiliary lemmas at the top of this file are the two elementary facts about `𝓞 ℚ` that are
used to identify the rational prime `p` (the generator of the prime of `𝓞 ℚ` below `A`) with the
residue-characteristic data used in the main argument.
-/

open SSGRoute
open scoped IntermediateField

namespace Work.SSGRoute

/-- **Elementary number theory.**  If `2 ≤ p` and `0 < d` then `p ^ d - 1 ∣ p ^ f - 1` forces
`d ∣ f`. -/
theorem dvd_of_pow_sub_one_dvd_pow_sub_one (p d f : ℕ) (hp : 2 ≤ p) (hd : 0 < d)
    (h : p ^ d - 1 ∣ p ^ f - 1) : d ∣ f := by
  rw [Nat.dvd_iff_mod_eq_zero]
  by_contra hne
  have hpos : 0 < f % d := Nat.pos_of_ne_zero hne
  have hlt : f % d < d := Nat.mod_lt f hd
  have hp2 : 1 < p := by omega
  have hkey : p ^ d - 1 ∣ p ^ (f % d) - 1 := by
    have h1 : p ^ d - 1 ∣ p ^ (d * (f / d)) - 1 :=
      Nat.pow_sub_one_dvd_pow_sub_one p (dvd_mul_right d (f / d))
    have h2 : p ^ d - 1 ∣ p ^ (f % d) * (p ^ (d * (f / d)) - 1) :=
      dvd_mul_of_dvd_right h1 _
    have hsplit : p ^ f - 1 =
        p ^ (f % d) * (p ^ (d * (f / d)) - 1) + (p ^ (f % d) - 1) := by
      have hf : f = f % d + d * (f / d) := (Nat.mod_add_div f d).symm
      have hA : 1 ≤ p ^ (d * (f / d)) := Nat.one_le_pow _ _ (by omega)
      have hB : 1 ≤ p ^ (f % d) := Nat.one_le_pow _ _ (by omega)
      have h1 : p ^ f = p ^ (f % d) * p ^ (d * (f / d)) := by
        conv_lhs => rw [hf]
        rw [pow_add]
      have hmul : p ^ (f % d) * (p ^ (d * (f / d)) - 1)
          = p ^ (f % d) * p ^ (d * (f / d)) - p ^ (f % d) := by
        rw [Nat.mul_sub_left_distrib, mul_one]
      have hBX : p ^ (f % d) ≤ p ^ (f % d) * p ^ (d * (f / d)) := by
        calc p ^ (f % d) = p ^ (f % d) * 1 := (mul_one _).symm
          _ ≤ p ^ (f % d) * p ^ (d * (f / d)) := Nat.mul_le_mul_left _ hA
      rw [h1, hmul]
      omega
    have h3 : p ^ d - 1 ∣ (p ^ f - 1) - p ^ (f % d) * (p ^ (d * (f / d)) - 1) :=
      Nat.dvd_sub h h2
    rw [hsplit, Nat.add_sub_cancel_left] at h3
    exact h3
  have hlt2 : p ^ (f % d) - 1 < p ^ d - 1 :=
    Nat.sub_lt_sub_right (Nat.one_le_pow _ _ (by omega))
      (Nat.pow_lt_pow_right hp2 hlt)
  have hzero : p ^ (f % d) - 1 = 0 := by
    rcases Nat.eq_zero_or_pos (p ^ (f % d) - 1) with h0 | hpos2
    · exact h0
    · exact absurd hlt2 (not_lt.mpr (Nat.le_of_dvd hpos2 hkey))
  have h1 : p ^ (f % d) = 1 := by
    have hle := Nat.sub_eq_zero_iff_le.mp hzero
    have hge := Nat.one_le_pow (f % d) p (by omega)
    omega
  have h2 : f % d = 0 := by
    by_contra hcon
    have : 1 < p ^ (f % d) := Nat.one_lt_pow hcon hp2
    omega
  exact hne h2

/-- The residue field `𝓞 ℚ ⧸ q` of a place `q` of `ℚ` has `natGenerator q` elements. -/
theorem natCard_quotient_rat_primeIdeal
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    Nat.card (NumberField.RingOfIntegers ℚ ⧸ q.asIdeal) =
      Rat.HeightOneSpectrum.natGenerator q := by
  calc Nat.card (NumberField.RingOfIntegers ℚ ⧸ q.asIdeal)
      = Nat.card (ℤ ⧸ Ideal.map
          (Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)) q.asIdeal) :=
        Nat.card_congr (Ideal.quotientEquiv q.asIdeal _
          (Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)) rfl).toEquiv
    _ = Nat.card (ℤ ⧸ Ideal.span {(Rat.HeightOneSpectrum.natGenerator q : ℤ)}) := by
        rw [Rat.HeightOneSpectrum.span_natGenerator]
    _ = Nat.card (ZMod (Rat.HeightOneSpectrum.natGenerator q)) :=
        Nat.card_congr (Int.quotientSpanNatEquivZMod _).toEquiv
    _ = Rat.HeightOneSpectrum.natGenerator q := by
        haveI : NeZero (Rat.HeightOneSpectrum.natGenerator q) :=
          ⟨(Rat.HeightOneSpectrum.prime_natGenerator q).ne_zero⟩
        rw [Nat.card_eq_fintype_card, ZMod.card]

/-- An integer lies in the place `q` of `ℚ` exactly when `natGenerator q` divides it. -/
theorem rat_primeIdeal_mem_iff
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (N : ℕ) :
    (N : NumberField.RingOfIntegers ℚ) ∈ q.asIdeal ↔
      Rat.HeightOneSpectrum.natGenerator q ∣ N := by
  have h := Ideal.apply_mem_of_equiv_iff (I := q.asIdeal)
    (f := Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ))
    (x := (N : NumberField.RingOfIntegers ℚ))
  simp only [map_natCast] at h
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
  exact h.symm

theorem exists_level_residueDeg
    (A : ValuationSubring SSGRoute.QBar) (hA : SSGRoute.IsFinPlace ℚ A)
    (d : ℕ) (hd : 0 < d) :
    ∃ (L : IntermediateField ℚ SSGRoute.QBar) (hL : FiniteDimensional ℚ L)
      (hLn : Normal ℚ L) (hLnf : NumberField ↥L),
      d ∣ ((NK.Reconstruct.primeOfLevel A L
        (NK.Reconstruct.comap_level_ne_top hA L)).asIdeal.inertiaDeg
          (NumberField.RingOfIntegers ℚ)) := by
  haveI hsep : IsSepClosed SSGRoute.QBar :=
    (inferInstance : IsSepClosure ℚ SSGRoute.QBar).sep_closed
  let 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
    Submission.NeukirchUchida.primeOf A hA
  let p : ℕ := Rat.HeightOneSpectrum.natGenerator 𝔭
  have hpprime : Nat.Prime p := Rat.HeightOneSpectrum.prime_natGenerator 𝔭
  have hp2 : 2 ≤ p := hpprime.two_le
  let m : ℕ := p ^ d - 1
  have hmpos : 0 < m := by
    have h1 : 1 < p ^ d := Nat.one_lt_pow (by omega) (by omega)
    change 0 < p ^ d - 1
    omega
  have hpm : ¬ p ∣ m := by
    intro hdiv
    have h1 : p ∣ p ^ d := dvd_pow_self p (by omega)
    have h2 : p ∣ p ^ d - (p ^ d - 1) := Nat.dvd_sub h1 hdiv
    rw [Nat.sub_sub_self (Nat.one_le_pow d p (by omega))] at h2
    exact hpprime.not_dvd_one h2
  haveI hmne : NeZero m := ⟨hmpos.ne'⟩
  haveI hmcast : NeZero ((m : ℕ) : SSGRoute.QBar) :=
    ⟨fun h => hmpos.ne' (by exact_mod_cast h)⟩
  obtain ⟨ζ, hζ⟩ :=
    NK.LocalAnabelian.exists_isPrimitiveRoot_of_isSepClosed (K := SSGRoute.QBar) (n := m)
  let L : IntermediateField ℚ SSGRoute.QBar := ℚ⟮ζ⟯
  haveI hcyc : IsCyclotomicExtension ({m} : Set ℕ) ℚ ↥L :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  haveI hfd : FiniteDimensional ℚ ↥L :=
    IsCyclotomicExtension.finiteDimensional ({m} : Set ℕ) ℚ ↥L
  haveI hnorm : Normal ℚ ↥L :=
    (IsCyclotomicExtension.isGalois ({m} : Set ℕ) ℚ ↥L).to_normal
  haveI hnf : NumberField ↥L := NumberField.of_module_finite ℚ ↥L
  refine ⟨L, hfd, hnorm, hnf, ?_⟩
  let P : NK.Chebotarev.PrimeIdeal ↥L :=
    NK.Reconstruct.primeOfLevel A L (NK.Reconstruct.comap_level_ne_top hA L)
  show d ∣ P.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ)
  have hlies : P.asIdeal.LiesOver 𝔭.asIdeal := primeOfLevel_liesOver' L A hA
  have hF : Nat.card (NumberField.RingOfIntegers ℚ ⧸ 𝔭.asIdeal) = p := by
    change Nat.card (NumberField.RingOfIntegers ℚ ⧸ 𝔭.asIdeal)
      = Rat.HeightOneSpectrum.natGenerator 𝔭
    exact natCard_quotient_rat_primeIdeal 𝔭
  let κ := NK.CFTLib.IdeleHasse.Descent.ResidueFieldOf ↥L P
  haveI hκfin : Finite κ :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum P
  have hNcard : Nat.card κ = p ^ P.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) := by
    show Nat.card (NumberField.RingOfIntegers ↥L ⧸ P.asIdeal) = _
    rw [Commons.NumberTheory.NumberField.natCard_residue_eq_pow_inertiaDeg 𝔭 P hlies, hF]
  let ζL : ↥L := ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩
  have hζL : IsPrimitiveRoot ζL m :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp
      (by rw [show (ζL : SSGRoute.QBar) = ζ from rfl]; exact hζ)
  have hint : IsIntegral ℤ ζL := hζL.isIntegral hmpos
  obtain ⟨ζO, hζOeq⟩ := (IsIntegralClosure.isIntegral_iff
    (A := NumberField.RingOfIntegers ↥L) (R := ℤ) (B := ↥L)).mp hint
  have hζO : IsPrimitiveRoot ζO m := by
    have h1 : IsPrimitiveRoot ((ζO : ↥L)) m := by
      rw [show ((ζO : ↥L)) = ζL from hζOeq]
      exact hζL
    exact IsPrimitiveRoot.coe_submonoidClass_iff.mp h1
  have hdvdP : ∀ n : ℕ, (n : NumberField.RingOfIntegers ↥L) ∈ P.asIdeal → p ∣ n := by
    intro n hn
    have h1 : (n : NumberField.RingOfIntegers ℚ) ∈
        P.asIdeal.under (NumberField.RingOfIntegers ℚ) := by
      rw [Ideal.mem_under, map_natCast]
      exact hn
    rw [← hlies.over] at h1
    have h2 : Rat.HeightOneSpectrum.natGenerator 𝔭 ∣ n :=
      (rat_primeIdeal_mem_iff 𝔭 n).mp h1
    exact h2
  have hpri : IsPrimitiveRoot (Ideal.Quotient.mk P.asIdeal ζO : κ) m :=
    isPrimitiveRoot_quotient_mk P.asIdeal hmpos hdvdP hpm hζO
  have hm_dvd : m ∣ Nat.card κ - 1 := by
    have hη0 : (Ideal.Quotient.mk P.asIdeal ζO : κ) ≠ 0 := by
      intro h0
      have h1 := hpri.1
      rw [h0, zero_pow hmpos.ne'] at h1
      exact one_ne_zero h1.symm
    let u : κˣ := Units.mk0 _ hη0
    have hu : (u : κ) = (Ideal.Quotient.mk P.asIdeal ζO : κ) := rfl
    have huo : orderOf u = m := by
      rw [← orderOf_units, hu]; exact hpri.eq_orderOf.symm
    have h := orderOf_dvd_natCard u
    rwa [huo, Nat.card_units] at h
  have hm_dvd' : m ∣ p ^ P.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) - 1 := by
    rw [hNcard] at hm_dvd
    exact hm_dvd
  exact dvd_of_pow_sub_one_dvd_pow_sub_one p d
    (P.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ)) hp2 hd hm_dvd'

end Work.SSGRoute
