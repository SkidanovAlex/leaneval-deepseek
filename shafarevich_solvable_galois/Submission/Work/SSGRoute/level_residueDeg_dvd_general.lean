import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.LocalFields.Basic
import Submission.Work.SSGRoute.E7Arch.exists_level_localDegree_ge_three
import Submission.Work.SSGRoute.exists_level_residueDeg
import Submission.Work.SSGRoute.inertiaAtLevelDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute
open scoped IntermediateField

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-- **A finite Galois level whose residue degree at a finite place of `Ω` is divisible by a
prescribed `d`** — the general-number-field version of `Work.SSGRoute.exists_level_residueDeg`
(the case `k = ℚ` in `Submission/Work/SSGRoute/exists_level_residueDeg.lean`, a complete template).

CONSTRUCTION.  Let `𝔭` be the prime of `𝓞 k` below `A`, `q := Nat.card (𝓞 k ⧸ 𝔭.asIdeal)`
(equivalently `Work.LocalFields.residueCard k 𝔭`), and `m := q ^ d - 1`.  Then `2 ≤ q`, `¬ p ∣ m`
for `p` the residue characteristic, and for a primitive `m`-th root of unity `ζ ∈ Ω`
(`NK.LocalAnabelian.exists_isPrimitiveRoot_of_isSepClosed`) the level
`L := IntermediateField.adjoin k {ζ}` is cyclotomic over `k`, hence `FiniteDimensional`, `Normal`
and a number field, and unramified at `A`.  The reduction of `ζ` mod `P_L := primeOfLevel A L` is a
primitive `m`-th root of unity (`Work.SSGRoute.isPrimitiveRoot_quotient_mk`), so with
`f := P_L.asIdeal.inertiaDeg (𝓞 k)` one has `m ∣ #(𝓞 L ⧸ P_L) - 1 = q ^ f - 1`, and
`Work.SSGRoute.dvd_of_pow_sub_one_dvd_pow_sub_one q d f` (needing only `2 ≤ q` and `0 < d`) gives
`d ∣ f`.  CAUTION (both reviewers): the ℚ proof sizes `m = p^d - 1` from the *rational* prime; for
general `k` the base must be the residue-field size `q = #κ(𝔭)`, otherwise one only gets
`d ∣ f₀ * f`.  `Submission/Work/SSGRoute/E7Arch/exists_level_localDegree_ge_three.lean` contains
the general-base version of the same divisibility computation. -/
theorem level_residueDeg_dvd_general (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (d : ℕ) (hd : 0 < d) :
    ∃ (L : IntermediateField k Ω) (_ : FiniteDimensional k L) (_ : Normal k L)
      (_ : NumberField ↥L),
      d ∣ ((NK.Reconstruct.primeOfLevel A L
        (NK.Reconstruct.comap_level_ne_top hA L)).asIdeal.inertiaDeg
          (NumberField.RingOfIntegers k)) := by
  -- `Ω` is separably closed, and the prime `𝔭` of `𝓞 k` below `A`
  haveI hsep : IsSepClosed Ω := (inferInstance : IsSepClosure k Ω).sep_closed
  let 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
    Submission.NeukirchUchida.primeOf A hA
  haveI hfinq : Finite (NumberField.RingOfIntegers k ⧸ 𝔭.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum 𝔭
  haveI hfintq : Fintype (NumberField.RingOfIntegers k ⧸ 𝔭.asIdeal) := Fintype.ofFinite _
  haveI hfieldq : Field (NumberField.RingOfIntegers k ⧸ 𝔭.asIdeal) :=
    Ideal.Quotient.field 𝔭.asIdeal
  -- the residue-field size `q` and the exponent `m = q ^ d - 1`
  let q : ℕ := Nat.card (NumberField.RingOfIntegers k ⧸ 𝔭.asIdeal)
  have hq2 : 2 ≤ q := by
    show 2 ≤ Nat.card (NumberField.RingOfIntegers k ⧸ 𝔭.asIdeal)
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  let m : ℕ := q ^ d - 1
  have hmpos : 0 < m := by
    have h1 : 1 < q ^ d := Nat.one_lt_pow (by omega) (by omega)
    change 0 < q ^ d - 1
    omega
  haveI hmne : NeZero m := ⟨hmpos.ne'⟩
  haveI hmcast : NeZero ((m : ℕ) : Ω) := ⟨fun h => hmpos.ne' (by
    have h' : algebraMap k Ω (m : k) = 0 := by rw [map_natCast, h]
    exact Nat.cast_eq_zero.mp ((algebraMap k Ω).injective (h'.trans (map_zero _).symm)))⟩
  -- the residue characteristic `p`, which divides the residue-field size `q`
  let p : ℕ := ringChar (NumberField.RingOfIntegers k ⧸ 𝔭.asIdeal)
  have hp_dvd_q : p ∣ q := by
    show p ∣ Nat.card (NumberField.RingOfIntegers k ⧸ 𝔭.asIdeal)
    exact ringChar.dvd (by rw [Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _)
  have hp1 : p ≠ 1 := by
    intro h
    have h1 : ((1 : ℕ) : (NumberField.RingOfIntegers k ⧸ 𝔭.asIdeal)) = 0 :=
      (ringChar.spec (NumberField.RingOfIntegers k ⧸ 𝔭.asIdeal) 1).mpr (by rw [← h])
    rw [Nat.cast_one] at h1
    exact one_ne_zero h1
  have hpm : ¬ p ∣ m := by
    intro hdiv
    have hqd : p ∣ q ^ d := dvd_pow hp_dvd_q (by omega)
    have h2 : p ∣ q ^ d - (q ^ d - 1) := Nat.dvd_sub hqd hdiv
    rw [Nat.sub_sub_self (Nat.one_le_pow d q (by omega))] at h2
    exact hp1 (Nat.dvd_one.mp h2)
  -- a primitive `m`-th root of unity `ζ ∈ Ω` and the level `L = k⟮ζ⟯`
  obtain ⟨ζ, hζ⟩ :=
    NK.LocalAnabelian.exists_isPrimitiveRoot_of_isSepClosed (K := Ω) (n := m)
  let L : IntermediateField k Ω := k⟮ζ⟯
  haveI hcyc : IsCyclotomicExtension ({m} : Set ℕ) k ↥L :=
    hζ.intermediateField_adjoin_isCyclotomicExtension k
  haveI hfd : FiniteDimensional k ↥L :=
    IsCyclotomicExtension.finiteDimensional ({m} : Set ℕ) k ↥L
  haveI hnorm : Normal k ↥L :=
    (IsCyclotomicExtension.isGalois ({m} : Set ℕ) k ↥L).to_normal
  haveI hnf : NumberField ↥L := NumberField.of_module_finite k ↥L
  refine ⟨L, hfd, hnorm, hnf, ?_⟩
  let P : NK.Chebotarev.PrimeIdeal ↥L :=
    NK.Reconstruct.primeOfLevel A L (NK.Reconstruct.comap_level_ne_top hA L)
  show d ∣ P.asIdeal.inertiaDeg (NumberField.RingOfIntegers k)
  have hlies : P.asIdeal.LiesOver 𝔭.asIdeal :=
    NK.ResidueFrob.primeOfLevel_liesOver (K := k) (K' := Ω) ⟨A, hA⟩ L
  -- the residue field `κ` of `L` at `P`, of cardinality `q ^ f`
  let κ := NK.CFTLib.IdeleHasse.Descent.ResidueFieldOf ↥L P
  haveI hκfin : Finite κ :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum P
  have hNcard : Nat.card κ = q ^ P.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
    show Nat.card (NumberField.RingOfIntegers ↥L ⧸ P.asIdeal) =
      Nat.card (NumberField.RingOfIntegers k ⧸ 𝔭.asIdeal) ^
        P.asIdeal.inertiaDeg (NumberField.RingOfIntegers k)
    exact Commons.NumberTheory.NumberField.natCard_residue_eq_pow_inertiaDeg 𝔭 P hlies
  -- `ζ` as an element of `L` and of `𝓞 L`
  let ζL : ↥L := ⟨ζ, IntermediateField.mem_adjoin_simple_self k ζ⟩
  have hζL : IsPrimitiveRoot ζL m :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp
      (by rw [show (ζL : Ω) = ζ from rfl]; exact hζ)
  have hint : IsIntegral ℤ ζL := hζL.isIntegral hmpos
  obtain ⟨ζO, hζOeq⟩ := (IsIntegralClosure.isIntegral_iff
    (A := NumberField.RingOfIntegers ↥L) (R := ℤ) (B := ↥L)).mp hint
  have hζO : IsPrimitiveRoot ζO m := by
    have h1 : IsPrimitiveRoot ((ζO : ↥L)) m := by
      rw [show ((ζO : ↥L)) = ζL from hζOeq]
      exact hζL
    exact IsPrimitiveRoot.coe_submonoidClass_iff.mp h1
  -- an integer in `P` is divisible by the residue characteristic
  have hdvdP : ∀ n : ℕ, (n : NumberField.RingOfIntegers ↥L) ∈ P.asIdeal → p ∣ n := by
    intro n hn
    have h1 : (n : NumberField.RingOfIntegers k) ∈
        P.asIdeal.under (NumberField.RingOfIntegers k) := by
      rw [Ideal.mem_under, map_natCast]
      exact hn
    rw [← hlies.over] at h1
    have h2 : ((n : ℕ) : NumberField.RingOfIntegers k ⧸ 𝔭.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk 𝔭.asIdeal) n]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h1
    exact ringChar.dvd h2
  -- reduction of `ζ` mod `P` is a primitive `m`-th root of unity
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
  have hm_dvd' : q ^ d - 1 ∣ q ^ P.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) - 1 := by
    rw [← hNcard]
    exact hm_dvd
  exact dvd_of_pow_sub_one_dvd_pow_sub_one q d
    (P.asIdeal.inertiaDeg (NumberField.RingOfIntegers k)) hq2 hd hm_dvd'

end Work.SSGRoute
