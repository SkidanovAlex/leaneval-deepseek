import Mathlib
import Submission.Work.SSGRoute.brauer_single_place
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.exists_level_residueDeg
import Submission.Work.SSGRoute.exists_level_inertiaDeg_mul_dvd
import Submission.Work.SSGRoute.level_residueDeg_dvd_general
import Submission.Work.SSGRoute.E7cOmega.exists_level_p_dvd_decomp
import Submission.Work.SSGRoute.E7cC.exists_level_unramified_p_dvd_inertiaDeg
import Submission.NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A finite Galois level at which a prescribed finite place is unramified with `N`-divisible
residue degree

This is the `p ↦ N` generalisation of `Work.SSGRoute.E7cC.exists_level_unramified_p_dvd_inertiaDeg`
(whose proof is adapted verbatim: primality enters only through `N ≥ 1` and `2 ≤ |κ(q)|`).

It is the second ingredient of clause (6)'s arithmetic input
(`Work.SSGRoute.PT.G1plusOwn.exists_unramified_level_factors`): combined with
`Work.SSGRoute.levelSub_comap_index_eq_inertiaDeg` and
`Work.SSGRoute.PT.G1plusOwn.levelSub_index_chain` it produces a finite Galois level `M' ≥ K`,
unramified at a prescribed place, whose level subgroup has index divisible by `2 * U.index` — hence
inside the constancy subgroup of the cocycle.
-/

open scoped IntermediateField NumberField

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.PT.G1plusOwn

/-- **A finite Galois level at which a prescribed finite place is unramified with `N`-divisible
residue degree.**

Let `k ⊆ K` be number fields with `K/k` finite Galois, `Ω` an algebraic closure of `k`, `q` a
finite place of `K` and `N ≠ 0`.  Then there is a finite Galois level `L ⊇ K` over `k` and a place
`q'` of `L` above `q` such that `q` is *unramified* in `L/K` (`e(q'|q) = 1`) while `N ∣ f(q'|q)`.

Route (the same proof as the on-disk `Work.SSGRoute.E7cC.exists_level_unramified_p_dvd_inertiaDeg`,
which does the case `N = p` prime, with `p ↦ N`): take
`m := Nat.card (𝓞 K ⧸ q.asIdeal) ^ N - 1` and `L := K ⊔ k⟮ζ_m⟯` for a primitive `m`-th root of unity
`ζ_m ∈ Ω`.  Then `L/k` is finite, normal and a number field (compositum of two such), and
`k⟮ζ_m⟯/k` is unramified at every place whose residue characteristic does not divide `m`; as
`m ≡ -1 mod |κ(q)|` we have `gcd(m, |κ(q)|) = 1`, so `L/K` is unramified at `q` and `e(q'|q) = 1`.
Finally the reduction of `ζ_m` modulo `q'` is a primitive `m`-th root of unity, so
`m ∣ Nat.card κ(q') - 1`, i.e. `|κ(q)| ^ N - 1 ∣ |κ(q)| ^ f - 1` with `f = f(q'|q)`, and
`Work.SSGRoute.dvd_of_pow_sub_one_dvd_pow_sub_one` gives `N ∣ f`. -/
theorem exists_level_unramified_mul_dvd
    (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (N : ℕ) (hN : N ≠ 0) :
    ∃ (L : IntermediateField K Ω), ∃ (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
      (_ : IsGalois k ↥L),
      ∃ (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L)),
        q'.asIdeal.LiesOver q.asIdeal ∧
        q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
        N ∣ q'.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
  classical
  haveI hΩchar : CharZero Ω :=
    charZero_of_injective_algebraMap (RingHom.injective (algebraMap k Ω))
  -- ## the residue field of `K` at `q`, of cardinality `Q`
  haveI hFinq : Finite (NumberField.RingOfIntegers K ⧸ q.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum q
  haveI hfintq : Fintype (NumberField.RingOfIntegers K ⧸ q.asIdeal) := Fintype.ofFinite _
  let Q : ℕ := Nat.card (NumberField.RingOfIntegers K ⧸ q.asIdeal)
  have hQ2 : 2 ≤ Q := by
    rw [show Q = Nat.card (NumberField.RingOfIntegers K ⧸ q.asIdeal) from rfl,
      Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  -- ## the cyclotomic exponent `m = Q ^ N - 1` and a primitive `m`-th root of unity
  let m : ℕ := Q ^ N - 1
  have hmpos : 0 < m := by
    have h1 : 1 < Q ^ N := Nat.one_lt_pow hN (by omega)
    rw [show m = Q ^ N - 1 from rfl]; omega
  haveI hmne : NeZero m := ⟨hmpos.ne'⟩
  haveI hmcast : NeZero ((m : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hmpos.ne'⟩
  obtain ⟨ζ, hζ⟩ := NK.LocalAnabelian.exists_isPrimitiveRoot_of_isSepClosed (K := Ω) (n := m)
  -- ## the levels `Kf = image of K`, `L₀ = k⟮ζ⟯` and their compositum `Lk`
  let Kf : IntermediateField k Ω := (IsScalarTower.toAlgHom k K Ω).fieldRange
  let L₀ : IntermediateField k Ω := IntermediateField.adjoin k ({ζ} : Set Ω)
  haveI hcyc₀ : IsCyclotomicExtension ({m} : Set ℕ) k ↥L₀ :=
    Work.SSGRoute.E7cC.isCyclotomicExtension_adjoin_primitiveRoot (K := k) hζ
  let Lk : IntermediateField k Ω := Kf ⊔ L₀
  haveI hfdKf : FiniteDimensional k Kf :=
    LinearEquiv.finiteDimensional
      (AlgHom.equivFieldRange (IsScalarTower.toAlgHom k K Ω)).toLinearEquiv
  haveI hfdL₀ : FiniteDimensional k L₀ := IsCyclotomicExtension.finiteDimensional {m} k ↥L₀
  haveI hgalKf : IsGalois k Kf :=
    IsGalois.of_algEquiv (AlgHom.equivFieldRange (IsScalarTower.toAlgHom k K Ω))
  haveI hgalL₀ : IsGalois k L₀ := IsCyclotomicExtension.isGalois {m} k ↥L₀
  haveI hgalLk : IsGalois k Lk := inferInstance
  haveI hfdLk : FiniteDimensional k Lk := IntermediateField.finiteDimensional_sup Kf L₀
  haveI hnfLk : NumberField ↥Lk := NumberField.of_module_finite k ↥Lk
  -- ## the level `L = K⟮ζ⟯` over `K`, with the same underlying field as `Lk`
  let L : IntermediateField K Ω := IntermediateField.adjoin K ({ζ} : Set Ω)
  have hLrestrict : L.restrictScalars k = Lk := by
    show (IntermediateField.adjoin K ({ζ} : Set Ω)).restrictScalars k = Kf ⊔ L₀
    rw [IntermediateField.restrictScalars_adjoin_of_algEquiv (F := k)
        (AlgHom.equivFieldRange (IsScalarTower.toAlgHom k K Ω)) (by ext x; rfl) ({ζ} : Set Ω),
      IntermediateField.restrictScalars_adjoin_eq_sup (F := k) Kf ({ζ} : Set Ω)]
  have eL : ↥Lk ≃ₐ[k] ↥L := (IntermediateField.equivOfEq hLrestrict).symm
  haveI hgalL : IsGalois k ↥L := IsGalois.of_algEquiv eL
  haveI hfdL : FiniteDimensional k ↥L := LinearEquiv.finiteDimensional eL.toLinearEquiv
  haveI hnfL : NumberField ↥L := NumberField.of_module_finite k ↥L
  haveI hcycL : IsCyclotomicExtension ({m} : Set ℕ) K ↥L :=
    Work.SSGRoute.E7cC.isCyclotomicExtension_adjoin_primitiveRoot (K := K) hζ
  haveI hgalL_K : IsGalois K ↥L := IsCyclotomicExtension.isGalois {m} K ↥L
  haveI hfdL_K : FiniteDimensional K ↥L := IsCyclotomicExtension.finiteDimensional {m} K ↥L
  -- ## a prime `q'` of `𝓞 L` above `q`
  obtain ⟨q', hq'lies⟩ :=
    Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := ↥L) q
  -- ## the residue characteristic `ℓ` of `q` divides neither `N`-free quantity: `ℓ ∤ m`
  let ℓ : ℕ := ringChar (NumberField.RingOfIntegers K ⧸ q.asIdeal)
  have hℓdvdQ : ℓ ∣ Q := by
    show ℓ ∣ Nat.card (NumberField.RingOfIntegers K ⧸ q.asIdeal)
    exact ringChar.dvd (by rw [Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _)
  have hℓ1 : ℓ ≠ 1 := by
    intro h
    have h1 : ((1 : ℕ) : (NumberField.RingOfIntegers K ⧸ q.asIdeal)) = 0 :=
      (ringChar.spec (NumberField.RingOfIntegers K ⧸ q.asIdeal) 1).mpr (by rw [← h])
    rw [Nat.cast_one] at h1
    exact one_ne_zero h1
  have hℓm : ¬ ℓ ∣ m := by
    intro hdiv
    have hqd : ℓ ∣ Q ^ N := dvd_pow hℓdvdQ hN
    have h2 : ℓ ∣ Q ^ N - (Q ^ N - 1) := Nat.dvd_sub hqd hdiv
    rw [Nat.sub_sub_self (Nat.one_le_pow N Q (by omega))] at h2
    exact hℓ1 (Nat.dvd_one.mp h2)
  have hmp : ((m : ℕ) : NumberField.RingOfIntegers K) ∉ q.asIdeal := by
    intro hmem
    have h2 : ((m : ℕ) : NumberField.RingOfIntegers K ⧸ q.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk q.asIdeal) m]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    exact hℓm (ringChar.dvd h2)
  -- ## `q` is unramified in `L / K`: `L / K = K(ζ_m) / K` with `ℓ ∤ m`
  have hunr : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := ↥L) q :=
    NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (k := K) (Ω := ↥L) m q hmp
  have he : q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := hunr q' hq'lies
  -- ## the residue field `κ` of `L` at `q'` and the reduction of `ζ`
  let κ := NK.CFTLib.IdeleHasse.Descent.ResidueFieldOf ↥L q'
  have hdvdP : ∀ n : ℕ, (n : NumberField.RingOfIntegers ↥L) ∈ q'.asIdeal → ℓ ∣ n := by
    intro n hn
    have h1 : (n : NumberField.RingOfIntegers K) ∈
        q'.asIdeal.under (NumberField.RingOfIntegers K) := by
      rw [Ideal.mem_under, map_natCast]; exact hn
    rw [← hq'lies.over] at h1
    have h2 : ((n : ℕ) : NumberField.RingOfIntegers K ⧸ q.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk q.asIdeal) n]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h1
    exact ringChar.dvd h2
  let ζL : ↥L := ⟨ζ, IntermediateField.mem_adjoin_simple_self K ζ⟩
  have hζL : IsPrimitiveRoot ζL m := by
    exact IsPrimitiveRoot.coe_submonoidClass_iff.mp (by
      rw [show ((ζL : ↥L) : Ω) = ζ from rfl]; exact hζ)
  have hint : IsIntegral ℤ ζL := hζL.isIntegral hmpos
  obtain ⟨ζO, hζOeq⟩ := (IsIntegralClosure.isIntegral_iff
    (A := NumberField.RingOfIntegers ↥L) (R := ℤ) (B := ↥L)).mp hint
  have hζO : IsPrimitiveRoot ζO m := by
    have h1 : IsPrimitiveRoot ((ζO : ↥L)) m := by
      rw [show ((ζO : ↥L)) = ζL from hζOeq]; exact hζL
    exact IsPrimitiveRoot.coe_submonoidClass_iff.mp h1
  have hpri : IsPrimitiveRoot (Ideal.Quotient.mk q'.asIdeal ζO : κ) m :=
    Work.SSGRoute.isPrimitiveRoot_quotient_mk q'.asIdeal hmpos hdvdP hℓm hζO
  -- ## `m ∣ #κ - 1`
  have hm_dvd : m ∣ Nat.card κ - 1 := by
    have hη0 : (Ideal.Quotient.mk q'.asIdeal ζO : κ) ≠ 0 := by
      intro h0
      have h1 := hpri.1
      rw [h0, zero_pow hmpos.ne'] at h1
      exact one_ne_zero h1.symm
    let u : κˣ := Units.mk0 _ hη0
    have hu : (u : κ) = (Ideal.Quotient.mk q'.asIdeal ζO : κ) := rfl
    have huo : orderOf u = m := by
      rw [← orderOf_units, hu]; exact hpri.eq_orderOf.symm
    have h := orderOf_dvd_natCard u
    rwa [huo, Nat.card_units] at h
  have hQcard : Nat.card κ = Q ^ q'.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
    have h := Commons.NumberTheory.NumberField.natCard_residue_eq_pow_inertiaDeg q q' hq'lies
    rwa [show Nat.card (NumberField.RingOfIntegers K ⧸ q.asIdeal) = Q from rfl] at h
  -- ## the residue degree `f = f(q'/q)` is divisible by `N`
  have hNdvdf : N ∣ q'.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
    refine Work.SSGRoute.dvd_of_pow_sub_one_dvd_pow_sub_one Q N
      (q'.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) hQ2 (Nat.pos_of_ne_zero hN) ?_
    rw [← hQcard]; exact hm_dvd
  exact ⟨L, hnfL, hfdL, hgalL, q', hq'lies, he, hNdvdf⟩

end Work.SSGRoute.PT.G1plusOwn
