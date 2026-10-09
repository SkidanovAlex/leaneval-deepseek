import Mathlib
import Submission.Work.SSGRoute.PT.finHalfData
import Submission.Work.SSGRoute.E7cOmega.exists_level_p_dvd_decomp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A Galois level of `p`-divisible stabilizer at a *prescribed* finite place

For a number field `k`, an algebraic closure `Ω ⊇ k`, a finite Galois level `K ≤ Ω` and a finite
place `A` of `Ω` over `k`, we produce a finite Galois level `L ≥ K` at which the *specific* place
of `𝓞 L` cut out by `A` (`PT.finQW L A hA`) has a stabilizer in `Gal(L/k)` of order divisible
by `p`.

This is the `k`-level companion of `Work.SSGRoute.E7cOmega.exists_level_p_dvd_decomp`, which
produces *some* place of a level over `K` with `p`-divisible stabilizer.  Here the level lives over
`k` directly (`L = K ⊔ k⟮μ_m⟯`) and the place is the one canonically determined by `A`, which is
what the `G1⁺` finite half (`PT.finQW`) consumes.

The construction is cyclotomic: with `q₀` the cardinality of the residue field of `k` at the prime
`Q` of `𝓞 k` below `A` and `m = q₀ ^ p - 1`, we take `L = K · k⟮μ_m⟯ ⊆ Ω`.  A primitive `m`-th
root of unity `ζ ∈ L` reduces modulo the prime `P = finQW L A hA` to a primitive `m`-th root of
unity of the residue field (`Work.SSGRoute.isPrimitiveRoot_quotient_mk`), so `m ∣ q₀ ^ f - 1` for
`f` the residue degree of `P` over `Q`; by `Work.SSGRoute.dvd_of_pow_sub_one_dvd_pow_sub_one` this
forces `p ∣ f`, and the stabilizer of `P` in `Gal(L/k)` has order
`e · f` (`Ideal.card_stabilizer_eq`), hence is divisible by `p`.
-/

namespace Work.SSGRoute.PT.G1plusOwn

open scoped NumberField Pointwise
open Work.SSGRoute.PT

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

theorem exists_level_p_dvd_stab
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    ∃ (L : IntermediateField k Ω) (_ : FiniteDimensional k L) (_ : IsGalois k L)
      (_ : NumberField L),
      K ≤ L ∧
      p ∣ Nat.card (MulAction.stabilizer (↥L ≃ₐ[k] ↥L)
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))) := by
  classical
  haveI hp : p.Prime := Fact.out
  haveI hΩchar : CharZero Ω :=
    charZero_of_injective_algebraMap (RingHom.injective (algebraMap k Ω))
  haveI hΩalg : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI hΩsep : IsSepClosed Ω := inferInstance
  haveI hnfK : NumberField ↥K := NumberField.of_module_finite k ↥K
  -- ## The prime `q` of `𝓞 K` and its trace `Q` in `𝓞 k`
  let q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) := finQW K A hA
  let Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
    ⟨q.asIdeal.under (NumberField.RingOfIntegers k), inferInstance, Ideal.under_ne_bot _ q.ne_bot⟩
  haveI hFinQ : Finite (NumberField.RingOfIntegers k ⧸ Q.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum Q
  haveI : Fintype (NumberField.RingOfIntegers k ⧸ Q.asIdeal) := Fintype.ofFinite _
  let q₀ : ℕ := Nat.card (NumberField.RingOfIntegers k ⧸ Q.asIdeal)
  have hq₀2 : 2 ≤ q₀ := by
    rw [show q₀ = Nat.card (NumberField.RingOfIntegers k ⧸ Q.asIdeal) from rfl,
      Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  -- ## The cyclotomic exponent `m = q₀ ^ p - 1` and a primitive `m`-th root of unity in `Ω`
  let m : ℕ := q₀ ^ p - 1
  have hmpos : 0 < m := by
    have h1 : 1 < q₀ ^ p := Nat.one_lt_pow hp.ne_zero (by omega)
    rw [show m = q₀ ^ p - 1 from rfl]; omega
  haveI hmne : NeZero m := ⟨hmpos.ne'⟩
  haveI hmcast : NeZero ((m : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hmpos.ne'⟩
  obtain ⟨ζ₀, hζ₀⟩ := NK.LocalAnabelian.exists_isPrimitiveRoot_of_isSepClosed (K := Ω) (n := m)
  -- ## The level `L = K · k⟮μ_m⟯`
  let L₀ : IntermediateField k Ω :=
    IntermediateField.adjoin k ((Polynomial.X ^ m - 1 : Polynomial k).rootSet Ω)
  have hsplitΩ : ((Polynomial.X ^ m - 1 : Polynomial k).map (algebraMap k Ω)).Splits := by
    have h1 : (Polynomial.X ^ m - 1 : Polynomial Ω).Splits :=
      Polynomial.X_pow_sub_one_splits hζ₀
    simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one] using h1
  haveI hsplitField : Polynomial.IsSplittingField k L₀ (Polynomial.X ^ m - 1) :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplitΩ
  haveI hfdL₀ : FiniteDimensional k L₀ :=
    Polynomial.IsSplittingField.finiteDimensional L₀ (Polynomial.X ^ m - 1)
  haveI hnormL₀ : Normal k L₀ := Normal.of_isSplittingField (Polynomial.X ^ m - 1)
  haveI hgalL₀ : IsGalois k L₀ := IsGalois.of_separable_splitting_field
    (p := (Polynomial.X ^ m - 1 : Polynomial k))
    (by rw [Polynomial.X_pow_sub_one_separable_iff]; exact Nat.cast_ne_zero.mpr hmpos.ne')
  let L : IntermediateField k Ω := K ⊔ L₀
  haveI hfdL : FiniteDimensional k L := IntermediateField.finiteDimensional_sup K L₀
  haveI hgalL : IsGalois k L := inferInstance
  haveI hnfL : NumberField ↥L := NumberField.of_module_finite k ↥L
  have hKL : K ≤ L := le_sup_left
  letI : Algebra ↥K ↥L := (IntermediateField.inclusion (le_sup_left : K ≤ L)).toAlgebra
  haveI hst1 : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hst2 : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- ## The prime `P = finQW L A hA` lies over `Q`
  have hQlies : q.asIdeal.LiesOver Q.asIdeal := Ideal.over_under q.asIdeal
  have hliesKL : (finQW L A hA).asIdeal.LiesOver (finQW K A hA).asIdeal :=
    finQW_liesOver (L := K) (L' := L) A hA hKL
  have hPoverQ : (finQW L A hA).asIdeal.LiesOver Q.asIdeal :=
    Ideal.LiesOver.trans (finQW L A hA).asIdeal (finQW K A hA).asIdeal Q.asIdeal
  -- ## The residue characteristic `ℓ` of `Q` does not divide `m`
  let ℓ : ℕ := ringChar (NumberField.RingOfIntegers k ⧸ Q.asIdeal)
  have hℓdvdq₀ : ℓ ∣ q₀ := by
    show ℓ ∣ Nat.card (NumberField.RingOfIntegers k ⧸ Q.asIdeal)
    exact ringChar.dvd (by rw [Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _)
  have hℓ1 : ℓ ≠ 1 := by
    intro h
    have h1 : ((1 : ℕ) : (NumberField.RingOfIntegers k ⧸ Q.asIdeal)) = 0 :=
      (ringChar.spec (NumberField.RingOfIntegers k ⧸ Q.asIdeal) 1).mpr (by rw [← h])
    rw [Nat.cast_one] at h1
    exact one_ne_zero h1
  have hℓm : ¬ ℓ ∣ m := by
    intro hdiv
    have hqd : ℓ ∣ q₀ ^ p := dvd_pow hℓdvdq₀ hp.ne_zero
    have h2 : ℓ ∣ q₀ ^ p - (q₀ ^ p - 1) := Nat.dvd_sub hqd hdiv
    rw [Nat.sub_sub_self (Nat.one_le_pow p q₀ (by omega))] at h2
    exact hℓ1 (Nat.dvd_one.mp h2)
  -- ## An integer in `P` is divisible by `ℓ`
  have hunder : (finQW L A hA).asIdeal.under (NumberField.RingOfIntegers k) = Q.asIdeal :=
    hPoverQ.over.symm
  have hdvdP : ∀ n : ℕ, (n : NumberField.RingOfIntegers ↥L) ∈ (finQW L A hA).asIdeal → ℓ ∣ n := by
    intro n hn
    have h1 : (n : NumberField.RingOfIntegers k) ∈
        (finQW L A hA).asIdeal.under (NumberField.RingOfIntegers k) := by
      rw [Ideal.mem_under, map_natCast]; exact hn
    rw [hunder] at h1
    have h2 : ((n : ℕ) : (NumberField.RingOfIntegers k ⧸ Q.asIdeal)) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk Q.asIdeal) n]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h1
    exact ringChar.dvd h2
  haveI hFinP : Finite (NumberField.RingOfIntegers ↥L ⧸ (finQW L A hA).asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum _
  -- ## The reduction of `ζ₀` mod `P` is primitive of order `m`
  have hζroot : ζ₀ ∈ (Polynomial.X ^ m - 1 : Polynomial k).rootSet Ω := by
    rw [Polynomial.mem_rootSet']
    refine ⟨?_, ?_⟩
    · rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
      exact Polynomial.X_pow_sub_C_ne_zero hmpos (1 : Ω)
    · rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_one, hζ₀.pow_eq_one, sub_self]
  have hζ_L : ζ₀ ∈ L := (le_sup_right : L₀ ≤ L) (IntermediateField.subset_adjoin k _ hζroot)
  have hζL : IsPrimitiveRoot (⟨ζ₀, hζ_L⟩ : ↥L) m :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp (by
      rw [show ((⟨ζ₀, hζ_L⟩ : ↥L) : Ω) = ζ₀ from rfl]
      exact hζ₀)
  have hint : IsIntegral ℤ (⟨ζ₀, hζ_L⟩ : ↥L) := hζL.isIntegral hmpos
  obtain ⟨ζO, hζOeq⟩ :=
    (IsIntegralClosure.isIntegral_iff (A := NumberField.RingOfIntegers ↥L) (R := ℤ) (B := ↥L)).mp hint
  have hζO : IsPrimitiveRoot ζO m := by
    have h1 : IsPrimitiveRoot ((ζO : ↥L)) m := by
      rw [show ((ζO : ↥L)) = (⟨ζ₀, hζ_L⟩ : ↥L) from hζOeq]
      exact hζL
    exact IsPrimitiveRoot.coe_submonoidClass_iff.mp h1
  have hpri : IsPrimitiveRoot
      (Ideal.Quotient.mk (finQW L A hA).asIdeal ζO :
        NumberField.RingOfIntegers ↥L ⧸ (finQW L A hA).asIdeal) m :=
    Work.SSGRoute.isPrimitiveRoot_quotient_mk (finQW L A hA).asIdeal hmpos hdvdP hℓm hζO
  -- ## `m ∣ #(𝓞 L ⧸ P) - 1`
  have hm_dvd : m ∣ Nat.card (NumberField.RingOfIntegers ↥L ⧸ (finQW L A hA).asIdeal) - 1 := by
    haveI hfinκ : Finite (NK.CFTLib.IdeleHasse.Descent.ResidueFieldOf ↥L (finQW L A hA)) := hFinP
    haveI hftκ : Fintype (NK.CFTLib.IdeleHasse.Descent.ResidueFieldOf ↥L (finQW L A hA)) :=
      Fintype.ofFinite _
    let ζbar : NK.CFTLib.IdeleHasse.Descent.ResidueFieldOf ↥L (finQW L A hA) :=
      Ideal.Quotient.mk (finQW L A hA).asIdeal ζO
    have hζbar : IsPrimitiveRoot ζbar m := hpri
    have hζbar0 : ζbar ≠ 0 := by
      intro h0
      have h1 := hζbar.1
      rw [h0, zero_pow hmpos.ne'] at h1
      exact one_ne_zero h1.symm
    let u : (NK.CFTLib.IdeleHasse.Descent.ResidueFieldOf ↥L (finQW L A hA))ˣ :=
      Units.mk0 ζbar hζbar0
    have hu : (u : NK.CFTLib.IdeleHasse.Descent.ResidueFieldOf ↥L (finQW L A hA)) = ζbar := rfl
    have huo : orderOf u = m := by
      rw [← orderOf_units, hu]
      exact hζbar.eq_orderOf.symm
    have h := orderOf_dvd_natCard u
    rw [huo, Nat.card_units] at h
    exact h
  -- ## The residue degree `f = [κ(P) : κ(Q)]` is divisible by `p`
  have hNcard : Nat.card (NumberField.RingOfIntegers ↥L ⧸ (finQW L A hA).asIdeal)
      = q₀ ^ (finQW L A hA).asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
    have h := Commons.NumberTheory.NumberField.natCard_residue_eq_pow_inertiaDeg Q (finQW L A hA) hPoverQ
    rwa [show Nat.card (NumberField.RingOfIntegers k ⧸ Q.asIdeal) = q₀ from rfl] at h
  have hpdvdf : p ∣ (finQW L A hA).asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
    refine Work.SSGRoute.dvd_of_pow_sub_one_dvd_pow_sub_one q₀ p
      ((finQW L A hA).asIdeal.inertiaDeg (NumberField.RingOfIntegers k)) hq₀2 hp.pos ?_
    rw [← hNcard]
    exact hm_dvd
  -- ## The stabilizer of the place `Place.ofFinite P` has order divisible by `p`
  have hdvdfIn : p ∣ Q.asIdeal.inertiaDegIn (NumberField.RingOfIntegers ↥L) := by
    rw [Ideal.inertiaDegIn_eq_inertiaDeg Q.asIdeal (finQW L A hA).asIdeal (↥L ≃ₐ[k] ↥L)]
    exact hpdvdf
  have hcard : Nat.card (MulAction.stabilizer (↥L ≃ₐ[k] ↥L) (finQW L A hA).asIdeal)
      = Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers ↥L)
        * Q.asIdeal.inertiaDegIn (NumberField.RingOfIntegers ↥L) :=
    Ideal.card_stabilizer_eq Q.asIdeal (finQW L A hA).asIdeal
  have hpstab : p ∣ Nat.card (MulAction.stabilizer (↥L ≃ₐ[k] ↥L) (finQW L A hA).asIdeal) := by
    rw [hcard]
    exact dvd_mul_of_dvd_right hdvdfIn _
  have hplace : MulAction.stabilizer (↥L ≃ₐ[k] ↥L) (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
      = MulAction.stabilizer (↥L ≃ₐ[k] ↥L) (finQW L A hA).asIdeal := by
    ext σ
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
      NK.GlobalCFT.Place.smul_ofFinite, NK.GlobalCFT.Place.ofFinite_inj,
      IsDedekindDomain.HeightOneSpectrum.ext_iff,
      NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal]
    rw [Ideal.pointwise_smul_def]
    exact Iff.rfl
  refine ⟨L, hfdL, hgalL, hnfL, hKL, ?_⟩
  rw [hplace]
  exact hpstab

end Work.SSGRoute.PT.G1plusOwn
