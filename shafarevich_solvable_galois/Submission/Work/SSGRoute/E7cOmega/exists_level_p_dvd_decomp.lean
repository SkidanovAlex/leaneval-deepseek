import Mathlib
import Submission.Work.SSGRoute.exists_galois_level_p_dvd
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.exists_level_residueDeg
import Submission.Work.SSGRoute.isPrimitiveRoot_quotient_mk
import Submission.Commons.NumberTheory.NumberField.orderOf_frobenius_eq_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
import Submission.Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum
import Submission.Commons.NumberTheory.NumberField.perfectField_residueField_heightOneSpectrum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A `k`-level at which a prescribed place has `p`-divisible stabilizer

Given a finite place `w` of a number field `K` above a finite place `Q` of the base number field
`k`, we produce a finite Galois level `L ⊆ Ω` of `K` over `k`, together with a place `q'` of `L`
lying over `w`, whose decomposition group `Stab_{Gal(L/k)}(q')` has order divisible by `p`.

The construction is cyclotomic: writing `q₀` for the cardinality of the residue field of `k` at
`Q` and `m = q₀ ^ p - 1`, we take `L` to be the compositum of `K` with the field `L₀ ⊆ Ω`
generated over `k` by all `m`-th roots of unity.  As `L₀` is the splitting field of `X ^ m - 1`
over `k` it is finite Galois over `k`, and `L = K · L₀` is finite Galois over `k` as well.

At any prime `P` of `𝓞 L` above `Q` the reduction of a primitive `m`-th root of unity `ζ ∈ L` is
again primitive (`Work.SSGRoute.isPrimitiveRoot_quotient_mk`), so `m = q₀ ^ p - 1` divides
`#(𝓞 L ⧸ P) - 1 = q₀ ^ f - 1`, where `f` is the residue degree of `P` over `Q`; hence `p ∣ f`.
Finally `f ∣ e · f` is the order of the decomposition group of `P` in `Gal(L/k)`
(Mathlib's `Ideal.card_stabilizer_eq`), and the stabilizer of the place `Place.ofFinite P` is the
stabilizer of the prime `P`.
-/

open scoped NumberField Pointwise

namespace Work.SSGRoute.E7cOmega

set_option maxHeartbeats 1000000

theorem exists_level_p_dvd_decomp (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (w : NK.GlobalCFT.Place K)
    (hw : ∃ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      w = NK.GlobalCFT.Place.ofFinite q) :
    ∃ (L : IntermediateField K Ω), ∃ (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
      (_ : IsGalois k ↥L), ∃ (q' : NK.GlobalCFT.Place ↥L),
        NK.GlobalCFT.Place.LiesOver q' w ∧
        p ∣ Nat.card (MulAction.stabilizer (↥L ≃ₐ[k] ↥L) q') := by
  classical
  obtain ⟨q, rfl⟩ := hw
  haveI hp : p.Prime := Fact.out
  haveI hΩchar : CharZero Ω :=
    charZero_of_injective_algebraMap (RingHom.injective (algebraMap k Ω))
  -- ## The prime `Q` of `𝓞 k` below `q`
  let Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
    ⟨q.asIdeal.under (NumberField.RingOfIntegers k), inferInstance,
      Ideal.under_ne_bot _ q.ne_bot⟩
  have hQlies : q.asIdeal.LiesOver Q.asIdeal := Ideal.over_under q.asIdeal
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
  -- ## The levels `L₀ = k⟮μ_m⟯` and `L_k = K · L₀`
  let Kf : IntermediateField k Ω := (IsScalarTower.toAlgHom k K Ω).fieldRange
  let L₀ : IntermediateField k Ω :=
    IntermediateField.adjoin k ((Polynomial.X ^ m - 1 : Polynomial k).rootSet Ω)
  let Lk : IntermediateField k Ω := Kf ⊔ L₀
  haveI hfdKf : FiniteDimensional k Kf :=
    LinearEquiv.finiteDimensional
      (AlgHom.equivFieldRange (IsScalarTower.toAlgHom k K Ω)).toLinearEquiv
  haveI hgalKf : IsGalois k Kf :=
    IsGalois.of_algEquiv (AlgHom.equivFieldRange (IsScalarTower.toAlgHom k K Ω))
  have hsplitΩ : ((Polynomial.X ^ m - 1 : Polynomial k).map (algebraMap k Ω)).Splits := by
    have h1 : (Polynomial.X ^ m - 1 : Polynomial Ω).Splits :=
      Polynomial.X_pow_sub_one_splits hζ₀
    simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
      using h1
  haveI hsplitField : Polynomial.IsSplittingField k L₀ (Polynomial.X ^ m - 1) :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplitΩ
  haveI hfdL₀ : FiniteDimensional k L₀ :=
    Polynomial.IsSplittingField.finiteDimensional L₀ (Polynomial.X ^ m - 1)
  haveI hnormL₀ : Normal k L₀ := Normal.of_isSplittingField (Polynomial.X ^ m - 1)
  haveI hgalL₀ : IsGalois k L₀ := IsGalois.of_separable_splitting_field
    (p := (Polynomial.X ^ m - 1 : Polynomial k))
    (by rw [Polynomial.X_pow_sub_one_separable_iff]; exact Nat.cast_ne_zero.mpr hmpos.ne')
  haveI hfdLk : FiniteDimensional k Lk := IntermediateField.finiteDimensional_sup Kf L₀
  haveI hgalLk : IsGalois k Lk := inferInstance
  haveI hnfLk : NumberField ↥Lk := NumberField.of_module_finite k ↥Lk
  -- ## The level `L` over `K` with the same underlying field
  let L : IntermediateField K Ω :=
    Lk.toSubfield.toIntermediateField (fun x => by
      have hx : algebraMap K Ω x ∈ Kf := by
        have h1 : algebraMap K Ω x
            = (((IsScalarTower.toAlgHom k K Ω).equivFieldRange x : ↥Kf) : Ω) := by
          rw [AlgHom.equivFieldRange_apply_coe, IsScalarTower.toAlgHom_apply]
        rw [h1]
        exact ((IsScalarTower.toAlgHom k K Ω).equivFieldRange x).2
      exact (show Kf ≤ Lk from le_sup_left) hx)
  have hLrestrict : L.restrictScalars k = Lk := by
    ext x; exact Iff.rfl
  have eL : ↥Lk ≃ₐ[k] ↥L := (IntermediateField.equivOfEq hLrestrict).symm
  haveI hfdL : FiniteDimensional k ↥L := LinearEquiv.finiteDimensional eL.toLinearEquiv
  haveI hgalL : IsGalois k ↥L := IsGalois.of_algEquiv eL
  haveI hnfL : NumberField ↥L := NumberField.of_module_finite k ↥L
  -- ## A prime `P` of `𝓞 L` over `q`
  obtain ⟨P, hPlies⟩ :=
    Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := ↥L) q
  have hPoverQ : P.asIdeal.LiesOver Q.asIdeal := Ideal.LiesOver.trans P.asIdeal q.asIdeal Q.asIdeal
  haveI hPmax : P.asIdeal.IsMaximal := inferInstance
  haveI hPprime : P.asIdeal.IsPrime := inferInstance
  haveI hFinP : Finite (NumberField.RingOfIntegers ↥L ⧸ P.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum P
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
  have hunder : P.asIdeal.under (NumberField.RingOfIntegers k) = Q.asIdeal := hPoverQ.over.symm
  have hdvdP : ∀ n : ℕ, (n : NumberField.RingOfIntegers ↥L) ∈ P.asIdeal → ℓ ∣ n := by
    intro n hn
    have h1 : (n : NumberField.RingOfIntegers k) ∈ P.asIdeal.under (NumberField.RingOfIntegers k) := by
      rw [Ideal.mem_under, map_natCast]
      exact hn
    rw [hunder] at h1
    have h2 : ((n : ℕ) : NumberField.RingOfIntegers k ⧸ Q.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk Q.asIdeal) n]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h1
    exact ringChar.dvd h2
  -- ## The reduction of `ζ₀` mod `P` is primitive of order `m`
  haveI hfieldP : Field (NumberField.RingOfIntegers ↥L ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  have hζroot : ζ₀ ∈ (Polynomial.X ^ m - 1 : Polynomial k).rootSet Ω := by
    rw [Polynomial.mem_rootSet']
    refine ⟨?_, ?_⟩
    · rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
      exact Polynomial.X_pow_sub_C_ne_zero hmpos (1 : Ω)
    · rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_one, hζ₀.pow_eq_one, sub_self]
  have hζ_Lk : ζ₀ ∈ Lk :=
    (le_sup_right : L₀ ≤ Lk) (IntermediateField.subset_adjoin k _ hζroot)
  have hζL : IsPrimitiveRoot (⟨ζ₀, hζ_Lk⟩ : ↥L) m :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp (by
      rw [show ((⟨ζ₀, hζ_Lk⟩ : ↥L) : Ω) = ζ₀ from rfl]
      exact hζ₀)
  have hint : IsIntegral ℤ (⟨ζ₀, hζ_Lk⟩ : ↥L) := hζL.isIntegral hmpos
  obtain ⟨ζO, hζOeq⟩ :=
    (IsIntegralClosure.isIntegral_iff (A := NumberField.RingOfIntegers ↥L) (R := ℤ) (B := ↥L)).mp hint
  have hζO : IsPrimitiveRoot ζO m := by
    have h1 : IsPrimitiveRoot ((ζO : ↥L)) m := by
      rw [show ((ζO : ↥L)) = (⟨ζ₀, hζ_Lk⟩ : ↥L) from hζOeq]
      exact hζL
    exact IsPrimitiveRoot.coe_submonoidClass_iff.mp h1
  have hpri : IsPrimitiveRoot
      (Ideal.Quotient.mk P.asIdeal ζO : NumberField.RingOfIntegers ↥L ⧸ P.asIdeal) m :=
    Work.SSGRoute.isPrimitiveRoot_quotient_mk P.asIdeal hmpos hdvdP hℓm hζO
  -- ## `m ∣ #(𝓞 L ⧸ P) - 1`
  have hm_dvd : m ∣ Nat.card (NumberField.RingOfIntegers ↥L ⧸ P.asIdeal) - 1 := by
    haveI hfinκ : Finite (NK.CFTLib.IdeleHasse.Descent.ResidueFieldOf ↥L P) := hFinP
    haveI hftκ : Fintype (NK.CFTLib.IdeleHasse.Descent.ResidueFieldOf ↥L P) := Fintype.ofFinite _
    let ζbar : NK.CFTLib.IdeleHasse.Descent.ResidueFieldOf ↥L P := Ideal.Quotient.mk P.asIdeal ζO
    have hζbar : IsPrimitiveRoot ζbar m := hpri
    have hζbar0 : ζbar ≠ 0 := by
      intro h0
      have h1 := hζbar.1
      rw [h0, zero_pow hmpos.ne'] at h1
      exact one_ne_zero h1.symm
    let u : (NK.CFTLib.IdeleHasse.Descent.ResidueFieldOf ↥L P)ˣ := Units.mk0 ζbar hζbar0
    have hu : (u : NK.CFTLib.IdeleHasse.Descent.ResidueFieldOf ↥L P) = ζbar := rfl
    have huo : orderOf u = m := by
      rw [← orderOf_units, hu]
      exact hζbar.eq_orderOf.symm
    have h := orderOf_dvd_natCard u
    rw [huo, Nat.card_units] at h
    exact h
  -- ## The residue degree `f = [κ(P) : κ(Q)]` is divisible by `p`
  have hNcard : Nat.card (NumberField.RingOfIntegers ↥L ⧸ P.asIdeal)
      = q₀ ^ P.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
    have h := Commons.NumberTheory.NumberField.natCard_residue_eq_pow_inertiaDeg Q P hPoverQ
    rwa [show Nat.card (NumberField.RingOfIntegers k ⧸ Q.asIdeal) = q₀ from rfl] at h
  have hpdvdf : p ∣ P.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
    refine Work.SSGRoute.dvd_of_pow_sub_one_dvd_pow_sub_one q₀ p
      (P.asIdeal.inertiaDeg (NumberField.RingOfIntegers k)) hq₀2 hp.pos ?_
    rw [← hNcard]
    exact hm_dvd
  -- ## The stabilizer of the place `Place.ofFinite P` has order divisible by `p`
  have hdvdfIn : p ∣ Q.asIdeal.inertiaDegIn (NumberField.RingOfIntegers ↥L) := by
    rw [Ideal.inertiaDegIn_eq_inertiaDeg Q.asIdeal P.asIdeal (↥L ≃ₐ[k] ↥L)]
    exact hpdvdf
  have hcard : Nat.card (MulAction.stabilizer (↥L ≃ₐ[k] ↥L) P.asIdeal)
      = Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers ↥L)
        * Q.asIdeal.inertiaDegIn (NumberField.RingOfIntegers ↥L) :=
    Ideal.card_stabilizer_eq Q.asIdeal P.asIdeal
  have hpstab : p ∣ Nat.card (MulAction.stabilizer (↥L ≃ₐ[k] ↥L) P.asIdeal) := by
    rw [hcard]
    exact dvd_mul_of_dvd_right hdvdfIn _
  have hplace : MulAction.stabilizer (↥L ≃ₐ[k] ↥L) (NK.GlobalCFT.Place.ofFinite P)
      = MulAction.stabilizer (↥L ≃ₐ[k] ↥L) P.asIdeal := by
    ext σ
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
      NK.GlobalCFT.Place.smul_ofFinite, NK.GlobalCFT.Place.ofFinite_inj,
      IsDedekindDomain.HeightOneSpectrum.ext_iff,
      NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal]
    rw [Ideal.pointwise_smul_def]
    exact Iff.rfl
  exact ⟨L, hnfL, hfdL, hgalL, NK.GlobalCFT.Place.ofFinite P,
    NK.GlobalCFT.Place.liesOver_ofFinite hPlies, by rw [hplace]; exact hpstab⟩

end Work.SSGRoute.E7cOmega
