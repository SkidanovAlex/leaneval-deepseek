import Mathlib
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum
import Submission.Commons.NumberTheory.NumberField.exists_frobenius_galRestrict
import Submission.Commons.NumberTheory.NumberField.orderOf_frobenius_eq_inertiaDeg
import Submission.Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.frobenius_eq_of_commute

open scoped IntermediateField NumberField
open IsDedekindDomain.HeightOneSpectrum

set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.NumberField.Completion

/-- Arithmetic: `q^n - 1` divides `q^k - 1` exactly when `n` divides `k`. -/
lemma dvd_pow_sub_one_iff {q n k : ℕ} (hq : 2 ≤ q) (hn : 0 < n) :
    q ^ n - 1 ∣ q ^ k - 1 ↔ n ∣ k := by
  have h1q : 1 ≤ q := by omega
  refine ⟨fun h => ?_, fun h => Nat.pow_sub_one_dvd_pow_sub_one q h⟩
  set r := k % n with hr
  have hrlt : r < n := Nat.mod_lt k hn
  have hk : n * (k / n) + r = k := by rw [hr]; exact Nat.div_add_mod k n
  set N := n * (k / n) with hN
  have hNk : N + r = k := hk
  have hpow : q ^ k = q ^ N * q ^ r := by rw [← hNk, pow_add]
  have hdN : q ^ n - 1 ∣ q ^ N - 1 :=
    Nat.pow_sub_one_dvd_pow_sub_one q (by rw [hN]; exact dvd_mul_right n (k / n))
  have hNle : N ≤ k := by rw [hN]; exact Nat.mul_div_le k n
  have hdNr : q ^ n - 1 ∣ q ^ N * (q ^ r - 1) := by
    have hEq : q ^ N * (q ^ r - 1) = (q ^ k - 1) - (q ^ N - 1) := by
      have hle : q ^ N ≤ q ^ k := Nat.pow_le_pow_right (by omega) hNle
      have hle1 : 1 ≤ q ^ N := Nat.one_le_pow N q (by omega)
      have hle2 : 1 ≤ q ^ k := Nat.one_le_pow k q (by omega)
      have hA : q ^ N * (q ^ r - 1) = q ^ k - q ^ N := by
        rw [Nat.mul_sub_left_distrib, mul_one, ← hpow]
      have hB : (q ^ k - 1) - (q ^ N - 1) = q ^ k - q ^ N := by omega
      rw [hA, hB]
    rw [hEq]
    exact Nat.dvd_sub h hdN
  have h3 : q ^ n - 1 ∣ q ^ r - 1 := by
    have hkey : q ^ N * (q ^ r - 1) - (q ^ N - 1) * (q ^ r - 1) = q ^ r - 1 := by
      rw [Nat.sub_mul, one_mul]
      exact Nat.sub_sub_self (Nat.le_mul_of_pos_left (q ^ r - 1) (pow_pos (by omega) N))
    rw [← hkey]
    exact Nat.dvd_sub hdNr (Dvd.dvd.mul_right hdN _)
  have hlt : q ^ r - 1 < q ^ n - 1 :=
    Nat.sub_lt_sub_right (Nat.one_le_pow r q (by omega))
      (Nat.pow_lt_pow_right (by omega) hrlt)
  have hzero : q ^ r - 1 = 0 := Nat.eq_zero_of_dvd_of_lt h3 hlt
  have hr0 : r = 0 := by
    have hqr : q ^ r = 1 :=
      le_antisymm (Nat.sub_eq_zero_iff_le.mp hzero) (Nat.one_le_pow r q (by omega))
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exact h0
    · exfalso
      have h2 : 2 ≤ q ^ r := by
        calc 2 ≤ q := hq
          _ = q ^ 1 := (pow_one q).symm
          _ ≤ q ^ r := Nat.pow_le_pow_right (by omega) h0
      rw [hqr] at h2
      exact absurd h2 (by norm_num)
  rw [← hNk, hr0, add_zero]
  exact dvd_mul_right n (k / n)

/-- In a number field, a root of unity of order dividing `N` which is congruent to `1` modulo a
prime `P` with `N ∉ P` is `1`. -/
lemma eq_one_of_pow_eq_one_of_sub_mem {K : Type} [Field K] [NumberField K] {P : Ideal (𝓞 K)}
    {N : ℕ} {η : 𝓞 K} (hη : η ^ N = 1) (hsub : η - 1 ∈ P)
    (hN : ((N : ℕ) : 𝓞 K) ∉ P) : η = 1 := by
  by_contra hne
  obtain ⟨c, hc⟩ := sub_one_dvd_natCast_of_pow_eq_one hη hne
  exact hN (hc ▸ Ideal.mul_mem_right c P hsub)

/-- In a number field, two roots of unity of order dividing `N` which are congruent modulo a prime
`P` with `N ∉ P` are equal. -/
lemma eq_of_sub_mem_of_pow_eq_one {K : Type} [Field K] [NumberField K] {P : Ideal (𝓞 K)}
    {N : ℕ} {θ η : 𝓞 K} (hθ : θ ^ N = 1) (hη : η ^ N = 1) (hsub : θ - η ∈ P)
    (hN : ((N : ℕ) : 𝓞 K) ∉ P) : θ = η := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · exfalso
    refine hN ?_
    rw [hN0, Nat.cast_zero]
    exact P.zero_mem
  have hN1 : 1 ≤ N := hNpos
  have hζ : θ * η ^ N = θ := by rw [hη, mul_one]
  have hζ1 : (θ * η ^ (N - 1)) ^ N = 1 := by
    rw [mul_pow, hθ, one_mul, ← pow_mul, mul_comm, pow_mul, hη, one_pow]
  have hsub' : θ * η ^ (N - 1) - 1 ∈ P := by
    have hEq : θ * η ^ (N - 1) - 1 = (θ - η) * η ^ (N - 1) := by
      have h2 : (θ - η) * η ^ (N - 1) = θ * η ^ (N - 1) - η ^ N := by
        rw [sub_mul, ← pow_succ', Nat.sub_add_cancel hN1]
      rw [h2, hη]
    rw [hEq]
    exact Ideal.mul_mem_right _ _ hsub
  have hone : θ * η ^ (N - 1) = 1 := eq_one_of_pow_eq_one_of_sub_mem hζ1 hsub' hN
  calc θ = θ * η ^ N := hζ.symm
    _ = θ * η ^ (N - 1) * η := by rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hN1]
    _ = η := by rw [hone, one_mul]

/-- The cardinality of the residue field of a finite place lies in the place. -/
lemma natCard_residueField_mem {L : Type} [Field L] [NumberField L]
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    ((Nat.card (𝓞 L ⧸ q.asIdeal) : ℕ) : 𝓞 L) ∈ q.asIdeal := by
  haveI hfin : Finite (𝓞 L ⧸ q.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum q
  haveI hft : Fintype (𝓞 L ⧸ q.asIdeal) := Fintype.ofFinite (𝓞 L ⧸ q.asIdeal)
  letI : Field (𝓞 L ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rw [map_natCast]
  have h := FiniteField.cast_card_eq_zero (𝓞 L ⧸ q.asIdeal)
  rw [Nat.card_eq_fintype_card]
  exact h

theorem exists_galois_unramified_extension_tower
    {L : Type} [Field L] [NumberField L] {L' : Type} [Field L'] [NumberField L']
    [Algebra L L'] [FiniteDimensional L L'] [IsGalois L L']
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L'))
    (hq : q'.asIdeal.LiesOver q.asIdeal) (n : ℕ) (hn : 0 < n) :
    ∃ (L'' : Type) (_ : Field L'') (_ : NumberField L'') (_ : Algebra L L'')
      (_ : Algebra L' L'') (_ : IsScalarTower L L' L'') (_ : FiniteDimensional L L'')
      (_ : IsGalois L L'') (_ : IsGalois L' L'')
      (q'' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L'')),
      q''.asIdeal.LiesOver q'.asIdeal ∧
      q''.asIdeal.ramificationIdx (NumberField.RingOfIntegers L') = 1 ∧
      q''.asIdeal.inertiaDeg (NumberField.RingOfIntegers L') = n := by
  classical
  -- ============ Step 0: the numerical data ============
  haveI hfin : Finite (NumberField.RingOfIntegers L' ⧸ q'.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum q'
  haveI hfint : Fintype (NumberField.RingOfIntegers L' ⧸ q'.asIdeal) := Fintype.ofFinite _
  set qN : ℕ := Nat.card (NumberField.RingOfIntegers L' ⧸ q'.asIdeal) with hqN
  have hqN2 : 2 ≤ qN := by
    rw [hqN, Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  set m : ℕ := qN ^ n - 1 with hm
  have hmpos : 0 < m := by
    have h1 : 1 < qN ^ n := one_lt_pow₀ (by omega) hn.ne'
    omega
  haveI hmne : NeZero m := ⟨hmpos.ne'⟩
  -- ============ Step 1: the ambient field and the subfields ============
  let Ω := AlgebraicClosure L
  let ι : L' →ₐ[L] Ω := IsAlgClosed.lift
  have hι : Function.Injective ι := ι.toRingHom.injective
  let E1 : IntermediateField L Ω := ι.fieldRange
  let e1 : L' ≃ₐ[L] ↥E1 := AlgEquiv.ofInjective ι hι
  haveI hE1fin : FiniteDimensional L ↥E1 := LinearEquiv.finiteDimensional e1.toLinearEquiv
  haveI hE1gal : IsGalois L ↥E1 := IsGalois.of_algEquiv e1
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ m := by
    obtain ⟨ζ, hζr⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic m Ω) (by
      rw [Polynomial.degree_cyclotomic]
      simpa using (Nat.totient_pos.mpr hmpos).ne')
    exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζr⟩
  let E2 : IntermediateField L Ω := IntermediateField.adjoin L {ζ}
  haveI hE2cyc : IsCyclotomicExtension {m} L ↥E2 :=
    IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension L hζ
  haveI hE2fin : FiniteDimensional L ↥E2 := by
    refine IntermediateField.adjoin.finiteDimensional ?_
    exact ⟨Polynomial.X ^ m - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hmpos.ne',
      by simpa [sub_eq_zero] using hζ.pow_eq_one⟩
  haveI hE2gal : IsGalois L ↥E2 := IsCyclotomicExtension.isGalois {m} L ↥E2
  let L'' : IntermediateField L Ω := E1 ⊔ E2
  haveI hgalL : IsGalois L ↥L'' := ⟨⟩
  haveI hfinL : FiniteDimensional L ↥L'' := IntermediateField.finiteDimensional_sup E1 E2
  haveI hnf : NumberField ↥L'' :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := L) (K' := Ω) L''
  -- ============ Step 2: the algebra structure over L' ============
  have hE1le : E1 ≤ L'' := le_sup_left
  let φ : L' →ₐ[L] ↥L'' := (IntermediateField.inclusion hE1le).comp e1.toAlgHom
  letI : Algebra L' ↥L'' := φ.toRingHom.toAlgebra
  haveI hST : IsScalarTower L L' ↥L'' := IsScalarTower.of_algebraMap_eq (fun x => by
    change (algebraMap L ↥L'') x = φ (algebraMap L L' x)
    rw [show φ (algebraMap L L' x) =
        (IntermediateField.inclusion hE1le) (e1 (algebraMap L L' x)) from rfl, e1.commutes x]
    exact ((IntermediateField.inclusion hE1le).commutes x).symm)
  haveI hgalL' : IsGalois L' ↥L'' := IsGalois.tower_top_of_isGalois L L' ↥L''
  haveI hfinL' : FiniteDimensional L' ↥L'' := FiniteDimensional.right L L' ↥L''
  -- ============ Step 3: the prime q'' over q' ============
  obtain ⟨q'', hq''⟩ :=
    Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := L') (L := ↥L'') q'
  -- ============ Step 4: the primitive root of unity as an integral element ============
  have hxζmem : ζ ∈ (L'' : Set Ω) :=
    (SetLike.coe_subset_coe.mpr le_sup_right)
      (IntermediateField.subset_adjoin L ({ζ} : Set Ω) (Set.mem_singleton ζ))
  let xζ : ↥L'' := ⟨ζ, hxζmem⟩
  have hxζcoe : (xζ : Ω) = ζ := rfl
  have hxζprim : IsPrimitiveRoot xζ m := by
    refine ⟨?_, ?_⟩
    · apply Subtype.ext
      show (xζ : Ω) ^ m = 1
      rw [hxζcoe]
      exact hζ.pow_eq_one
    · intro l hl
      apply hζ.dvd_of_pow_eq_one l
      have h : ((xζ ^ l : ↥L'') : Ω) = ((1 : ↥L'') : Ω) := congrArg Subtype.val hl
      simpa [hxζcoe] using h
  have hxζm : xζ ^ m = 1 := hxζprim.pow_eq_one
  have hxζint : IsIntegral ℤ xζ :=
    ⟨Polynomial.X ^ m - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hmpos.ne',
      by
        show Polynomial.eval₂ (algebraMap ℤ ↥L'') xζ (Polynomial.X ^ m - Polynomial.C 1) = 0
        rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
          hxζm, map_one, sub_self]⟩
  obtain ⟨Θ, hΘ⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 ↥L'') (R := ℤ)
    (B := ↥L'')).mp hxζint
  have hΘm : Θ ^ m = 1 := by
    have h2 : (algebraMap (𝓞 ↥L'') ↥L'') (Θ ^ m) = (algebraMap (𝓞 ↥L'') ↥L'') 1 := by
      rw [map_pow, map_one, hΘ, hxζm]
    exact IsIntegralClosure.algebraMap_injective (𝓞 ↥L'') ℤ ↥L'' h2
  have hxζne : xζ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hmpos.ne'] at hxζm
    exact one_ne_zero hxζm.symm
  -- ============ Step 5: the faithfulness of the action on `ζ` ============
  have hfaith : ∀ σ : ↥L'' ≃ₐ[L'] ↥L'', σ xζ = xζ → σ = 1 := by
    intro σ hσζ
    have hE2le : (E2 : Set Ω) ⊆ (L'' : Set Ω) := SetLike.coe_subset_coe.mpr le_sup_right
    have hE2fix : ∀ (x : Ω) (hx : x ∈ E2), ∀ hx' : x ∈ (L'' : Set Ω),
        σ ⟨x, hx'⟩ = ⟨x, hx'⟩ := by
      intro x hx
      induction hx using IntermediateField.adjoin_induction with
      | mem y hy =>
          intro hy'
          have h1 : (⟨y, hy'⟩ : ↥L'') = xζ := by
            apply Subtype.ext
            exact Set.mem_singleton_iff.mp hy
          rw [h1, hσζ]
      | algebraMap y =>
          intro hy'
          have h1 : (⟨algebraMap L Ω y, hy'⟩ : ↥L'') = algebraMap L ↥L'' y := by
            apply Subtype.ext
            rfl
          rw [h1, IsScalarTower.algebraMap_apply L L' ↥L'', AlgEquiv.commutes]
      | add y z hy hz ihy ihz =>
          intro hy'
          rw [show (⟨y + z, hy'⟩ : ↥L'') = ⟨y, hE2le hy⟩ + ⟨z, hE2le hz⟩ from rfl,
            map_add, ihy (hE2le hy), ihz (hE2le hz)]
      | inv y hy ihy =>
          intro hy'
          rw [show (⟨y⁻¹, hy'⟩ : ↥L'') = (⟨y, hE2le hy⟩ : ↥L'')⁻¹ from rfl, map_inv₀,
            ihy (hE2le hy)]
      | mul y z hy hz ihy ihz =>
          intro hy'
          rw [show (⟨y * z, hy'⟩ : ↥L'') = ⟨y, hE2le hy⟩ * ⟨z, hE2le hz⟩ from rfl,
            map_mul, ihy (hE2le hy), ihz (hE2le hz)]
    have hmain : ∀ (x : Ω) (hx : x ∈ (E1 ⊔ E2 : IntermediateField L Ω)),
        ∀ hx' : x ∈ (L'' : Set Ω), σ ⟨x, hx'⟩ = ⟨x, hx'⟩ := by
      intro x hx
      induction hx using IntermediateField.adjoin_induction with
      | mem y hy =>
          intro hy'
          rcases hy with hy | hy
          · obtain ⟨z, rfl⟩ := (AlgHom.mem_fieldRange).mp hy
            have h1 : (⟨ι z, hy'⟩ : ↥L'') = algebraMap L' ↥L'' z := by
              apply Subtype.ext
              rfl
            rw [h1, AlgEquiv.commutes]
          · exact hE2fix y hy hy'
      | algebraMap y =>
          intro hy'
          have h1 : (⟨algebraMap L Ω y, hy'⟩ : ↥L'') = algebraMap L ↥L'' y := by
            apply Subtype.ext
            rfl
          rw [h1, IsScalarTower.algebraMap_apply L L' ↥L'', AlgEquiv.commutes]
      | add y z hy hz ihy ihz =>
          intro hy'
          rw [show (⟨y + z, hy'⟩ : ↥L'') = ⟨y, hy⟩ + ⟨z, hz⟩ from rfl,
            map_add, ihy hy, ihz hz]
      | inv y hy ihy =>
          intro hy'
          rw [show (⟨y⁻¹, hy'⟩ : ↥L'') = (⟨y, hy⟩ : ↥L'')⁻¹ from rfl, map_inv₀, ihy hy]
      | mul y z hy hz ihy ihz =>
          intro hy'
          rw [show (⟨y * z, hy'⟩ : ↥L'') = ⟨y, hy⟩ * ⟨z, hz⟩ from rfl,
            map_mul, ihy hy, ihz hz]
    ext x
    simpa using hmain (x : Ω) x.2 x.2
  -- ============ Step 6: `m` is a unit at `q''` ============
  have hqle : q'.asIdeal ≤ Ideal.comap (algebraMap (𝓞 L') (𝓞 ↥L'')) q''.asIdeal :=
    le_of_eq (Ideal.LiesOver.over (P := q''.asIdeal) (p := q'.asIdeal))
  let ψ : (𝓞 L' ⧸ q'.asIdeal) →+* (𝓞 ↥L'' ⧸ q''.asIdeal) :=
    Ideal.Quotient.lift q'.asIdeal
      ((Ideal.Quotient.mk q''.asIdeal).comp (algebraMap (𝓞 L') (𝓞 ↥L'')))
      (fun a ha => by
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact hqle ha)
  haveI : Field (𝓞 L' ⧸ q'.asIdeal) := Ideal.Quotient.field q'.asIdeal
  haveI : Field (𝓞 ↥L'' ⧸ q''.asIdeal) := Ideal.Quotient.field q''.asIdeal
  have hqNmem : ((qN : ℕ) : 𝓞 L') ∈ q'.asIdeal := by
    rw [hqN]
    exact natCard_residueField_mem q'
  have hqNzero : (Ideal.Quotient.mk q'.asIdeal ((qN : ℕ) : 𝓞 L')) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hqNmem
  have hqNzero'' : (Ideal.Quotient.mk q''.asIdeal ((qN : ℕ) : 𝓞 ↥L'')) = 0 := by
    have h := congrArg ψ hqNzero
    rw [map_zero] at h
    rw [show ψ (Ideal.Quotient.mk q'.asIdeal ((qN : ℕ) : 𝓞 L')) =
        Ideal.Quotient.mk q''.asIdeal
          (algebraMap (𝓞 L') (𝓞 ↥L'') ((qN : ℕ) : 𝓞 L')) from
      Ideal.Quotient.lift_mk q'.asIdeal _ _] at h
    rwa [map_natCast] at h
  have hmm : (Ideal.Quotient.mk q''.asIdeal ((m : ℕ) : 𝓞 ↥L'')) ≠ 0 := by
    have hm1 : m + 1 = qN ^ n := by omega
    have h1 : (Ideal.Quotient.mk q''.asIdeal ((m : ℕ) : 𝓞 ↥L'')) + 1 = 0 := by
      have hsum : ((m : ℕ) : 𝓞 ↥L'') + 1 = ((qN ^ n : ℕ) : 𝓞 ↥L'') := by
        rw [← Nat.cast_one, ← Nat.cast_add, hm1]
      have hpow : ((qN ^ n : ℕ) : 𝓞 ↥L'') = ((qN : ℕ) : 𝓞 ↥L'') ^ n := Nat.cast_pow qN n
      have h3 : Ideal.Quotient.mk q''.asIdeal (((m : ℕ) : 𝓞 ↥L'') + 1) = 0 := by
        rw [hsum, hpow, map_pow, hqNzero'', zero_pow hn.ne']
      rwa [map_add, map_one] at h3
    intro h0
    rw [h0, zero_add] at h1
    exact one_ne_zero h1
  have hm_unit : ((m : ℕ) : 𝓞 ↥L'') ∉ q''.asIdeal := by
    intro hmem
    exact hmm (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  -- ============ Step 7: `e(q''|q') = 1` ============
  have he : q''.asIdeal.ramificationIdx (𝓞 L') = 1 := by
    haveI : q''.asIdeal.LiesOver q'.asIdeal := hq''
    rw [← Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
      q'.asIdeal q''.asIdeal]
    rw [Subgroup.eq_bot_iff_forall]
    intro σ hσ
    refine hfaith σ ?_
    have hmem : σ • Θ - Θ ∈ q''.asIdeal :=
      (AddSubgroup.mem_inertia.mp (show σ ∈ (q''.asIdeal.toAddSubgroup).inertia
        (↥L'' ≃ₐ[L'] ↥L'') from hσ)) Θ
    have hθm : (σ • Θ) ^ m = 1 := by
      have h := map_pow (MulSemiringAction.toRingHom (↥L'' ≃ₐ[L'] ↥L'') (𝓞 ↥L'') σ) Θ m
      rw [hΘm, map_one] at h
      exact h.symm
    have hσΘ : σ • Θ = Θ := eq_of_sub_mem_of_pow_eq_one hθm hΘm hmem hm_unit
    have hcoe : ((σ • Θ : 𝓞 ↥L'') : ↥L'') = σ xζ := by
      rw [Commons.NumberTheory.NumberField.FrobeniusEqOfCommute.smul_ringOfIntegers_eq_galRestrict]
      change (algebraMap (𝓞 ↥L'') ↥L'') (galRestrict (𝓞 L') L' ↥L'' (𝓞 ↥L'') σ Θ) = σ xζ
      rw [algebraMap_galRestrict_apply (𝓞 L') σ Θ]
      exact congrArg σ hΘ
    rw [← hcoe, hσΘ]
    change (algebraMap (𝓞 ↥L'') ↥L'') Θ = xζ
    exact hΘ
  -- ============ Step 8: `f(q''|q') = n` ============
  have hf : q''.asIdeal.inertiaDeg (𝓞 L') = n := by
    obtain ⟨σ, hσmap, hσres⟩ :=
      Commons.NumberTheory.NumberField.exists_frobenius_galRestrict (K := L') (L := ↥L'') q' q'' hq''
    have hresΘ : (Ideal.Quotient.mk q''.asIdeal
          (galRestrict (𝓞 L') L' ↥L'' (𝓞 ↥L'') σ Θ)) =
        (Ideal.Quotient.mk q''.asIdeal Θ) ^ qN := by
      have h := hσres Θ
      rwa [← hqN] at h
    have hsub : galRestrict (𝓞 L') L' ↥L'' (𝓞 ↥L'') σ Θ - Θ ^ qN ∈ q''.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hresΘ, map_pow, sub_self]
    have hθm : (galRestrict (𝓞 L') L' ↥L'' (𝓞 ↥L'') σ Θ) ^ m = 1 := by
      have h : (σ • Θ) ^ m = 1 := by
        have h2 := map_pow (MulSemiringAction.toRingHom (↥L'' ≃ₐ[L'] ↥L'') (𝓞 ↥L'') σ) Θ m
        rw [hΘm, map_one] at h2
        exact h2.symm
      rwa [← Commons.NumberTheory.NumberField.FrobeniusEqOfCommute.smul_ringOfIntegers_eq_galRestrict]
    have hΘqm : (Θ ^ qN) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hΘm, one_pow]
    have hσΘ : galRestrict (𝓞 L') L' ↥L'' (𝓞 ↥L'') σ Θ = Θ ^ qN :=
      eq_of_sub_mem_of_pow_eq_one hθm hΘqm hsub hm_unit
    have hσxζ : σ xζ = xζ ^ qN := by
      have hcoe : ((galRestrict (𝓞 L') L' ↥L'' (𝓞 ↥L'') σ Θ : 𝓞 ↥L'') : ↥L'') = σ xζ := by
        change (algebraMap (𝓞 ↥L'') ↥L'') (galRestrict (𝓞 L') L' ↥L'' (𝓞 ↥L'') σ Θ) = σ xζ
        rw [algebraMap_galRestrict_apply (𝓞 L') σ Θ]
        exact congrArg σ hΘ
      rw [← hcoe, hσΘ]
      rw [show ((Θ ^ qN : 𝓞 ↥L'') : ↥L'') = (algebraMap (𝓞 ↥L'') ↥L'') (Θ ^ qN) from rfl,
        map_pow]
      exact congrArg (fun z => z ^ qN) hΘ
    have hpow : ∀ k : ℕ, (σ ^ k) xζ = xζ ^ (qN ^ k) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ', AlgEquiv.mul_apply, ih]
          rw [show σ (xζ ^ qN ^ k) = (σ xζ) ^ (qN ^ k) from map_pow (σ : ↥L'' →+* ↥L'') _ _]
          rw [hσxζ, ← pow_mul, ← pow_succ']
    have hord : orderOf σ = n := by
      rw [orderOf_eq_iff hn]
      refine ⟨?_, ?_⟩
      · apply hfaith (σ ^ n)
        rw [hpow n]
        rw [show qN ^ n = m + 1 by omega, pow_succ, hxζm, one_mul]
      · intro k hk hkpos hk1
        have h1 : (σ ^ k) xζ = xζ := by rw [hk1]; rfl
        rw [hpow k] at h1
        have h2 : xζ ^ (qN ^ k - 1) = 1 := by
          have hqk1 : 1 ≤ qN ^ k := Nat.one_le_pow k qN (by omega)
          have h3 : xζ ^ (qN ^ k - 1) * xζ = xζ := by
            rw [← pow_succ, Nat.sub_add_cancel hqk1]
            exact h1
          exact mul_right_cancel₀ hxζne (by rw [h3, one_mul])
        have h4 : m ∣ qN ^ k - 1 := (hxζprim.pow_eq_one_iff_dvd _).mp h2
        have h5 : n ∣ k := (dvd_pow_sub_one_iff hqN2 hn).mp h4
        obtain ⟨c, hc⟩ := h5
        rw [hc] at hk
        have hk' : n * c < n * 1 := by
          rw [mul_one]
          exact hk
        have hc1 : c < 1 := (Nat.mul_lt_mul_left hn).mp hk'
        have hcpos : 0 < c := by
          rcases Nat.eq_zero_or_pos c with h0 | h0
          · rw [hc, h0, mul_zero] at hkpos
            exact absurd hkpos (lt_irrefl 0)
          · exact h0
        omega
    rw [← Commons.NumberTheory.NumberField.orderOf_frobenius_eq_inertiaDeg
      q' q'' hq'' he σ hσmap hσres]
    exact hord
  exact ⟨↥L'', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, q'', hq'', he, hf⟩

end Commons.NumberTheory.NumberField.Completion
