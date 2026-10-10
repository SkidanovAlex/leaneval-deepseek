import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Ring.Star
import Submission.Commons.NumberTheory.NumberField.Completion.exists_galois_unramified_extension_tower

open scoped IntermediateField NumberField
open IsDedekindDomain.HeightOneSpectrum

set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.NumberField.Completion

theorem exists_galois_unramified_tower_with_subfield
    {L : Type} [Field L] [NumberField L] {L' : Type} [Field L'] [NumberField L']
    [Algebra L L'] [FiniteDimensional L L'] [IsGalois L L']
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L'))
    (hq : q'.asIdeal.LiesOver q.asIdeal) (c : ℕ) (hc : 0 < c) :
    ∃ (L'' : Type) (_ : Field L'') (_ : NumberField L'')
      (_ : Algebra L L'') (_ : Algebra L' L'') (_ : IsScalarTower L L' L'')
      (_ : FiniteDimensional L L'') (_ : FiniteDimensional L' L'')
      (_ : IsGalois L L'') (_ : IsGalois L' L'')
      (q'' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L'')),
      q''.asIdeal.LiesOver q'.asIdeal ∧
      q''.asIdeal.ramificationIdx (NumberField.RingOfIntegers L') = 1 ∧
      q''.asIdeal.inertiaDeg (NumberField.RingOfIntegers L') = c ∧
      ∃ (L₁ : Type) (_ : Field L₁) (_ : NumberField L₁)
        (_ : Algebra L L₁) (_ : FiniteDimensional L L₁) (_ : IsGalois L L₁)
        (_ : Algebra L₁ L'') (_ : IsScalarTower L L₁ L'')
        (_ : FiniteDimensional L₁ L'') (_ : IsGalois L₁ L'')
        (q₁ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₁)),
        q₁.asIdeal.LiesOver q.asIdeal ∧
        q''.asIdeal.LiesOver q₁.asIdeal ∧
        q₁.asIdeal.ramificationIdx (NumberField.RingOfIntegers L) = 1 ∧
        q₁.asIdeal.inertiaDeg (NumberField.RingOfIntegers L) =
          c * q'.asIdeal.inertiaDeg (NumberField.RingOfIntegers L) := by
  classical
  -- ============ Step 0: the numerical data ============
  haveI hfin : Finite (NumberField.RingOfIntegers L' ⧸ q'.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum q'
  haveI hfint : Fintype (NumberField.RingOfIntegers L' ⧸ q'.asIdeal) := Fintype.ofFinite _
  haveI hfinq : Finite (NumberField.RingOfIntegers L ⧸ q.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum q
  haveI hfintq : Fintype (NumberField.RingOfIntegers L ⧸ q.asIdeal) := Fintype.ofFinite _
  set qN : ℕ := Nat.card (NumberField.RingOfIntegers L' ⧸ q'.asIdeal) with hqN
  set N0 : ℕ := Nat.card (NumberField.RingOfIntegers L ⧸ q.asIdeal) with hN0
  set fdeg : ℕ := q'.asIdeal.inertiaDeg (NumberField.RingOfIntegers L) with hfdeg
  have hqNpow : qN = N0 ^ fdeg := by
    rw [hqN, hN0, hfdeg]
    exact Commons.NumberTheory.NumberField.natCard_residue_eq_pow_inertiaDeg q q' hq
  have hqN2 : 2 ≤ qN := by
    rw [hqN, Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hN02 : 2 ≤ N0 := by
    rw [hN0, Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hfdeg_pos : 0 < fdeg := by
    by_contra h
    rw [not_lt, Nat.le_zero] at h
    have h2 : N0 ^ fdeg = 1 := by rw [h, pow_zero]
    rw [hqNpow, h2] at hqN2
    omega
  have hcf : 0 < c * fdeg := Nat.mul_pos hc hfdeg_pos
  set m : ℕ := qN ^ c - 1 with hm
  have hmpos : 0 < m := by
    have h1 : 1 < qN ^ c := one_lt_pow₀ (by omega) hc.ne'
    omega
  have hmN0 : m = N0 ^ (c * fdeg) - 1 := by
    rw [hm, hqNpow, ← pow_mul, mul_comm]
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
  haveI hnf₂ : NumberField ↥E2 :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := L) (K' := Ω) E2
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
  haveI hfinL' : FiniteDimensional L' ↥L'' := Module.Finite.of_restrictScalars_finite L L' ↥L''
  -- ============ Step 2b: the algebra structure over the subfield `L₁ = L(ζ)` ============
  letI : Algebra ↥E2 ↥L'' := (IntermediateField.inclusion le_sup_right).toRingHom.toAlgebra
  haveI hST₁ : IsScalarTower L ↥E2 ↥L'' := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI hfinE2 : FiniteDimensional ↥E2 ↥L'' := Module.Finite.of_restrictScalars_finite ℚ ↥E2 ↥L''
  haveI hgalE2 : IsGalois ↥E2 ↥L'' := IsGalois.tower_top_of_isGalois L ↥E2 ↥L''
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
    have hm1 : m + 1 = qN ^ c := by omega
    have h1 : (Ideal.Quotient.mk q''.asIdeal ((m : ℕ) : 𝓞 ↥L'')) + 1 = 0 := by
      have hsum : ((m : ℕ) : 𝓞 ↥L'') + 1 = ((qN ^ c : ℕ) : 𝓞 ↥L'') := by
        rw [← Nat.cast_one, ← Nat.cast_add, hm1]
      have hpow : ((qN ^ c : ℕ) : 𝓞 ↥L'') = ((qN : ℕ) : 𝓞 ↥L'') ^ c := Nat.cast_pow qN c
      have h3 : Ideal.Quotient.mk q''.asIdeal (((m : ℕ) : 𝓞 ↥L'') + 1) = 0 := by
        rw [hsum, hpow, map_pow, hqNzero'', zero_pow hc.ne']
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
  -- ============ Step 8: `f(q''|q') = c` ============
  have hf : q''.asIdeal.inertiaDeg (𝓞 L') = c := by
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
    have hord : orderOf σ = c := by
      rw [orderOf_eq_iff hc]
      refine ⟨?_, ?_⟩
      · apply hfaith (σ ^ c)
        rw [hpow c]
        rw [show qN ^ c = m + 1 by omega, pow_succ, hxζm, one_mul]
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
        have h5 : c ∣ k := (dvd_pow_sub_one_iff hqN2 hc).mp h4
        obtain ⟨d, hd⟩ := h5
        rw [hd] at hk
        have hk' : c * d < c * 1 := by rw [mul_one]; exact hk
        have hd1 : d < 1 := (Nat.mul_lt_mul_left hc).mp hk'
        have hdpos : 0 < d := by
          rcases Nat.eq_zero_or_pos d with h0 | h0
          · rw [hd, h0, mul_zero] at hkpos
            exact absurd hkpos (lt_irrefl 0)
          · exact h0
        omega
    rw [← Commons.NumberTheory.NumberField.orderOf_frobenius_eq_inertiaDeg
      q' q'' hq'' he σ hσmap hσres]
    exact hord
  -- ============ Step 9: the subfield `L₁ = L(ζ)` and its place `q₁` ============
  have hxζmem₂ : ζ ∈ (E2 : Set Ω) :=
    IntermediateField.subset_adjoin L ({ζ} : Set Ω) (Set.mem_singleton ζ)
  let xζ₂ : ↥E2 := ⟨ζ, hxζmem₂⟩
  have hxζ₂coe : (xζ₂ : Ω) = ζ := rfl
  have hxζ₂prim : IsPrimitiveRoot xζ₂ m := by
    refine ⟨?_, ?_⟩
    · apply Subtype.ext
      show (xζ₂ : Ω) ^ m = 1
      rw [hxζ₂coe]
      exact hζ.pow_eq_one
    · intro l hl
      apply hζ.dvd_of_pow_eq_one l
      have h : ((xζ₂ ^ l : ↥E2) : Ω) = ((1 : ↥E2) : Ω) := congrArg Subtype.val hl
      simpa [hxζ₂coe] using h
  have hxζ₂m : xζ₂ ^ m = 1 := hxζ₂prim.pow_eq_one
  have hxζ₂int : IsIntegral ℤ xζ₂ :=
    ⟨Polynomial.X ^ m - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hmpos.ne',
      by
        show Polynomial.eval₂ (algebraMap ℤ ↥E2) xζ₂
          (Polynomial.X ^ m - Polynomial.C 1) = 0
        rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
          Polynomial.eval₂_C, hxζ₂m, map_one, sub_self]⟩
  obtain ⟨Θ₂, hΘ₂⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 ↥E2) (R := ℤ)
    (B := ↥E2)).mp hxζ₂int
  have hΘ₂m : Θ₂ ^ m = 1 := by
    have h2 : (algebraMap (𝓞 ↥E2) ↥E2) (Θ₂ ^ m) = (algebraMap (𝓞 ↥E2) ↥E2) 1 := by
      rw [map_pow, map_one, hΘ₂, hxζ₂m]
    exact IsIntegralClosure.algebraMap_injective (𝓞 ↥E2) ℤ ↥E2 h2
  have hxζ₂ne : xζ₂ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hmpos.ne'] at hxζ₂m
    exact one_ne_zero hxζ₂m.symm
  have hfaith₂ : ∀ σ : ↥E2 ≃ₐ[L] ↥E2, σ xζ₂ = xζ₂ → σ = 1 := by
    intro σ hσζ
    have key : ∀ (x : Ω) (hx : x ∈ (E2 : Set Ω)), ∀ hx' : x ∈ (E2 : Set Ω),
        σ ⟨x, hx'⟩ = ⟨x, hx'⟩ := by
      intro x hx
      induction hx using IntermediateField.adjoin_induction with
      | mem y hy =>
          intro hy'
          have h1 : (⟨y, hy'⟩ : ↥E2) = xζ₂ := by
            apply Subtype.ext
            exact Set.mem_singleton_iff.mp hy
          rw [h1, hσζ]
      | algebraMap y =>
          intro hy'
          have h1 : (⟨algebraMap L Ω y, hy'⟩ : ↥E2) = algebraMap L ↥E2 y := by
            apply Subtype.ext
            rfl
          rw [h1, AlgEquiv.commutes]
      | add y z hy hz ihy ihz =>
          intro hy'
          rw [show (⟨y + z, hy'⟩ : ↥E2) = ⟨y, hy⟩ + ⟨z, hz⟩ from rfl,
            map_add, ihy hy, ihz hz]
      | inv y hy ihy =>
          intro hy'
          rw [show (⟨y⁻¹, hy'⟩ : ↥E2) = (⟨y, hy⟩ : ↥E2)⁻¹ from rfl, map_inv₀, ihy hy]
      | mul y z hy hz ihy ihz =>
          intro hy'
          rw [show (⟨y * z, hy'⟩ : ↥E2) = ⟨y, hy⟩ * ⟨z, hz⟩ from rfl,
            map_mul, ihy hy, ihz hz]
    ext x
    exact congrArg Subtype.val (key (x : Ω) x.2 x.2)
  let q₁ : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥E2) :=
    ⟨q''.asIdeal.under (𝓞 ↥E2), inferInstance,
      Ideal.under_ne_bot (𝓞 ↥E2) q''.ne_bot⟩
  have hq₁over : q₁.asIdeal = q''.asIdeal.under (𝓞 ↥E2) := rfl
  have hq₁lies'' : q''.asIdeal.LiesOver q₁.asIdeal := ⟨hq₁over⟩
  have hq₁lies : q₁.asIdeal.LiesOver q.asIdeal := by
    refine ⟨?_⟩
    rw [hq₁over, Ideal.under_under]
    have h2 : q''.asIdeal.under (𝓞 L') = q'.asIdeal := hq''.over.symm
    have h3 : q'.asIdeal.under (𝓞 L) = q.asIdeal := hq.over.symm
    rw [← Ideal.under_under (A := 𝓞 L) (B := 𝓞 L') (C := 𝓞 ↥L'') q''.asIdeal, h2, h3]
  have hq₁le : q.asIdeal ≤ Ideal.comap (algebraMap (𝓞 L) (𝓞 ↥E2)) q₁.asIdeal :=
    hq₁lies.over.le
  have hqNmem₂ : ((qN : ℕ) : 𝓞 ↥E2) ∈ q₁.asIdeal := by
    have hbase : Ideal.Quotient.mk q.asIdeal ((N0 : ℕ) : 𝓞 L) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [hN0]; exact natCard_residueField_mem q)
    have hmemq : ((qN : ℕ) : 𝓞 L) ∈ q.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have hcast : ((qN : ℕ) : 𝓞 L) = ((N0 : 𝓞 L)) ^ fdeg := by
        rw [hqNpow, Nat.cast_pow]
      rw [hcast, map_pow, hbase, zero_pow hfdeg_pos.ne']
    have h := hq₁le hmemq
    rw [Ideal.mem_comap, map_natCast] at h
    exact h
  have hmm₁ : (Ideal.Quotient.mk q₁.asIdeal ((m : ℕ) : 𝓞 ↥E2)) ≠ 0 := by
    have hm1 : m + 1 = qN ^ c := by omega
    have h1 : (Ideal.Quotient.mk q₁.asIdeal ((m : ℕ) : 𝓞 ↥E2)) + 1 = 0 := by
      have hsum : ((m : ℕ) : 𝓞 ↥E2) + 1 = ((qN ^ c : ℕ) : 𝓞 ↥E2) := by
        rw [← Nat.cast_one, ← Nat.cast_add, hm1]
      have hpow : ((qN ^ c : ℕ) : 𝓞 ↥E2) = ((qN : ℕ) : 𝓞 ↥E2) ^ c := Nat.cast_pow qN c
      have h3 : Ideal.Quotient.mk q₁.asIdeal (((m : ℕ) : 𝓞 ↥E2) + 1) = 0 := by
        rw [hsum, hpow, map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr hqNmem₂,
          zero_pow hc.ne']
      rwa [map_add, map_one] at h3
    intro h0
    rw [h0, zero_add] at h1
    exact one_ne_zero h1
  have hm_unit₁ : ((m : ℕ) : 𝓞 ↥E2) ∉ q₁.asIdeal := by
    intro hmem
    exact hmm₁ (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  -- ============ Step 10: `e(q₁|q) = 1` ============
  have he₁ : q₁.asIdeal.ramificationIdx (𝓞 L) = 1 := by
    haveI hq₁liesI : q₁.asIdeal.LiesOver q.asIdeal := hq₁lies
    rw [← Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
      q.asIdeal q₁.asIdeal]
    rw [Subgroup.eq_bot_iff_forall]
    intro σ hσ
    refine hfaith₂ σ ?_
    have hmem : σ • Θ₂ - Θ₂ ∈ q₁.asIdeal :=
      (AddSubgroup.mem_inertia.mp (show σ ∈ (q₁.asIdeal.toAddSubgroup).inertia
        (↥E2 ≃ₐ[L] ↥E2) from hσ)) Θ₂
    have hθm : (σ • Θ₂) ^ m = 1 := by
      have h := map_pow (MulSemiringAction.toRingHom (↥E2 ≃ₐ[L] ↥E2) (𝓞 ↥E2) σ) Θ₂ m
      rw [hΘ₂m, map_one] at h
      exact h.symm
    have hσΘ : σ • Θ₂ = Θ₂ := eq_of_sub_mem_of_pow_eq_one hθm hΘ₂m hmem hm_unit₁
    have hcoe : ((σ • Θ₂ : 𝓞 ↥E2) : ↥E2) = σ xζ₂ := by
      rw [Commons.NumberTheory.NumberField.FrobeniusEqOfCommute.smul_ringOfIntegers_eq_galRestrict]
      change (algebraMap (𝓞 ↥E2) ↥E2) (galRestrict (𝓞 L) L ↥E2 (𝓞 ↥E2) σ Θ₂) = σ xζ₂
      rw [algebraMap_galRestrict_apply (𝓞 L) σ Θ₂]
      exact congrArg σ hΘ₂
    rw [← hcoe, hσΘ]
    change (algebraMap (𝓞 ↥E2) ↥E2) Θ₂ = xζ₂
    exact hΘ₂
  -- ============ Step 11: `f(q₁|q) = c * fdeg` ============
  have hf₁ : q₁.asIdeal.inertiaDeg (𝓞 L) = c * q'.asIdeal.inertiaDeg (𝓞 L) := by
    obtain ⟨σ, hσmap, hσres⟩ :=
      Commons.NumberTheory.NumberField.exists_frobenius_galRestrict (K := L) (L := ↥E2) q q₁ hq₁lies
    have hresΘ : (Ideal.Quotient.mk q₁.asIdeal
          (galRestrict (𝓞 L) L ↥E2 (𝓞 ↥E2) σ Θ₂)) =
        (Ideal.Quotient.mk q₁.asIdeal Θ₂) ^ N0 := by
      have h := hσres Θ₂
      rwa [← hN0] at h
    have hsub : galRestrict (𝓞 L) L ↥E2 (𝓞 ↥E2) σ Θ₂ - Θ₂ ^ N0 ∈ q₁.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hresΘ, map_pow, sub_self]
    have hθm : (galRestrict (𝓞 L) L ↥E2 (𝓞 ↥E2) σ Θ₂) ^ m = 1 := by
      have h : (σ • Θ₂) ^ m = 1 := by
        have h2 := map_pow (MulSemiringAction.toRingHom (↥E2 ≃ₐ[L] ↥E2) (𝓞 ↥E2) σ) Θ₂ m
        rw [hΘ₂m, map_one] at h2
        exact h2.symm
      rwa [← Commons.NumberTheory.NumberField.FrobeniusEqOfCommute.smul_ringOfIntegers_eq_galRestrict]
    have hΘqm : (Θ₂ ^ N0) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hΘ₂m, one_pow]
    have hσΘ : galRestrict (𝓞 L) L ↥E2 (𝓞 ↥E2) σ Θ₂ = Θ₂ ^ N0 :=
      eq_of_sub_mem_of_pow_eq_one hθm hΘqm hsub hm_unit₁
    have hσxζ : σ xζ₂ = xζ₂ ^ N0 := by
      have hcoe : ((galRestrict (𝓞 L) L ↥E2 (𝓞 ↥E2) σ Θ₂ : 𝓞 ↥E2) : ↥E2) = σ xζ₂ := by
        change (algebraMap (𝓞 ↥E2) ↥E2) (galRestrict (𝓞 L) L ↥E2 (𝓞 ↥E2) σ Θ₂) = σ xζ₂
        rw [algebraMap_galRestrict_apply (𝓞 L) σ Θ₂]
        exact congrArg σ hΘ₂
      rw [← hcoe, hσΘ]
      rw [show ((Θ₂ ^ N0 : 𝓞 ↥E2) : ↥E2) = (algebraMap (𝓞 ↥E2) ↥E2) (Θ₂ ^ N0) from rfl,
        map_pow]
      exact congrArg (fun z => z ^ N0) hΘ₂
    have hpow : ∀ k : ℕ, (σ ^ k) xζ₂ = xζ₂ ^ (N0 ^ k) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ', AlgEquiv.mul_apply, ih]
          rw [show σ (xζ₂ ^ N0 ^ k) = (σ xζ₂) ^ (N0 ^ k) from
            map_pow (σ : ↥E2 →+* ↥E2) _ _]
          rw [hσxζ, ← pow_mul, ← pow_succ']
    have hord : orderOf σ = c * fdeg := by
      rw [orderOf_eq_iff hcf]
      refine ⟨?_, ?_⟩
      · apply hfaith₂ (σ ^ (c * fdeg))
        rw [hpow (c * fdeg)]
        rw [show N0 ^ (c * fdeg) = m + 1 by omega, pow_succ, hxζ₂m, one_mul]
      · intro k hk hkpos hk1
        have h1 : (σ ^ k) xζ₂ = xζ₂ := by rw [hk1]; rfl
        rw [hpow k] at h1
        have h2 : xζ₂ ^ (N0 ^ k - 1) = 1 := by
          have hN0k1 : 1 ≤ N0 ^ k := Nat.one_le_pow k N0 (by omega)
          have h3 : xζ₂ ^ (N0 ^ k - 1) * xζ₂ = xζ₂ := by
            rw [← pow_succ, Nat.sub_add_cancel hN0k1]
            exact h1
          exact mul_right_cancel₀ hxζ₂ne (by rw [h3, one_mul])
        have h4 : m ∣ N0 ^ k - 1 := (hxζ₂prim.pow_eq_one_iff_dvd _).mp h2
        rw [hmN0] at h4
        have h5 : c * fdeg ∣ k := (dvd_pow_sub_one_iff hN02 hcf).mp h4
        obtain ⟨d, hd⟩ := h5
        rw [hd] at hk
        have hk' : (c * fdeg) * d < (c * fdeg) * 1 := by rw [mul_one]; exact hk
        have hd1 : d < 1 := (Nat.mul_lt_mul_left hcf).mp hk'
        have hdpos : 0 < d := by
          rcases Nat.eq_zero_or_pos d with h0 | h0
          · rw [hd, h0, mul_zero] at hkpos
            exact absurd hkpos (lt_irrefl 0)
          · exact h0
        omega
    rw [← Commons.NumberTheory.NumberField.orderOf_frobenius_eq_inertiaDeg
      q q₁ hq₁lies he₁ σ hσmap hσres, hord, hfdeg]
  exact ⟨↥L'', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, q'', hq'', he, hf,
    ↥E2, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, q₁, hq₁lies, hq₁lies'', he₁, hf₁⟩

end Commons.NumberTheory.NumberField.Completion
