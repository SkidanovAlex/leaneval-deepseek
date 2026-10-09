import Mathlib
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.ValExp
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.ordAt_sum_le
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.aeval_derivative_sum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # Helper lemmas for the totally ramified different bound -/

open scoped NumberField nonZeroDivisors

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

/-- The `P`-adic order of an element of `R`, as the additive exponent of its image in the
fraction field. -/
theorem ordAt_eq_adicExp {R : Type*} {K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (v : IsDedekindDomain.HeightOneSpectrum R) (x : R) :
    ordAt v.asIdeal x = adicExp v (algebraMap R K x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ordAt_zero, adicExp_zero]
  · rw [ordAt, adicExp_algebraMap_eq_count v x hx]

/-- **The `P`-adic order of `algebraMap a` at a prime `P` over `𝔢` is `e(P/𝔢) · ord_𝔢 a`.** -/
theorem ordAt_algebraMap_eq_mul_ramificationIdx {A : Type*} {B : Type*} {K : Type*} {L : Type*}
    [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.IsTorsionFree A B] [Field K] [Field L] [Algebra K L] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    (v : IsDedekindDomain.HeightOneSpectrum A) (w : IsDedekindDomain.HeightOneSpectrum B)
    [w.asIdeal.LiesOver v.asIdeal] (x : A) :
    ordAt w.asIdeal (algebraMap A B x) = w.asIdeal.ramificationIdx A * ordAt v.asIdeal x := by
  have h1 : ((ordAt w.asIdeal (algebraMap A B x) : ℕ) : ℤ) = adicExp (K := L) w (algebraMap A L x) := by
    rw [show algebraMap A L x = algebraMap B L (algebraMap A B x) from
      IsScalarTower.algebraMap_apply A B L x]
    exact ordAt_eq_adicExp (K := L) w (algebraMap A B x)
  refine Nat.cast_injective (R := ℤ) ?_
  have h2 : adicExp (K := K) v (algebraMap A K x) = ((ordAt v.asIdeal x : ℕ) : ℤ) :=
    (ordAt_eq_adicExp (K := K) v x).symm
  rw [Nat.cast_mul, h1, adicExp_liesOver (K := K) (L := L) v w x, h2]

/-- **Counts are antitone in the inclusion of ideals**: a smaller ideal is more divisible. -/
theorem count_normalizedFactors_le_of_le {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I J : Ideal R} {P : Ideal R} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hJ : J ≠ ⊥) (h : J ≤ I) :
    (UniqueFactorizationMonoid.normalizedFactors I).count P ≤
      (UniqueFactorizationMonoid.normalizedFactors J).count P := by
  obtain ⟨K, rfl⟩ := Ideal.dvd_iff_le.mpr h
  have hI : I ≠ ⊥ := fun hI => hJ (by simp [hI])
  rcases eq_or_ne K ⊥ with hK | hK
  · exact absurd (by rw [hK, Ideal.mul_bot]) hJ
  · rw [UniqueFactorizationMonoid.normalizedFactors_mul hI hK, Multiset.count_add]
    exact Nat.le_add_right _ _

/-- The `(p)`-adic order of a natural number inside `ℤ`. -/
theorem ordAt_span_prime_int (p : ℕ) [Fact p.Prime] (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v.asIdeal = Ideal.span ({(p : ℤ)} : Set ℤ)) (n : ℕ) :
    ordAt v.asIdeal (n : ℤ) = padicValNat p n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.cast_zero, ordAt_zero, padicValNat_zero_right]
  · have key : ∀ k : ℕ, k ≤ ordAt v.asIdeal (n : ℤ) ↔ k ≤ padicValNat p n := by
      intro k
      rw [← mem_pow_iff_le_ordAt v (by exact_mod_cast hn) k, hv, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton, ← Nat.cast_pow, Int.natCast_dvd_natCast]
      exact Nat.pow_dvd_iff_le_padicValNat (Fact.out : Nat.Prime p).ne_one hn
    exact le_antisymm (key _ |>.mp le_rfl) (key _ |>.mpr le_rfl)

/-- The degree of the minimal polynomial of an integral primitive element. -/
theorem natDegree_minpoly_ringOfIntegers {F : Type*} {K : Type*} [Field F] [NumberField F]
    [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K]
    (x : NumberField.RingOfIntegers K)
    (hx : Algebra.adjoin F {algebraMap (NumberField.RingOfIntegers K) K x} = ⊤) :
    (minpoly (NumberField.RingOfIntegers F) x).natDegree = Module.finrank F K := by
  have hxint : IsIntegral (NumberField.RingOfIntegers F) x :=
    IsIntegralClosure.isIntegral (NumberField.RingOfIntegers F) K x
  have h1 : (minpoly F (algebraMap (NumberField.RingOfIntegers K) K x)).natDegree =
      Module.finrank F K :=
    (Field.primitive_element_iff_minpoly_natDegree_eq (F := F)
        (algebraMap (NumberField.RingOfIntegers K) K x)).mp
      ((IntermediateField.adjoin_eq_top_iff (S := {algebraMap (NumberField.RingOfIntegers K) K x})).mpr
        hx)
  have h2 : minpoly F (algebraMap (NumberField.RingOfIntegers K) K x) =
      (minpoly (NumberField.RingOfIntegers F) x).map (algebraMap (NumberField.RingOfIntegers F) F) :=
    minpoly.isIntegrallyClosed_eq_field_fractions F K hxint
  rw [← h1, h2, Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective _ _)]

/-- Adjoining a nonzero scalar multiple of an element generates the same field. -/
theorem adjoin_smul_eq_adjoin {F E : Type*} [Field F] [Field E] [Algebra F E] {a : F} (ha : a ≠ 0)
    {x : E} : IntermediateField.adjoin F {a • x} = IntermediateField.adjoin F {x} := by
  refine le_antisymm ?_ ?_
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz, Algebra.smul_def]
    exact mul_mem (Subalgebra.algebraMap_mem _ a) (IntermediateField.mem_adjoin_simple_self F x)
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    have h1 : a • x ∈ IntermediateField.adjoin F {a • x} :=
      IntermediateField.mem_adjoin_simple_self F (a • x)
    have hmem : (algebraMap F E) a⁻¹ * (a • x) ∈ IntermediateField.adjoin F {a • x} :=
      mul_mem (Subalgebra.algebraMap_mem _ a⁻¹) h1
    rw [← Algebra.smul_def] at hmem
    have h2 : a⁻¹ • (a • x) = x := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    rwa [h2] at hmem

/-- **A primitive element of `𝓞 K` over `F` which is a uniformiser at a given prime.**

There is `x ∈ 𝓞 K` with `F(x) = K` and `v_P(x) = 1`.  Concretely, if `x₀ ∈ 𝓞 K` generates `K`
over `F` and `π` is a uniformiser at `P`, then for `s ∈ (P ∩ 𝓞 F)²` outside a finite bad set the
element `π + s·x₀` works. -/
theorem exists_primitive_uniformizer {F : Type*} {K : Type*} [Field F] [NumberField F] [Field K]
    [NumberField K] [Algebra F K] [FiniteDimensional F K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ x : NumberField.RingOfIntegers K,
      Algebra.adjoin F {algebraMap (NumberField.RingOfIntegers K) K x} = ⊤ ∧
        v.intValuation x = WithZero.exp (-1 : ℤ) := by
  classical
  -- ### step 1: an integral primitive element `x₀` of `𝓞 K` over `F`
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F K
  have hαint : IsIntegral F α := IsIntegral.of_finite F α
  obtain ⟨c, hc⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (M := (𝓞 F)⁰) (Rₘ := F) (S := K) α hαint
  have hc0 : (c : 𝓞 F) ≠ 0 := nonZeroDivisors.coe_ne_zero c
  let x₀ : 𝓞 K := IsIntegralClosure.mk' (𝓞 K) ((c : 𝓞 F) • α) hc
  have hx₀ : algebraMap (𝓞 K) K x₀ = (c : 𝓞 F) • α :=
    IsIntegralClosure.algebraMap_mk' (𝓞 K) ((c : 𝓞 F) • α) hc
  have hcF : algebraMap (𝓞 F) F (c : 𝓞 F) ≠ 0 := fun h =>
    hc0 (IsFractionRing.injective (𝓞 F) F h)
  have hx₀prim : IntermediateField.adjoin F {algebraMap (𝓞 K) K x₀} = ⊤ := by
    have h1 : algebraMap (𝓞 K) K x₀ =
        algebraMap F K (algebraMap (𝓞 F) F (c : 𝓞 F)) * α := by
      rw [hx₀, Algebra.smul_def, IsScalarTower.algebraMap_apply (𝓞 F) F K]
    rw [h1, show algebraMap F K (algebraMap (𝓞 F) F (c : 𝓞 F)) * α =
      (algebraMap (𝓞 F) F (c : 𝓞 F)) • α from (Algebra.smul_def _ _).symm,
      adjoin_smul_eq_adjoin hcF, hα]
  have hx₀K : IntermediateField.adjoin F {algebraMap (𝓞 K) K x₀} = ⊤ := hx₀prim
  -- ### step 2: a uniformiser `π`
  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer v
  -- ### step 3: the prime `𝔢` below and elements of `𝔢²`
  set 𝔢 : IsDedekindDomain.HeightOneSpectrum (𝓞 F) := v.under (𝓞 F) with h𝔢
  haveI hliesv : v.asIdeal.LiesOver 𝔢.asIdeal := ⟨rfl⟩
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot 𝔢.ne_bot
  set s : ℤ → 𝓞 F := fun n => a ^ 2 * (n : 𝓞 F) with hs_def
  have hsmem : ∀ n : ℤ, s n ∈ 𝔢.asIdeal ^ 2 := by
    intro n
    have h2 : a * a ∈ 𝔢.asIdeal ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul ha ha
    rw [hs_def]
    exact Ideal.mul_mem_right (n : 𝓞 F) (𝔢.asIdeal ^ 2) (by simpa [pow_two] using h2)
  -- ### step 4: the pigeonhole
  have hinj2 : Function.Injective (algebraMap (𝓞 F) (𝓞 K)) := by
    intro p q hpq
    refine IsFractionRing.injective (𝓞 F) F ?_
    have h1 : algebraMap (𝓞 F) K p = algebraMap (𝓞 F) K q := by
      rw [IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K,
        IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, hpq]
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F K,
      IsScalarTower.algebraMap_apply (𝓞 F) F K] at h1
    exact (algebraMap F K).injective h1
  have hfin : Finite (IntermediateField F K) :=
    Field.finite_intermediateField_of_exists_primitive_element F K ⟨α, hα⟩
  let g : ℤ → IntermediateField F K := fun n =>
    IntermediateField.adjoin F
      {algebraMap (𝓞 K) K (π + algebraMap (𝓞 F) (𝓞 K) (s n) * x₀)}
  obtain ⟨n₁, n₂, hn₁₂, hgn⟩ := Finite.exists_ne_map_eq_of_infinite g
  have hsdiff : s n₁ - s n₂ ≠ 0 := by
    have h1 : s n₁ - s n₂ = a ^ 2 * ((n₁ - n₂ : ℤ) : 𝓞 F) := by
      rw [hs_def]; push_cast; ring
    rw [h1]
    refine mul_ne_zero (pow_ne_zero 2 ha0) ?_
    intro h
    exact hn₁₂ (sub_eq_zero.mp (Int.cast_injective (by simpa using h)))
  have hdtop : algebraMap (𝓞 K) K (π + algebraMap (𝓞 F) (𝓞 K) (s n₁) * x₀) ∈ g n₁ :=
    IntermediateField.mem_adjoin_simple_self F _
  have hdtope : algebraMap (𝓞 K) K (π + algebraMap (𝓞 F) (𝓞 K) (s n₂) * x₀) ∈ g n₁ := by
    rw [hgn]
    exact IntermediateField.mem_adjoin_simple_self F _
  have hdiffK : (π + algebraMap (𝓞 F) (𝓞 K) (s n₁) * x₀) -
      (π + algebraMap (𝓞 F) (𝓞 K) (s n₂) * x₀) =
      algebraMap (𝓞 F) (𝓞 K) (s n₁ - s n₂) * x₀ := by
    rw [map_sub]; ring
  have hdmem : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (s n₁ - s n₂)) *
      algebraMap (𝓞 K) K x₀ ∈ g n₁ := by
    have h := sub_mem hdtop hdtope
    rwa [← map_sub, hdiffK, map_mul] at h
  have hdne : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (s n₁ - s n₂)) ≠ 0 := by
    intro h
    have h1 : algebraMap (𝓞 F) (𝓞 K) (s n₁ - s n₂) = 0 := by
      apply IsFractionRing.injective (𝓞 K) K
      rw [h, map_zero]
    exact hsdiff (hinj2 (h1.trans (map_zero (algebraMap (𝓞 F) (𝓞 K))).symm))
  have hx₀mem : algebraMap (𝓞 K) K x₀ ∈ g n₁ := by
    have hpos : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (s n₁ - s n₂)) ∈ g n₁ := by
      have hmem : algebraMap F K (algebraMap (𝓞 F) F (s n₁ - s n₂)) ∈ g n₁ :=
        Subalgebra.algebraMap_mem _ _
      rwa [← IsScalarTower.algebraMap_apply (𝓞 F) F K,
        IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K] at hmem
    have h2 : algebraMap (𝓞 K) K x₀ =
        (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (s n₁ - s n₂)))⁻¹ *
          (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (s n₁ - s n₂)) *
            algebraMap (𝓞 K) K x₀) := by
      rw [← mul_assoc, inv_mul_cancel₀ hdne, one_mul]
    rw [h2]
    exact mul_mem (inv_mem hpos) hdmem
  have hgtop : g n₁ = ⊤ := by
    have hle : IntermediateField.adjoin F {algebraMap (𝓞 K) K x₀} ≤ g n₁ :=
      IntermediateField.adjoin_le_iff.mpr (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact hx₀mem)
    rw [hx₀prim] at hle
    exact top_le_iff.mp hle
  -- ### step 5: the valuation of the constructed element
  set x : 𝓞 K := π + algebraMap (𝓞 F) (𝓞 K) (s n₁) * x₀ with hx_def
  have he1 : 1 ≤ v.asIdeal.ramificationIdx (𝓞 F) :=
    Nat.one_le_iff_ne_zero.mpr (Ideal.ramificationIdx_pos (𝓞 F) v.asIdeal).ne'
  have hmem2 : algebraMap (𝓞 F) (𝓞 K) (s n₁) ∈ v.asIdeal ^ 2 := by
    rcases eq_or_ne (s n₁) 0 with h0 | h0
    · rw [h0, map_zero]; exact zero_mem _
    · have hsKne : algebraMap (𝓞 F) (𝓞 K) (s n₁) ≠ 0 := fun h =>
        h0 (hinj2 (h.trans (map_zero _).symm))
      rw [mem_pow_iff_le_ordAt v hsKne 2,
        ordAt_algebraMap_eq_mul_ramificationIdx (A := 𝓞 F) (B := 𝓞 K) (K := F) (L := K) 𝔢 v (s n₁)]
      have h2 : 2 ≤ ordAt 𝔢.asIdeal (s n₁) := by
        rw [← mem_pow_iff_le_ordAt 𝔢 h0 2]
        exact hsmem n₁
      exact le_trans h2 (le_mul_of_one_le_left (Nat.zero_le _) he1)
  have hxval2 : v.intValuation (algebraMap (𝓞 F) (𝓞 K) (s n₁) * x₀) ≤ WithZero.exp (-2 : ℤ) := by
    rw [map_mul]
    calc v.intValuation (algebraMap (𝓞 F) (𝓞 K) (s n₁)) * v.intValuation x₀
        ≤ WithZero.exp (-2 : ℤ) * 1 := mul_le_mul' (by
            exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem
              (v := v) (algebraMap (𝓞 F) (𝓞 K) (s n₁)) 2).mpr hmem2)
          (v.intValuation_le_one x₀)
      _ = WithZero.exp (-2 : ℤ) := mul_one _
  have hxval : v.intValuation x = WithZero.exp (-1 : ℤ) := by
    have hlt : v.intValuation (algebraMap (𝓞 F) (𝓞 K) (s n₁) * x₀) < v.intValuation π := by
      rw [hπ]
      exact lt_of_le_of_lt hxval2 (by rw [WithZero.exp_lt_exp]; norm_num)
    rw [hx_def, add_comm, (v.intValuation).map_add_eq_of_lt_right hlt, hπ]
  refine ⟨x, ?_, hxval⟩
  rw [← IntermediateField.adjoin_eq_top_iff, hx_def]
  exact hgtop

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
