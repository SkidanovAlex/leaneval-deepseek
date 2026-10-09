import Mathlib
import Submission.NK.CFTLib.RouteB.intersect_cyclotomic_eq_bot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped NumberField
open IntermediateField

namespace NK.CFTLib.ArtinReciprocityIdeal

/-- A rational prime `q` not dividing the discriminant of a number field `F` is unramified in
`F`: every prime ideal of `𝓞 F` above `(q)` has ramification index `1`. -/
private lemma unramified_of_not_dvd_discr' {F : Type} [Field F] [NumberField F] {q : ℕ}
    (hq : Nat.Prime q) (h : ¬ (q : ℤ) ∣ NumberField.discr F) :
    ∀ P : Ideal (𝓞 F), P.IsPrime →
      P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) → P.ramificationIdx ℤ = 1 := by
  intro P hP hlies
  have hpZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  haveI : P.IsPrime := hP
  have hmem : (q : 𝓞 F) ∈ P := by
    have h1 : (q : ℤ) ∈ Ideal.span ({(q : ℤ)} : Set ℤ) := Ideal.mem_span_singleton_self _
    rw [hlies.over, Ideal.mem_under] at h1
    simpa using h1
  have hne : P ≠ ⊥ := by
    intro hbot
    rw [hbot] at hmem
    simp only [Submodule.mem_bot] at hmem
    exact Nat.cast_ne_zero.mpr hq.ne_zero hmem
  have hmax : P.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot P hne
  haveI : Algebra.IsUnramifiedAt ℤ P :=
    (NumberField.not_dvd_discr_iff_forall_liesOver F (𝓞 F) hpZ).mp h P hmax hlies
  exact Ideal.ramificationIdx_eq_one P ℤ

/-- A form of `IntermediateField.LinearDisjoint.of_inf_eq_bot` whose `IsGalois` instance is an
explicit argument (the type-class search does not reliably find it at the application site when
the ambient field's `ℚ`-algebra structure is a local instance). -/
private theorem ld_of_inf_eq_bot' {F E : Type} [Field F] [Field E] [Algebra F E]
    {A B : IntermediateField F E} [IsGalois F ↥A] [FiniteDimensional F ↥A]
    [FiniteDimensional F ↥B] (h : A ⊓ B = ⊥) : A.LinearDisjoint ↥B :=
  IntermediateField.LinearDisjoint.of_inf_eq_bot h

/-- **`[K(ζ_q) : K] = q - 1` for `q` unramified in `K`.**  Let `K` be a number field, `q` a
rational prime not dividing `disc K`, `Ω` an overfield of `K` and `ζ ∈ Ω` a primitive `q`-th root
of unity.  Then `K(ζ_q)/K` has degree `q - 1 = φ(q)`.

Since `q ∤ disc K`, the first of the two number fields `ℚ(ζ_q)` and `K` (identified with its image
in `Ω`) is unramified at the only prime that could ramify in the other, so
`ℚ(ζ_q) ∩ K = ℚ` (`NK.CFTLib.RouteB.intersect_cyclotomic_eq_bot`).  Hence `K` and `ℚ(ζ_q)` are
linearly disjoint over `ℚ`, and since their compositum is `K(ζ_q)`, the degree over `K` is
`[ℚ(ζ_q) : ℚ] = φ(q) = q - 1`. -/
private theorem finrank_adjoin_primitiveRoot_prime {K Ω : Type} [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] (q : ℕ) (hq : q.Prime)
    (hK : ¬ (q : ℤ) ∣ NumberField.discr K) (ζ : Ω) (hζ : IsPrimitiveRoot ζ q) :
    Module.finrank K ↥(IntermediateField.adjoin K ({ζ} : Set Ω)) = q - 1 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI hCZ : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  haveI hTower : IsScalarTower ℚ K Ω :=
    IsScalarTower.of_algebraMap_eq fun x => by simp [map_ratCast]
  set Qζ : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ ({ζ} : Set Ω) with hQζ
  set Kq : IntermediateField ℚ Ω := (⊥ : IntermediateField K Ω).restrictScalars ℚ with hKq
  set Kζ : IntermediateField K Ω := IntermediateField.adjoin K ({ζ} : Set Ω) with hKζ
  -- ## `ℚ(ζ)` meets the image of `K` trivially
  have hdisjK : Qζ ⊓ Kq = ⊥ := by
    rw [hQζ, hKq]
    exact NK.CFTLib.RouteB.intersect_cyclotomic_eq_bot (F := K) q hq
      (unramified_of_not_dvd_discr' hq hK) ζ hζ
  -- ## `ℚ(ζ)` is a cyclotomic field of conductor `q`
  haveI hQζcyc : IsCyclotomicExtension {q} ℚ ↥Qζ := by
    rw [hQζ]
    exact (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin q ℚ Ω _ hζ).mpr rfl
  haveI hQζgal : IsGalois ℚ ↥Qζ := IsCyclotomicExtension.isGalois {q} ℚ ↥Qζ
  have hζint : IsIntegral ℚ ζ := (hζ.isIntegral hq.pos).tower_top
  haveI hQζfd : FiniteDimensional ℚ ↥Qζ := by
    rw [hQζ]
    exact IntermediateField.finiteDimensional_adjoin (S := ({ζ} : Set Ω)) (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      exact hx ▸ hζint)
  have hfrQζ : Module.finrank ℚ ↥Qζ = q - 1 := by
    rw [IsCyclotomicExtension.finrank ↥Qζ (Polynomial.cyclotomic.irreducible_rat hq.pos),
      Nat.totient_prime hq]
  haveI hKqfd : FiniteDimensional ℚ ↥Kq := by
    rw [hKq]; exact FiniteDimensional.trans ℚ K ↥(⊥ : IntermediateField K Ω)
  have hfrKq : Module.finrank ℚ ↥Kq = Module.finrank ℚ K := by
    have h : Module.finrank ℚ ↥(⊥ : IntermediateField K Ω) = Module.finrank ℚ K := by
      rw [← Module.finrank_mul_finrank ℚ K ↥(⊥ : IntermediateField K Ω),
        (IntermediateField.botEquiv K Ω).toLinearEquiv.finrank_eq, Module.finrank_self, mul_one]
    exact h
  -- ## `K(ζ)` restricted to `ℚ` is the compositum `Kq ⊔ Qζ`
  have hζQ : ζ ∈ (Qζ : Set Ω) := by
    rw [hQζ]; exact IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton ζ)
  have hζK : ζ ∈ (Kζ : Set Ω) := by
    rw [hKζ]; exact IntermediateField.subset_adjoin K _ (Set.mem_singleton ζ)
  have hKK : (Kq : Set Ω) ⊆ (Kζ : Set Ω) := by
    intro y hy
    obtain ⟨c, rfl⟩ := (IntermediateField.mem_bot).mp
      ((IntermediateField.mem_restrictScalars ℚ).mp (hKq ▸ hy))
    rw [hKζ]
    exact (IntermediateField.adjoin K ({ζ} : Set Ω)).algebraMap_mem c
  have hQK : (Qζ : Set Ω) ⊆ (Kζ : Set Ω) := by
    rw [hQζ, hKζ, IntermediateField.adjoin_subset_adjoin_iff]
    exact ⟨fun r hr => by
      obtain ⟨t, rfl⟩ := hr
      rw [IsScalarTower.algebraMap_apply ℚ K Ω]
      exact (IntermediateField.adjoin K ({ζ} : Set Ω)).algebraMap_mem t,
      fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        exact hy.symm ▸ hζK⟩
  have hKζq : Kζ.restrictScalars ℚ = Kq ⊔ Qζ := by
    have hsup : (Kq ⊔ Qζ : IntermediateField ℚ Ω) =
        IntermediateField.adjoin ℚ ((Kq : Set Ω) ∪ (Qζ : Set Ω)) := by
      rw [IntermediateField.adjoin_union, IntermediateField.adjoin_self,
        IntermediateField.adjoin_self]
    apply SetLike.coe_injective
    rw [IntermediateField.coe_restrictScalars, hsup]
    apply Set.Subset.antisymm
    · rw [hKζ, IntermediateField.adjoin_subset_adjoin_iff]
      constructor
      · intro y hy
        exact IntermediateField.subset_adjoin ℚ _
          (Set.subset_union_left ((IntermediateField.mem_restrictScalars ℚ).mpr
            ((IntermediateField.mem_bot).mpr hy)))
      · intro y hy
        rw [Set.mem_singleton_iff] at hy
        exact hy.symm ▸ (IntermediateField.subset_adjoin ℚ _ (Set.subset_union_right hζQ))
    · rw [hKζ, IntermediateField.adjoin_subset_adjoin_iff]
      exact ⟨fun r hr => by
        obtain ⟨t, rfl⟩ := hr
        rw [IsScalarTower.algebraMap_apply ℚ K Ω]
        exact (IntermediateField.adjoin K ({ζ} : Set Ω)).algebraMap_mem t,
        fun y hy => by
          rcases hy with hy | hy
          · exact hKK hy
          · exact hQK hy⟩
  -- ## the degree computation
  haveI hKζfd : FiniteDimensional K ↥Kζ := by
    rw [hKζ]
    exact IntermediateField.finiteDimensional_adjoin (S := ({ζ} : Set Ω)) (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      exact hx ▸ hζint.tower_top)
  have hfrKζ : Module.finrank K ↥Kζ = q - 1 := by
    have h1 : Module.finrank ℚ K * Module.finrank K ↥Kζ = Module.finrank ℚ ↥Kζ :=
      Module.finrank_mul_finrank ℚ K ↥Kζ
    have h2 : Module.finrank ℚ ↥Kζ = Module.finrank ℚ K * (q - 1) := by
      have heq : Module.finrank ℚ ↥Kζ = Module.finrank ℚ ↥(Kq ⊔ Qζ) := by
        rw [show Module.finrank ℚ ↥Kζ = Module.finrank ℚ ↥(Kζ.restrictScalars ℚ) from rfl,
          hKζq]
      rw [heq, sup_comm]
      have hLDK : Qζ.LinearDisjoint ↥Kq :=
        @ld_of_inf_eq_bot' ℚ Ω _ _ _ Qζ Kq hQζgal _ _ hdisjK
      rw [IntermediateField.LinearDisjoint.finrank_sup hLDK, hfrQζ, hfrKq]
      ring
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h1
  exact hfrKζ

/-- **The cyclotomic character of `K(ζ_q)/K` is surjective.**  Let `K` be a number field, `q` a
rational prime unramified in `K` (`q ∤ disc K`), `Ω` an overfield and `ζ ∈ Ω` a primitive `q`-th
root of unity.  Then every `τ ∈ (ℤ/q)^×` is realised by a `K`-automorphism of `K(ζ_q)`:
there is `σ` with `σ ζ = ζ^τ`.

This follows from the injectivity of `IsPrimitiveRoot.autToPow K` (`autToPow_injective`) and the
cardinality count `Nat.card Gal(K(ζ_q)/K) = [K(ζ_q):K] = q - 1 = Nat.card (ℤ/q)^×`: from
`q ∤ disc K` one gets `K ∩ ℚ(ζ_q) = ℚ`, hence `K(ζ_q)/K` is linearly disjoint from `ℚ(ζ_q)/ℚ`
and `[K(ζ_q):K] = [ℚ(ζ_q):ℚ] = q - 1`. -/
theorem exists_algEquiv_zeta_pow {K Ω : Type} [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] (q : ℕ) (hq : q.Prime)
    (hK : ¬ (q : ℤ) ∣ NumberField.discr K)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ q) (τ : (ZMod q)ˣ) :
    ∃ σ : (IntermediateField.adjoin K ({ζ} : Set Ω)) ≃ₐ[K]
        (IntermediateField.adjoin K ({ζ} : Set Ω)),
      σ ⟨ζ, IntermediateField.mem_adjoin_simple_self K ζ⟩ =
        (⟨ζ, IntermediateField.mem_adjoin_simple_self K ζ⟩ :
          ↥(IntermediateField.adjoin K ({ζ} : Set Ω))) ^ (τ : ZMod q).val := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  set S : IntermediateField K Ω := IntermediateField.adjoin K ({ζ} : Set Ω) with hS
  have hmemζ : ζ ∈ S := IntermediateField.mem_adjoin_simple_self K ζ
  have hζS : IsPrimitiveRoot (⟨ζ, hmemζ⟩ : S) q := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact hζ
  have hζint : IsIntegral K ζ := by
    refine ⟨Polynomial.X ^ q - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hq.ne_zero, ?_⟩
    simp [hζ.pow_eq_one]
  haveI hcyc : IsCyclotomicExtension ({q} : Set ℕ) K S :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin q K Ω S hζ).mpr rfl
  haveI hgal : IsGalois K S := IsCyclotomicExtension.isGalois {q} K S
  haveI hfd : FiniteDimensional K S := by
    rw [hS]
    exact IntermediateField.finiteDimensional_adjoin (S := ({ζ} : Set Ω))
      (fun x hx => by rw [Set.mem_singleton_iff] at hx; exact hx ▸ hζint)
  have hfr : Module.finrank K S = q - 1 := finrank_adjoin_primitiveRoot_prime q hq hK ζ hζ
  have hcard : Nat.card (S ≃ₐ[K] S) = Nat.card (ZMod q)ˣ := by
    rw [IsGalois.card_aut_eq_finrank K S, hfr, Nat.card_eq_fintype_card, ZMod.card_units q]
  have hinj : Function.Injective (hζS.autToPow K) := hζS.autToPow_injective K
  haveI : Fintype (S ≃ₐ[K] S) := Fintype.ofFinite _
  have hc : Fintype.card (S ≃ₐ[K] S) = Fintype.card (ZMod q)ˣ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact hcard
  obtain ⟨e⟩ := Fintype.card_eq.mp hc
  have hsurj : Function.Surjective (hζS.autToPow K) :=
    Function.Injective.surjective_of_finite e hinj
  obtain ⟨σ, hσ⟩ := hsurj τ
  refine ⟨σ, ?_⟩
  rw [← IsPrimitiveRoot.autToPow_spec K hζS σ, hσ]

end NK.CFTLib.ArtinReciprocityIdeal
