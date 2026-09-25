import Mathlib
import Submission.NK.CFTLib.ARL.disjoint_restrictScalars_adjoin_zeta
import Submission.NK.CFTLib.ARL.isFrobAtPrime_zeta
import Submission.NK.CFTLib.ArtinReciprocityIdeal.exists_algEquiv_zeta_pow

namespace NK.CFTLib.ArtinReciprocityIdeal.AuxFamily

open IntermediateField

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-- A form of `IntermediateField.LinearDisjoint.of_inf_eq_bot` whose `IsGalois` instance is an
explicit argument (the type-class search does not reliably find it at the application site when
the ambient field's `ℚ`-algebra structure is a local instance). -/
private theorem ld_of_inf_eq_bot' {F E : Type} [Field F] [Field E] [Algebra F E]
    {A B : IntermediateField F E} [IsGalois F ↥A] [FiniteDimensional F ↥A]
    [FiniteDimensional F ↥B] (h : A ⊓ B = ⊥) : A.LinearDisjoint ↥B :=
  IntermediateField.LinearDisjoint.of_inf_eq_bot h

/-- **`[K(ζ_M) : K] = φ(M)` when no prime dividing `M` divides `disc K`.**  Let `K` be a number
field, `M > 0`, `Ω` an overfield of `K` and `ζ ∈ Ω` a primitive `M`-th root of unity.  If no prime
divisor of `M` divides `disc K`, then `K(ζ)/K` has degree `M.totient`.

Indeed `ℚ(ζ) ∩ K = ℚ` (`NK.CFTLib.ARL.intersect_cyclotomic_eq_bot_gen`), so `ℚ(ζ)` and `K` are
linearly disjoint over `ℚ` and the compositum `K(ζ)` has degree `[K:ℚ]·φ(M)` over `ℚ`. -/
private theorem finrank_adjoin_primitiveRoot {K Ω : Type} [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] (M : ℕ) (hM : M ≠ 0)
    (hdisc : ∀ q : ℕ, q.Prime → q ∣ M → ¬ q ∣ (NumberField.discr K).natAbs)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ M) :
    Module.finrank K ↥(IntermediateField.adjoin K ({ζ} : Set Ω)) = M.totient := by
  classical
  haveI : NeZero M := ⟨hM⟩
  haveI hcz : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  haveI hTower : IsScalarTower ℚ K Ω :=
    IsScalarTower.of_algebraMap_eq fun x => by simp [map_ratCast]
  set Qζ : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ ({ζ} : Set Ω) with hQζ
  set Kq : IntermediateField ℚ Ω := (⊥ : IntermediateField K Ω).restrictScalars ℚ with hKq
  set Kζ : IntermediateField K Ω := IntermediateField.adjoin K ({ζ} : Set Ω) with hKζ
  -- ## `ℚ(ζ)` meets the image of `K` trivially
  have hdisjK : Qζ ⊓ Kq = ⊥ := by
    rw [hQζ, hKq]
    exact NK.CFTLib.ARL.intersect_cyclotomic_eq_bot_gen (F := K) M hdisc ζ hζ
  -- ## `ℚ(ζ)` is a cyclotomic field of conductor `M`
  haveI hQζcyc : IsCyclotomicExtension {M} ℚ ↥Qζ := by
    rw [hQζ]
    exact (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin M ℚ Ω
      (IntermediateField.adjoin ℚ ({ζ} : Set Ω)) hζ).mpr rfl
  haveI hQζgal : IsGalois ℚ ↥Qζ := IsCyclotomicExtension.isGalois {M} ℚ ↥Qζ
  haveI hQζfd : FiniteDimensional ℚ ↥Qζ := by
    rw [hQζ]
    exact IntermediateField.finiteDimensional_adjoin (S := ({ζ} : Set Ω)) (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      exact hx ▸ (hζ.isIntegral (NeZero.pos M)).tower_top)
  have hfrQζ : Module.finrank ℚ ↥Qζ = M.totient := by
    rw [IsCyclotomicExtension.finrank ↥Qζ (Polynomial.cyclotomic.irreducible_rat (NeZero.pos M))]
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
      exact hx ▸ (hζ.isIntegral (NeZero.pos M)).tower_top)
  have hfrKζ : Module.finrank K ↥Kζ = M.totient := by
    have h1 : Module.finrank ℚ K * Module.finrank K ↥Kζ = Module.finrank ℚ ↥Kζ :=
      Module.finrank_mul_finrank ℚ K ↥Kζ
    have h2 : Module.finrank ℚ ↥Kζ = Module.finrank ℚ K * M.totient := by
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

/-- **The cyclotomic character of `K(ζ_M)/K` is surjective.**  Let `K` be a number field, `M > 0`,
`ζ` a primitive `M`-th root of unity in a field `Ω` with `Algebra K Ω`, and suppose that no prime
dividing `M` divides the discriminant of `K`.  Then for every `u` coprime to `M` there is a
`K`-automorphism of `K⟮ζ⟯` raising `ζ` to the `u`-th power. -/
theorem autToPow_surjective_of_not_dvd_discr {K Ω : Type} [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] (M : ℕ) (hM : M ≠ 0) (ζ : Ω) (hζ : IsPrimitiveRoot ζ M)
    (hdisc : ∀ q : ℕ, q.Prime → q ∣ M → ¬ q ∣ (NumberField.discr K).natAbs)
    (u : ℕ) (hu : Nat.Coprime u M) :
    ∃ σ : ↥(IntermediateField.adjoin K ({ζ} : Set Ω)) ≃ₐ[K]
        ↥(IntermediateField.adjoin K ({ζ} : Set Ω)),
      σ ⟨ζ, IntermediateField.mem_adjoin_simple_self K ζ⟩ =
        (⟨ζ, IntermediateField.mem_adjoin_simple_self K ζ⟩ :
          ↥(IntermediateField.adjoin K ({ζ} : Set Ω))) ^ u := by
  classical
  haveI : NeZero M := ⟨hM⟩
  set S : IntermediateField K Ω := IntermediateField.adjoin K ({ζ} : Set Ω) with hS
  have hmemζ : ζ ∈ S := IntermediateField.mem_adjoin_simple_self K ζ
  set ζS : S := ⟨ζ, hmemζ⟩ with hζSdef
  have hζS : IsPrimitiveRoot ζS M := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact hζ
  have hζint : IsIntegral K ζ := by
    refine ⟨Polynomial.X ^ M - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hM, ?_⟩
    simp [hζ.pow_eq_one]
  haveI hcyc : IsCyclotomicExtension ({M} : Set ℕ) K S :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin M K Ω S hζ).mpr rfl
  haveI hgal : IsGalois K S := IsCyclotomicExtension.isGalois {M} K S
  haveI hfd : FiniteDimensional K S := by
    rw [hS]
    exact IntermediateField.finiteDimensional_adjoin (S := ({ζ} : Set Ω))
      (fun x hx => by rw [Set.mem_singleton_iff] at hx; exact hx ▸ hζint)
  have hfr : Module.finrank K S = M.totient :=
    finrank_adjoin_primitiveRoot M hM hdisc ζ hζ
  have hcard : Nat.card (S ≃ₐ[K] S) = Nat.card (ZMod M)ˣ := by
    rw [IsGalois.card_aut_eq_finrank K S, hfr, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient]
  have hinj : Function.Injective (hζS.autToPow K) := hζS.autToPow_injective K
  haveI : Fintype (S ≃ₐ[K] S) := Fintype.ofFinite _
  have hc : Fintype.card (S ≃ₐ[K] S) = Fintype.card (ZMod M)ˣ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact hcard
  obtain ⟨e⟩ := Fintype.card_eq.mp hc
  have hsurj : Function.Surjective (hζS.autToPow K) :=
    Function.Injective.surjective_of_finite e hinj
  obtain ⟨σ, hσ⟩ := hsurj (ZMod.unitOfCoprime u hu)
  refine ⟨σ, ?_⟩
  have hspec := IsPrimitiveRoot.autToPow_spec K hζS σ
  rw [← hspec, hσ]
  have hcoe : ((ZMod.unitOfCoprime u hu : (ZMod M)ˣ) : ZMod M) = (u : ZMod M) :=
    ZMod.coe_unitOfCoprime u hu
  rw [hcoe, ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div u M]
  rw [pow_add, pow_mul, hζS.pow_eq_one, one_pow, mul_one]

end NK.CFTLib.ArtinReciprocityIdeal.AuxFamily
