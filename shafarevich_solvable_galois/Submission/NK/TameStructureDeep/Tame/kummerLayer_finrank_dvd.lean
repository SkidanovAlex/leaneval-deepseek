import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.TameStructureDeep.Tame

open Polynomial IntermediateField

set_option linter.style.haveILetI false

/-- **The general Kummer layer.**  Let `F` be a field of characteristic zero containing a primitive
`n`-th root of unity, `a ∈ F`, `β` an element of an `F`-algebra `E` with `β ^ n = a`.  Then the
degree `m = [F⟮β⟯ : F]` divides `n`, and `β ^ m ∈ F`. -/
theorem kummerLayer_finrank_dvd {F E : Type*} [Field F] [CharZero F] [Field E]
    [Algebra F E] {n : ℕ} (hn : 0 < n) {a : F} {β : E} (hβ : β ^ n = algebraMap F E a)
    (hζ : (primitiveRoots n F).Nonempty) :
    Module.finrank F ↥(IntermediateField.adjoin F {β}) ∣ n ∧
      ∃ c : F, algebraMap F E c =
        β ^ (Module.finrank F ↥(IntermediateField.adjoin F {β})) := by
  by_cases ha : a = 0
  · -- `β = 0`, so `F⟮β⟯ = F` and both claims are trivial
    subst ha
    have hβ0 : β = 0 := by
      by_contra hb
      exact (pow_ne_zero n hb) (by simpa using hβ)
    have hL : IntermediateField.adjoin F ({β} : Set E) = ⊥ := by
      rw [hβ0]
      exact IntermediateField.adjoin_zero
    rw [hL, IntermediateField.finrank_bot]
    exact ⟨one_dvd n, ⟨0, by rw [hβ0]; simp⟩⟩
  · -- main case: `a ≠ 0`, hence `β ≠ 0`
    obtain ⟨ζ, hζmem⟩ := hζ
    have hζp : IsPrimitiveRoot ζ n := (mem_primitiveRoots hn).mp hζmem
    haveI : NeZero n := ⟨hn.ne'⟩
    -- the Kummer layer `L = F⟮β⟯`
    set L : IntermediateField F E := IntermediateField.adjoin F ({β} : Set E) with hLdef
    let βL : L := ⟨β, IntermediateField.mem_adjoin_simple_self F β⟩
    have hcoe : ((βL : L) : E) = β := rfl
    have hβL : (βL : L) ^ n = algebraMap F L a := by
      apply Subtype.coe_injective
      simp only [SubmonoidClass.coe_pow, hcoe, IsScalarTower.algebraMap_apply F L E,
        IntermediateField.algebraMap_apply, hβ]
    have hβL_int : IsIntegral F βL :=
      ⟨X ^ n - C a, Polynomial.monic_X_pow_sub_C a hn.ne', by
        change (aeval βL) (X ^ n - C a) = 0
        rw [map_sub, map_pow, aeval_X, aeval_C, hβL, sub_self]⟩
    -- `βL` generates `L` over `F`, also as an `F`-subalgebra
    have hadj_top : IntermediateField.adjoin F ({βL} : Set ↥L) = ⊤ := by
      apply IntermediateField.lift_injective L
      rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]
    have hAlgTop : Algebra.adjoin F ({βL} : Set ↥L) = ⊤ :=
      (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic (S := ({βL} : Set ↥L))
        (by intro x hx; rw [Set.mem_singleton_iff] at hx; exact hx ▸ hβL_int.isAlgebraic)).mp
        hadj_top
    -- `L` is the splitting field of `X ^ n - C a` over `F`
    have hβLmem : βL ∈ (X ^ n - C a : F[X]).rootSet ↥L := by
      rw [Polynomial.mem_rootSet]
      exact ⟨Polynomial.X_pow_sub_C_ne_zero hn a, by
        change (aeval βL) (X ^ n - C a) = 0
        rw [map_sub, map_pow, aeval_X, aeval_C, hβL, sub_self]⟩
    have hζL : IsPrimitiveRoot (algebraMap F ↥L ζ) n :=
      hζp.map_of_injective (algebraMap F ↥L).injective
    have hf_sep : (X ^ n - C a : F[X]).Separable :=
      separable_X_pow_sub_C a (Nat.cast_ne_zero.mpr hn.ne') ha
    have hL_splits : ((X ^ n - C a : F[X]).map (algebraMap F ↥L)).Splits := by
      rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
      exact X_pow_sub_C_splits_of_isPrimitiveRoot hζL hβL
    haveI : Polynomial.IsSplittingField F ↥L (X ^ n - C a : F[X]) :=
      ⟨hL_splits, by
        rw [eq_top_iff]
        calc ⊤ = Algebra.adjoin F ({βL} : Set ↥L) := hAlgTop.symm
          _ ≤ Algebra.adjoin F ((X ^ n - C a : F[X]).rootSet ↥L) :=
              Algebra.adjoin_mono (by
                intro x hx
                rw [Set.mem_singleton_iff] at hx
                subst hx
                exact hβLmem)⟩
    haveI : FiniteDimensional F ↥L :=
      Polynomial.IsSplittingField.finiteDimensional ↥L (X ^ n - C a)
    haveI : IsGalois F ↥L := IsGalois.of_separable_splitting_field hf_sep
    have hcard : Nat.card Gal(↥L/F) = Module.finrank F ↥L := IsGalois.card_aut_eq_finrank F ↥L
    -- `βL ≠ 0` and `a ≠ 0` in `L`
    have hβL_ne : (βL : ↥L) ≠ 0 := by
      intro h
      have h1 : (βL : ↥L) ^ n = 0 := by rw [h, zero_pow hn.ne']
      rw [hβL] at h1
      exact ha ((algebraMap F ↥L).injective (by simpa using h1))
    have hβLma_ne : algebraMap F ↥L a ≠ 0 := by
      intro h
      exact ha ((algebraMap F ↥L).injective (by simpa using h))
    -- every `n`-th root of unity in `L` lies in the prime field
    have hμL : ∀ η : rootsOfUnity n ↥L, ∃ c : F, algebraMap F ↥L c = ((η : Units ↥L) : ↥L) := by
      intro η
      obtain ⟨i, -, hi⟩ :=
        hζL.eq_pow_of_pow_eq_one ((mem_rootsOfUnity' n (η : Units ↥L)).mp η.prop)
      exact ⟨ζ ^ i, by rw [map_pow]; exact hi⟩
    have hfix_div : ∀ (σ : Gal(↥L/F)) (x : ↥L), x ^ n = 1 → σ x = x := by
      intro σ x hx
      obtain ⟨c, hc⟩ := hμL (rootsOfUnity.mkOfPowEq x hx)
      rw [rootsOfUnity.coe_mkOfPowEq] at hc
      rw [← hc, AlgEquiv.commutes]
    -- the Kummer pairing `σ ↦ σ βL / βL`
    have hratio_pow : ∀ σ : Gal(↥L/F), ((σ βL) / βL) ^ n = 1 := by
      intro σ
      rw [div_pow, ← map_pow, hβL, AlgEquiv.commutes, div_self hβLma_ne]
    let Ψ : Gal(↥L/F) →* rootsOfUnity n ↥L :=
      { toFun := fun σ => rootsOfUnity.mkOfPowEq ((σ βL) / βL) (hratio_pow σ)
        map_one' := by
          apply Subtype.ext
          apply Units.ext
          rw [rootsOfUnity.coe_mkOfPowEq, AlgEquiv.one_apply, div_self hβL_ne,
            OneMemClass.coe_one, Units.val_one]
        map_mul' := fun σ τ => by
          apply Subtype.ext
          apply Units.ext
          rw [rootsOfUnity.coe_mkOfPowEq]
          rw [AlgEquiv.mul_apply]
          have hσ : σ (τ βL) = ((τ βL) / βL) * σ βL := by
            conv_lhs => rw [← div_mul_cancel₀ (τ βL) hβL_ne]
            rw [map_mul, hfix_div σ ((τ βL) / βL) (hratio_pow τ)]
          rw [hσ]
          try simp only [Subgroup.coe_mul, Units.val_mul, rootsOfUnity.coe_mkOfPowEq]
          try field_simp }
    have hΨ_coe : ∀ σ : Gal(↥L/F), ((Ψ σ : Units ↥L) : ↥L) = (σ βL) / βL := fun _ => rfl
    -- the pairing is injective
    have hΨ_inj : Function.Injective Ψ := by
      intro σ τ hστ
      have h1 : σ βL = τ βL := by
        have h := congrArg (fun x : rootsOfUnity n ↥L => ((x : Units ↥L) : ↥L)) hστ
        rw [hΨ_coe, hΨ_coe] at h
        exact (div_left_inj' hβL_ne).mp h
      have h2 : (σ : ↥L →ₐ[F] ↥L) = (τ : ↥L →ₐ[F] ↥L) := by
        apply IntermediateField.algHom_ext_of_eq_adjoin (hS := hLdef)
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact h1
      exact AlgEquiv.coe_toAlgHom_injective h2
    have hrange : Nat.card Ψ.range = Nat.card Gal(↥L/F) :=
      (Nat.card_congr (MonoidHom.ofInjective hΨ_inj).toEquiv).symm
    -- the degree divides `n`
    have hdvd : Module.finrank F ↥L ∣ n := by
      rw [← hcard, ← hrange]
      calc Nat.card Ψ.range ∣ Nat.card (rootsOfUnity n ↥L) := Subgroup.card_subgroup_dvd_card _
        _ = n := hζL.card_rootsOfUnity
    -- `βL ^ m` is fixed by all automorphisms, hence lies in the prime field
    have hfixed : ∀ σ : Gal(↥L/F),
        σ ((βL : ↥L) ^ Module.finrank F ↥L) = (βL : ↥L) ^ Module.finrank F ↥L := by
      intro σ
      have hpow : (Ψ σ) ^ Module.finrank F ↥L = 1 := by
        have h1 : σ ^ Module.finrank F ↥L = 1 := by
          rw [← hcard]
          exact pow_card_eq_one'
        rw [← map_pow, h1, map_one]
      have hpow' : (((Ψ σ : Units ↥L) : ↥L)) ^ Module.finrank F ↥L = 1 := by
        have h2 := congrArg (fun x : rootsOfUnity n ↥L => ((x : Units ↥L) : ↥L)) hpow
        simpa using h2
      have hbm : σ βL = ((Ψ σ : Units ↥L) : ↥L) * βL := by
        rw [hΨ_coe]
        exact (div_mul_cancel₀ (σ βL) hβL_ne).symm
      rw [map_pow, hbm, mul_pow, hpow', one_mul]
    obtain ⟨c, hc⟩ :=
      (IsGalois.mem_range_algebraMap_iff_fixed ((βL : ↥L) ^ Module.finrank F ↥L)).mpr hfixed
    refine ⟨hdvd, ⟨c, ?_⟩⟩
    rw [IsScalarTower.algebraMap_apply F ↥L E, hc, IntermediateField.algebraMap_apply,
      SubmonoidClass.coe_pow, hcoe]

end NK.TameStructureDeep.Tame
