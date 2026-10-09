import Mathlib
import Submission.NK.Chebotarev.Basic
import Submission.NK.Chebotarev.IsFrobAtRestrictNormalHom
import Submission.NK.CFTLib.ARL.disjoint_restrictScalars_adjoin_zeta
import Submission.NK.CFTLib.ARL.isFrobAtPrime_zeta
import Submission.NK.CFTLib.ARL.isGalois_cyclotomicField_over_base
import Submission.NK.CFTLib.ARL.autToPow_eq_of_pow_eq
import Submission.NK.CFTLib.ARL.inertiaDeg_one_isFrobAtPrime_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace NK.CFTLib.Existence

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **`CyclotomicField M L` is `L` adjoined with a primitive `M`-th root of unity.** -/
theorem adjoin_zeta_eq_top (M : ℕ) [NeZero M] :
    (⊤ : IntermediateField L (CyclotomicField M L)) =
      IntermediateField.adjoin L
        ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} :
          Set (CyclotomicField M L)) := by
  haveI htop : IsCyclotomicExtension {M} L
      ↥(⊤ : IntermediateField L (CyclotomicField M L)) :=
    IsCyclotomicExtension.equiv {M} L (CyclotomicField M L)
      (IntermediateField.topEquiv (F := L)).symm
  exact (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin M L
    (CyclotomicField M L) ⊤ (IsCyclotomicExtension.zeta_spec M L _)).mp htop

/-- **`L(ζ_M) = L ⊔ K(ζ_M)`** as intermediate fields of `CyclotomicField M L` over `K`. -/
theorem sup_restrictScalars_adjoin_zeta_eq_top (M : ℕ) [NeZero M] :
    (⊥ : IntermediateField L (CyclotomicField M L)).restrictScalars K ⊔
      IntermediateField.adjoin K
        ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} :
          Set (CyclotomicField M L)) = ⊤ := by
  set A : IntermediateField K (CyclotomicField M L) :=
    (⊥ : IntermediateField L (CyclotomicField M L)).restrictScalars K with hA
  set ζ := IsCyclotomicExtension.zeta M L (CyclotomicField M L) with hζ
  set B : IntermediateField K (CyclotomicField M L) :=
    IntermediateField.adjoin K ({ζ} : Set (CyclotomicField M L)) with hB
  have htop : (⊤ : IntermediateField L (CyclotomicField M L)) =
      IntermediateField.adjoin L ({ζ} : Set (CyclotomicField M L)) :=
    adjoin_zeta_eq_top (L := L) M
  have hsub : (IntermediateField.adjoin L ({ζ} : Set (CyclotomicField M L)) :
      Set (CyclotomicField M L)) ⊆
      (IntermediateField.adjoin K
        ((A ⊔ B : IntermediateField K (CyclotomicField M L)) :
          Set (CyclotomicField M L))) := by
    rw [IntermediateField.adjoin_subset_adjoin_iff]
    constructor
    · rintro y ⟨l, rfl⟩
      refine IntermediateField.subset_adjoin K _ ((le_sup_left : A ≤ A ⊔ B) ?_)
      rw [hA]
      exact (IntermediateField.mem_restrictScalars K).mpr (IntermediateField.mem_bot.mpr ⟨l, rfl⟩)
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact IntermediateField.subset_adjoin K _
        ((le_sup_right : B ≤ A ⊔ B)
          (IntermediateField.subset_adjoin K _ (Set.mem_singleton ζ)))
  have hle : IntermediateField.adjoin K
      ((A ⊔ B : IntermediateField K (CyclotomicField M L)) :
        Set (CyclotomicField M L)) ≤ A ⊔ B :=
    IntermediateField.adjoin_le_iff.mpr (fun x hx => hx)
  have huniv : (IntermediateField.adjoin L ({ζ} : Set (CyclotomicField M L)) :
      Set (CyclotomicField M L)) = Set.univ := by
    rw [← htop]
    rfl
  change A ⊔ B = ⊤
  refine le_antisymm le_top ?_
  intro x hx
  exact hle (hsub (huniv ▸ Set.mem_univ x))

/-- **`L(ζ_M) = L ⊔ ℚ(ζ_M)`** as intermediate fields of `CyclotomicField M L` over `ℚ`. -/
theorem sup_restrictScalars_adjoin_zeta_eq_top_rat (M : ℕ) [NeZero M] :
    (⊥ : IntermediateField L (CyclotomicField M L)).restrictScalars ℚ ⊔
      IntermediateField.adjoin ℚ
        ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} :
          Set (CyclotomicField M L)) = ⊤ := by
  set A : IntermediateField ℚ (CyclotomicField M L) :=
    (⊥ : IntermediateField L (CyclotomicField M L)).restrictScalars ℚ with hA
  set ζ := IsCyclotomicExtension.zeta M L (CyclotomicField M L) with hζ
  set B : IntermediateField ℚ (CyclotomicField M L) :=
    IntermediateField.adjoin ℚ ({ζ} : Set (CyclotomicField M L)) with hB
  have htop : (⊤ : IntermediateField L (CyclotomicField M L)) =
      IntermediateField.adjoin L ({ζ} : Set (CyclotomicField M L)) :=
    adjoin_zeta_eq_top (L := L) M
  have hsub : (IntermediateField.adjoin L ({ζ} : Set (CyclotomicField M L)) :
      Set (CyclotomicField M L)) ⊆
      (IntermediateField.adjoin ℚ
        ((A ⊔ B : IntermediateField ℚ (CyclotomicField M L)) :
          Set (CyclotomicField M L))) := by
    rw [IntermediateField.adjoin_subset_adjoin_iff]
    constructor
    · rintro y ⟨l, rfl⟩
      refine IntermediateField.subset_adjoin ℚ _ ((le_sup_left : A ≤ A ⊔ B) ?_)
      rw [hA]
      exact (IntermediateField.mem_restrictScalars ℚ).mpr (IntermediateField.mem_bot.mpr ⟨l, rfl⟩)
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact IntermediateField.subset_adjoin ℚ _
        ((le_sup_right : B ≤ A ⊔ B)
          (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton ζ)))
  have hle : IntermediateField.adjoin ℚ
      ((A ⊔ B : IntermediateField ℚ (CyclotomicField M L)) :
        Set (CyclotomicField M L)) ≤ A ⊔ B :=
    IntermediateField.adjoin_le_iff.mpr (fun x hx => hx)
  have huniv : (IntermediateField.adjoin L ({ζ} : Set (CyclotomicField M L)) :
      Set (CyclotomicField M L)) = Set.univ := by
    rw [← htop]
    rfl
  change A ⊔ B = ⊤
  refine le_antisymm le_top ?_
  intro x hx
  exact hle (hsub (huniv ▸ Set.mem_univ x))

/-- The absolute norm of a prime ideal of a number field is at least two. -/
theorem one_lt_absNorm_heightOneSpectrum (F : Type*) [Field F] [NumberField F]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : 1 < Ideal.absNorm 𝔭.asIdeal := by
  haveI : 𝔭.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal 𝔭.isPrime 𝔭.ne_bot
  haveI : Field (𝓞 F ⧸ 𝔭.asIdeal) := Ideal.Quotient.field 𝔭.asIdeal
  haveI : Finite (𝓞 F ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot 𝔭.asIdeal 𝔭.ne_bot
  haveI : Fintype (𝓞 F ⧸ 𝔭.asIdeal) := Fintype.ofFinite _
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

/-- **`[F(ζ_M) : F] = φ(M)`.**  Let `F` be a number field, `Ω` a field containing a primitive
`M`-th root of unity `ζ`, and assume that no prime divisor of `M` divides `discr F`.  Then the
degree of `F(ζ)` over `F` is `M.totient`.

The proof computes the degree over `ℚ`: `F(ζ) = F·ℚ(ζ)` with `F ⊓ ℚ(ζ) = ℚ` (the discriminant
input `intersect_cyclotomic_eq_bot_gen`), so `[F(ζ):ℚ] = [F:ℚ]·φ(M)` by linear disjointness, and
the claim follows by cancelling `[F:ℚ]`. -/
theorem finrank_adjoin_zeta_eq_totient {Ω : Type} [Field Ω] [Algebra K Ω] [Algebra ℚ Ω]
    [IsScalarTower ℚ K Ω] (M : ℕ) [NeZero M]
    (hM : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr K).natAbs)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ M) :
    Module.finrank K ↥(IntermediateField.adjoin K ({ζ} : Set Ω)) = M.totient := by
  classical
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  set T : IntermediateField K Ω := IntermediateField.adjoin K ({ζ} : Set Ω) with hT
  set Qζ : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ ({ζ} : Set Ω) with hQζ
  set Kq : IntermediateField ℚ Ω := (⊥ : IntermediateField K Ω).restrictScalars ℚ with hKq
  have hdisjK : Qζ ⊓ Kq = ⊥ := by
    rw [hQζ, hKq]
    exact NK.CFTLib.ARL.intersect_cyclotomic_eq_bot_gen (F := K) M hM ζ hζ
  letI : Algebra ℚ ↥Qζ := Qζ.algebra'
  haveI hQζcyc : IsCyclotomicExtension {M} ℚ ↥Qζ :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin M ℚ Ω
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
    rw [hKq]
    exact FiniteDimensional.trans ℚ K ↥(⊥ : IntermediateField K Ω)
  have hfrKq : Module.finrank ℚ ↥Kq = Module.finrank ℚ K := by
    have h : Module.finrank ℚ ↥(⊥ : IntermediateField K Ω) = Module.finrank ℚ K := by
      rw [← Module.finrank_mul_finrank ℚ K ↥(⊥ : IntermediateField K Ω),
        (IntermediateField.botEquiv K Ω).toLinearEquiv.finrank_eq, Module.finrank_self, mul_one]
    exact h
  have hζQ : ζ ∈ (Qζ : Set Ω) := by
    rw [hQζ]; exact IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton ζ)
  have hζT : ζ ∈ (T : Set Ω) := by
    rw [hT]; exact IntermediateField.subset_adjoin K _ (Set.mem_singleton ζ)
  have hKqT : (Kq : Set Ω) ⊆ (T : Set Ω) := by
    intro y hy
    obtain ⟨c, rfl⟩ := (IntermediateField.mem_bot).mp
      ((IntermediateField.mem_restrictScalars ℚ).mp (hKq ▸ hy))
    rw [hT]
    exact (IntermediateField.adjoin K ({ζ} : Set Ω)).algebraMap_mem c
  have hQζT : (Qζ : Set Ω) ⊆ (T : Set Ω) := by
    rw [hQζ, hT, IntermediateField.adjoin_subset_adjoin_iff]
    exact ⟨fun r hr => by
      obtain ⟨t, rfl⟩ := hr
      rw [IsScalarTower.algebraMap_apply ℚ K Ω]
      exact (IntermediateField.adjoin K ({ζ} : Set Ω)).algebraMap_mem t,
      fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        exact hy.symm ▸ hζT⟩
  have hTℚ : T.restrictScalars ℚ = Kq ⊔ Qζ := by
    have hsup : (Kq ⊔ Qζ : IntermediateField ℚ Ω) =
        IntermediateField.adjoin ℚ ((Kq : Set Ω) ∪ (Qζ : Set Ω)) := by
      rw [IntermediateField.adjoin_union, IntermediateField.adjoin_self,
        IntermediateField.adjoin_self]
    apply SetLike.coe_injective
    rw [IntermediateField.coe_restrictScalars, hsup]
    apply Set.Subset.antisymm
    · rw [hT, IntermediateField.adjoin_subset_adjoin_iff]
      constructor
      · intro y hy
        exact IntermediateField.subset_adjoin ℚ _
          (Set.subset_union_left ((IntermediateField.mem_restrictScalars ℚ).mpr
            ((IntermediateField.mem_bot).mpr hy)))
      · intro y hy
        rw [Set.mem_singleton_iff] at hy
        exact hy.symm ▸ (IntermediateField.subset_adjoin ℚ _ (Set.subset_union_right hζQ))
    · rw [hT, IntermediateField.adjoin_subset_adjoin_iff]
      exact ⟨fun r hr => by
        obtain ⟨t, rfl⟩ := hr
        rw [IsScalarTower.algebraMap_apply ℚ K Ω]
        exact (IntermediateField.adjoin K ({ζ} : Set Ω)).algebraMap_mem t,
        fun y hy => by
          rcases hy with hy | hy
          · exact hKqT hy
          · exact hQζT hy⟩
  have h1 : Module.finrank ℚ K * Module.finrank K ↥T = Module.finrank ℚ ↥T :=
    Module.finrank_mul_finrank ℚ K ↥T
  have h2 : Module.finrank ℚ ↥T = Module.finrank ℚ K * M.totient := by
    have heq : Module.finrank ℚ ↥T = Module.finrank ℚ ↥(Kq ⊔ Qζ) := by
      rw [show Module.finrank ℚ ↥T = Module.finrank ℚ ↥(T.restrictScalars ℚ) from rfl, hTℚ]
    rw [heq, sup_comm]
    have hLDK : Qζ.LinearDisjoint ↥Kq :=
      @IntermediateField.LinearDisjoint.of_inf_eq_bot ℚ Ω _ _ _ Qζ Kq hQζgal _ _ hdisjK
    rw [IntermediateField.LinearDisjoint.finrank_sup hLDK, hfrQζ, hfrKq]
    ring
  rw [h2] at h1
  exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h1

/-- **A Frobenius at `𝔭` raises a primitive `M`-th root of unity to the `N𝔭`-th power.** -/
theorem isFrobAt_zeta_pow (M : ℕ) [NeZero M] {ζ : CyclotomicField M L}
    (hζ : IsPrimitiveRoot ζ M) (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h𝔭M : (M : 𝓞 K) ∉ 𝔭.asIdeal)
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 (CyclotomicField M L)))
    (hP : P.asIdeal.LiesOver 𝔭.asIdeal) (F : Gal(CyclotomicField M L/K))
    (hF : NK.Chebotarev.IsFrobAt (K := K) (L := CyclotomicField M L) P F) :
    F ζ = ζ ^ Ideal.absNorm 𝔭.asIdeal := by
  have hζint : IsPrimitiveRoot hζ.toInteger M := hζ.toInteger_isPrimitiveRoot
  have hcoe : algebraMap (𝓞 (CyclotomicField M L)) (CyclotomicField M L) hζ.toInteger = ζ :=
    hζ.coe_toInteger
  have hMP : (M : 𝓞 (CyclotomicField M L)) ∉ P.asIdeal := by
    intro hmem
    apply h𝔭M
    have h' : algebraMap (𝓞 K) (𝓞 (CyclotomicField M L)) (M : 𝓞 K) ∈ P.asIdeal := by
      rwa [map_natCast]
    exact (Ideal.mem_of_liesOver (P := P.asIdeal) (p := 𝔭.asIdeal) (x := (M : 𝓞 K))).mpr h'
  have h1 : galRestrict (𝓞 K) K (CyclotomicField M L) (𝓞 (CyclotomicField M L)) F
        hζ.toInteger
      = hζ.toInteger ^ Nat.card (𝓞 K ⧸ P.asIdeal.under (𝓞 K)) :=
    AlgHom.IsArithFrobAt.apply_of_pow_eq_one hF hζint.pow_eq_one hMP
  have h2 := congrArg (algebraMap (𝓞 (CyclotomicField M L)) (CyclotomicField M L)) h1
  rw [map_pow, algebraMap_galRestrict_apply] at h2
  rw [hcoe, ← hP.over] at h2
  have habs : Nat.card (𝓞 K ⧸ 𝔭.asIdeal) = Ideal.absNorm 𝔭.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rwa [habs] at h2

/-- **`[L(ζ_M) : K] = [L : K] · φ(M)`** for `M` coprime to the discriminant of `L`. -/
theorem finrank_cyclotomicField_eq (M : ℕ) [NeZero M]
    (hM : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr L).natAbs) :
    Module.finrank K (CyclotomicField M L) = Module.finrank K L * M.totient := by
  classical
  set Ω := CyclotomicField M L
  set ζ := IsCyclotomicExtension.zeta M L Ω with hζ
  have hζprim : IsPrimitiveRoot ζ M := IsCyclotomicExtension.zeta_spec M L Ω
  haveI : IsGalois K Ω := NK.CFTLib.ARL.isGalois_cyclotomicField_over_base (K := K) (L := L) M
  have hMK : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr K).natAbs := by
    intro p hp hpm hpd
    exact hM p hp hpm (dvd_trans hpd (Int.natAbs_dvd_natAbs.mpr (NumberField.discr_dvd_discr K L)))
  set A : IntermediateField K Ω := (⊥ : IntermediateField L Ω).restrictScalars K with hA
  set B : IntermediateField K Ω := IntermediateField.adjoin K ({ζ} : Set Ω) with hB
  have hdisj : A ⊓ B = ⊥ := by
    rw [hA, hB]
    exact disjoint_iff.mp (NK.CFTLib.ARL.disjoint_restrictScalars_adjoin_zeta
      (K := K) (L := L) M hM)
  have hsup : A ⊔ B = ⊤ := by
    rw [hA, hB]
    exact sup_restrictScalars_adjoin_zeta_eq_top (K := K) (L := L) M
  have hAeq : (IsScalarTower.toAlgHom K L Ω).fieldRange = A := by
    apply SetLike.ext
    intro x
    rw [AlgHom.mem_fieldRange]
    constructor
    · rintro ⟨y, rfl⟩
      rw [hA]
      exact (IntermediateField.mem_restrictScalars K).mpr
        ((IntermediateField.mem_bot).mpr ⟨y, rfl⟩)
    · intro hx
      rw [hA] at hx
      obtain ⟨y, hy⟩ := (IntermediateField.mem_bot).mp
        ((IntermediateField.mem_restrictScalars K).mp hx)
      exact ⟨y, hy⟩
  have hAL : L ≃ₐ[K] ↥((IsScalarTower.toAlgHom K L Ω).fieldRange) :=
    AlgEquiv.ofInjective (IsScalarTower.toAlgHom K L Ω)
      (FaithfulSMul.algebraMap_injective L Ω)
  haveI hAgal : IsGalois K ↥A := by
    rw [← hAeq]
    exact IsGalois.of_algEquiv hAL
  have hfrA : Module.finrank K ↥A = Module.finrank K L := by
    rw [← hAeq]
    exact hAL.toLinearEquiv.symm.finrank_eq
  have hfrB : Module.finrank K ↥B = M.totient := by
    rw [hB]
    exact finrank_adjoin_zeta_eq_totient (K := K) (Ω := Ω) M hMK ζ hζprim
  have hfr := IntermediateField.LinearDisjoint.finrank_sup
    (IntermediateField.LinearDisjoint.of_inf_eq_bot hdisj)
  rw [hsup] at hfr
  have htop : Module.finrank K ↥(⊤ : IntermediateField K Ω) = Module.finrank K Ω :=
    (IntermediateField.topEquiv (F := K) (E := Ω)).toLinearEquiv.finrank_eq
  rw [htop, hfrA, hfrB] at hfr
  exact hfr

/-- If `E ⊔ K(ζ_M) = ⊤` then `E ⊔ ℚ(ζ_M) = ⊤` as well (both are subfields of `L(ζ_M)`).

Since `E ⊇ K` and `K(ζ_M) = K·ℚ(ζ_M)`, the composita `E·K(ζ_M) = E·ℚ(ζ_M)` computed in `L(ζ_M)`
agree. -/
theorem restrictScalars_rat_sup_adjoin_zeta_eq_top (M : ℕ) [NeZero M]
    (E : IntermediateField K (CyclotomicField M L))
    (h : E ⊔ IntermediateField.adjoin K
        ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} :
          Set (CyclotomicField M L)) = ⊤) :
    (E.restrictScalars ℚ) ⊔ IntermediateField.adjoin ℚ
        ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} :
          Set (CyclotomicField M L)) = ⊤ := by
  set Ω := CyclotomicField M L
  set ζ := IsCyclotomicExtension.zeta M L Ω with hζdef
  -- the composite `E·K(ζ)` computed over `ℚ`
  have hX : E.restrictScalars ℚ ⊔
      (IntermediateField.adjoin K ({ζ} : Set Ω)).restrictScalars ℚ = ⊤ := by
    rw [IntermediateField.restrictScalars_sup (K := ℚ) E
      (IntermediateField.adjoin K ({ζ} : Set Ω)), h, IntermediateField.restrictScalars_top]
  -- `adjoin K {ζ} ⊆ E ⊔ ℚ(ζ)`, since `K ⊆ E`
  have hKW : (IntermediateField.adjoin K ({ζ} : Set Ω)).restrictScalars ℚ ≤
      E.restrictScalars ℚ ⊔ IntermediateField.adjoin ℚ ({ζ} : Set Ω) := by
    intro x hx
    have hset : (IntermediateField.adjoin K ({ζ} : Set Ω) : Set Ω) ⊆
        ((E.restrictScalars ℚ ⊔ IntermediateField.adjoin ℚ ({ζ} : Set Ω) :
          IntermediateField ℚ Ω) : Set Ω) := by
      rw [show ((E.restrictScalars ℚ ⊔ IntermediateField.adjoin ℚ ({ζ} : Set Ω) :
            IntermediateField ℚ Ω) : Set Ω) =
          (IntermediateField.adjoin ℚ
            (((E.restrictScalars ℚ ⊔ IntermediateField.adjoin ℚ ({ζ} : Set Ω) :
              IntermediateField ℚ Ω)) : Set Ω) : Set Ω) from by
        rw [IntermediateField.adjoin_self]]
      rw [IntermediateField.adjoin_subset_adjoin_iff]
      refine ⟨?_, ?_⟩
      · rintro y ⟨k, rfl⟩
        refine IntermediateField.subset_adjoin ℚ _ ?_
        exact (le_sup_left : (E.restrictScalars ℚ : IntermediateField ℚ Ω) ≤
          (E.restrictScalars ℚ ⊔ IntermediateField.adjoin ℚ ({ζ} : Set Ω) :
            IntermediateField ℚ Ω)) (E.algebraMap_mem k)
      · intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        refine IntermediateField.subset_adjoin ℚ _ ?_
        exact (le_sup_right : (IntermediateField.adjoin ℚ ({ζ} : Set Ω) : IntermediateField ℚ Ω) ≤
          (E.restrictScalars ℚ ⊔ IntermediateField.adjoin ℚ ({ζ} : Set Ω) :
            IntermediateField ℚ Ω))
          (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton ζ))
    exact hset hx
  refine le_antisymm le_top ?_
  rw [← hX]
  simpa [sup_assoc, sup_idem] using sup_le_sup_left hKW (E.restrictScalars ℚ)

/-- **The Galois group of `L(ζ_M)/K` is the product of `Gal(L/K)` and `(ℤ/M)ˣ`.**

The two components of the isomorphism are restriction to `L` and the cyclotomic character
`ζ ↦ ζ ^ k`; the statement records both, so the isomorphism is determined by its action. -/
theorem exists_prod_iso_cyclotomic (M : ℕ) [NeZero M]
    (hM : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr L).natAbs) :
    ∃ Ψe : Gal(CyclotomicField M L / K) ≃* (Gal(L/K) × (ZMod M)ˣ),
      (∀ (σ : Gal(CyclotomicField M L / K)),
        (Ψe σ).1 = AlgEquiv.restrictNormalHom (F := K) (K₁ := CyclotomicField M L) L σ) ∧
      (∀ (σ : Gal(CyclotomicField M L / K)),
        (Ψe σ).2 = (IsCyclotomicExtension.zeta_spec M L (CyclotomicField M L)).autToPow K σ) := by
  classical
  set Ω := CyclotomicField M L
  set ζ := IsCyclotomicExtension.zeta M L Ω with hζdef
  have hζ : IsPrimitiveRoot ζ M := IsCyclotomicExtension.zeta_spec M L Ω
  haveI hgalΩ : IsGalois K Ω := NK.CFTLib.ARL.isGalois_cyclotomicField_over_base (K := K) (L := L) M
  let ρ : Gal(Ω/K) →* Gal(L/K) := AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L
  let χ : Gal(Ω/K) →* (ZMod M)ˣ := hζ.autToPow K
  let Ψ : Gal(Ω/K) →* Gal(L/K) × (ZMod M)ˣ := ρ.prod χ
  have hΨinj : Function.Injective Ψ := by
    rintro x y hxy
    have hρ : ρ x = ρ y := congrArg Prod.fst hxy
    have hχ : χ x = χ y := congrArg Prod.snd hxy
    have htopadjoin : Algebra.adjoin K (Set.range (algebraMap L Ω) ∪ {ζ}) = ⊤ := by
      have hsup : (⊥ : IntermediateField L Ω).restrictScalars K ⊔
          IntermediateField.adjoin K ({ζ} : Set Ω) = ⊤ :=
        sup_restrictScalars_adjoin_zeta_eq_top (K := K) (L := L) M
      have hgen : IntermediateField.adjoin K (Set.range (algebraMap L Ω) ∪ {ζ}) = ⊤ := by
        rw [eq_top_iff, ← hsup]
        refine sup_le ?_ ?_
        · intro w hw
          have hw' : w ∈ (⊥ : IntermediateField L Ω) :=
            (IntermediateField.mem_restrictScalars K).mp hw
          exact IntermediateField.subset_adjoin K _
            (Or.inl (IntermediateField.mem_bot.mp hw'))
        · exact le_of_le_of_eq (IntermediateField.adjoin.mono K _ _
            (Set.subset_union_right : ({ζ} : Set Ω) ⊆ _)) rfl
      rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (F := K)
        (S := Set.range (algebraMap L Ω) ∪ {ζ}) (fun w _ => Algebra.IsAlgebraic.isAlgebraic w),
        hgen]
      rfl
    have halg : (x : Ω →ₐ[K] Ω) = (y : Ω →ₐ[K] Ω) := by
      refine AlgHom.ext_of_adjoin_eq_top (R := K) htopadjoin ?_
      rintro w (⟨l, rfl⟩ | hw)
      · rw [show (x : Ω →ₐ[K] Ω) (algebraMap L Ω l) = algebraMap L Ω ((ρ x) l) from
            (AlgEquiv.restrictNormal_commutes (F := K) (K₁ := Ω) (K₂ := Ω) x L l).symm,
          show (y : Ω →ₐ[K] Ω) (algebraMap L Ω l) = algebraMap L Ω ((ρ y) l) from
            (AlgEquiv.restrictNormal_commutes (F := K) (K₁ := Ω) (K₂ := Ω) y L l).symm,
          hρ]
      · rw [Set.mem_singleton_iff] at hw
        subst hw
        rw [show (x : Ω →ₐ[K] Ω) ζ = ζ ^ ((χ x : (ZMod M)ˣ) : ZMod M).val from
              (IsPrimitiveRoot.autToPow_spec K hζ x).symm,
          show (y : Ω →ₐ[K] Ω) ζ = ζ ^ ((χ y : (ZMod M)ˣ) : ZMod M).val from
              (IsPrimitiveRoot.autToPow_spec K hζ y).symm, hχ]
    exact AlgEquiv.ext (fun z => AlgHom.congr_fun halg z)
  have hcard : Nat.card (Gal(Ω/K)) = Nat.card (Gal(L/K) × (ZMod M)ˣ) := by
    rw [IsGalois.card_aut_eq_finrank K Ω,
      finrank_cyclotomicField_eq (K := K) (L := L) M hM, Nat.card_prod,
      IsGalois.card_aut_eq_finrank K L, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  haveI : Fintype (Gal(Ω/K)) := Fintype.ofFinite _
  haveI : Fintype (Gal(L/K) × (ZMod M)ˣ) := Fintype.ofFinite _
  have hΨbij : Function.Bijective Ψ := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hΨinj, by rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]; exact hcard⟩
  refine ⟨MulEquiv.ofBijective Ψ hΨbij, ?_, ?_⟩
  · intro σ
    rw [MulEquiv.ofBijective_apply]
    rfl
  · intro σ
    rw [MulEquiv.ofBijective_apply]
    rfl

/-- A power of an element fixing `a` still fixes `a`. -/
lemma zpow_apply_fixed {F E : Type*} [Field F] [Field E] [Algebra F E] (x : E ≃ₐ[F] E)
    {a : E} (h : x a = a) : ∀ k : ℤ, (x ^ k) a = a := by
  have hinv : x⁻¹ a = a := by
    have := congrArg (fun y => x⁻¹ y) h
    simpa using this.symm
  intro k
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih => rw [zpow_add_one, AlgEquiv.mul_apply, h, ih]
  | pred n ih => rw [zpow_sub_one, AlgEquiv.mul_apply, hinv, ih]

/-- **Independence of two elements of a finite abelian group with the expected orders.**

If `n ∣ orderOf a`, `n ∣ orderOf b`, and every relation `a ^ i * b ^ j = 1` with `i j` natural
forces `n ∣ i` and `n ∣ j`, then the same is true for integer exponents. -/
lemma int_dvd_of_zpow_mul_eq_one {n : ℕ} (hn : 0 < n) {H : Type*} [CommGroup H] {a b : H}
    (ha0 : orderOf a ≠ 0) (hb0 : orderOf b ≠ 0)
    (ha : n ∣ orderOf a) (hb : n ∣ orderOf b)
    (hind : ∀ i j : ℕ, a ^ i * b ^ j = 1 → n ∣ i ∧ n ∣ j) (i j : ℤ)
    (h : a ^ i * b ^ j = 1) : (n : ℤ) ∣ i ∧ (n : ℤ) ∣ j := by
  have hNa : (orderOf a : ℤ) ≠ 0 := by exact_mod_cast ha0
  have hNb : (orderOf b : ℤ) ≠ 0 := by exact_mod_cast hb0
  have hai : a ^ i = a ^ ((i % (orderOf a : ℤ)).toNat) := by
    rw [zpow_eq_zpow_emod' i (pow_orderOf_eq_one a), ← zpow_natCast,
      Int.toNat_of_nonneg (Int.emod_nonneg i hNa)]
  have hbj : b ^ j = b ^ ((j % (orderOf b : ℤ)).toNat) := by
    rw [zpow_eq_zpow_emod' j (pow_orderOf_eq_one b), ← zpow_natCast,
      Int.toNat_of_nonneg (Int.emod_nonneg j hNb)]
  have h0 : a ^ ((i % (orderOf a : ℤ)).toNat) * b ^ ((j % (orderOf b : ℤ)).toNat) = 1 := by
    rw [← hai, ← hbj, h]
  obtain ⟨hi0, hj0⟩ := hind _ _ h0
  have hia : ((i % (orderOf a : ℤ)).toNat : ℤ) = i % (orderOf a : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg i hNa)
  have hjb : ((j % (orderOf b : ℤ)).toNat : ℤ) = j % (orderOf b : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg j hNb)
  have hdiva : (n : ℤ) ∣ i % (orderOf a : ℤ) := by
    rw [← hia]; exact_mod_cast hi0
  have hdivb : (n : ℤ) ∣ j % (orderOf b : ℤ) := by
    rw [← hjb]; exact_mod_cast hj0
  constructor
  · have hN : (n : ℤ) ∣ (orderOf a : ℤ) := by exact_mod_cast ha
    have h2 : (n : ℤ) ∣ (i / (orderOf a : ℤ)) * (orderOf a : ℤ) := hN.mul_left _
    have h3 : (n : ℤ) ∣ i / (orderOf a : ℤ) * (orderOf a : ℤ) + i % (orderOf a : ℤ) :=
      dvd_add h2 hdiva
    rwa [Int.ediv_mul_add_emod] at h3
  · have hN : (n : ℤ) ∣ (orderOf b : ℤ) := by exact_mod_cast hb
    have h2 : (n : ℤ) ∣ (j / (orderOf b : ℤ)) * (orderOf b : ℤ) := hN.mul_left _
    have h3 : (n : ℤ) ∣ j / (orderOf b : ℤ) * (orderOf b : ℤ) + j % (orderOf b : ℤ) :=
      dvd_add h2 hdivb
    rwa [Int.ediv_mul_add_emod] at h3

end NK.CFTLib.Existence
