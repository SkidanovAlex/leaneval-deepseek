import Mathlib
import Submission.NK.Chebotarev.Basic
import Submission.NK.Chebotarev.FrobeniusOne
import Submission.NK.Chebotarev.IsFrobAtOrderOfEqInertiaDeg
import Submission.NK.Chebotarev.IsFrobAtRestrictNormalHom
import Submission.NK.CFTLib.ARL.exists_mod_order_independent
import Submission.NK.CFTLib.ARL.disjoint_restrictScalars_adjoin_zeta
import Submission.NK.CFTLib.ARL.isFrobAtPrime_zeta
import Submission.NK.CFTLib.ARL.autToPow_eq_of_pow_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NumberField IsDedekindDomain
open scoped NumberField

namespace NK.CFTLib.ARL

noncomputable section

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

/-- **`L(ζ_M) = L ⊔ F(ζ_M)`** for any base field `F` below `L`. -/
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

/-- **`CyclotomicField M L` is Galois over `K`** when `L/K` is finite Galois. -/
theorem isGalois_cyclotomicField (M : ℕ) [NeZero M] :
    IsGalois K (CyclotomicField M L) := by
  set Ω := CyclotomicField M L
  set ζ := IsCyclotomicExtension.zeta M L Ω with hζ
  set A : IntermediateField K Ω :=
    (⊥ : IntermediateField L Ω).restrictScalars K with hA
  set B : IntermediateField K Ω :=
    IntermediateField.adjoin K ({ζ} : Set Ω) with hB
  have hsup : A ⊔ B = ⊤ := sup_restrictScalars_adjoin_zeta_eq_top (K := K) (L := L) M
  have hArange : (IsScalarTower.toAlgHom K L Ω).fieldRange = A := by
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
  haveI hAgal : IsGalois K ↥A := by
    rw [← hArange]
    exact IsGalois.of_algEquiv (AlgEquiv.ofInjective (IsScalarTower.toAlgHom K L Ω)
      (FaithfulSMul.algebraMap_injective L Ω))
  haveI hBcyc : IsCyclotomicExtension {M} K ↥B := by
    rw [hB]
    exact (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin M K Ω _
      (IsCyclotomicExtension.zeta_spec M L Ω)).mpr rfl
  haveI hBgal : IsGalois K ↥B := IsCyclotomicExtension.isGalois {M} K ↥B
  have hN : Normal K (A ⊔ B : IntermediateField K Ω) := by
    haveI : Normal K A := hAgal.to_normal
    haveI : Normal K B := hBgal.to_normal
    exact inferInstance
  have hNtop : Normal K (⊤ : IntermediateField K Ω) := hsup ▸ hN
  have hSepTop : Algebra.IsSeparable K (⊤ : IntermediateField K Ω) := inferInstance
  haveI : IsGalois K ↥(⊤ : IntermediateField K Ω) := isGalois_iff.mpr ⟨hSepTop, hNtop⟩
  exact IsGalois.of_algEquiv (IntermediateField.topEquiv (F := K))

/-- **The degree of `L(ζ_M)` over `K`**: `[L(ζ_M) : K] = [L : K] · φ(M)` for `M` coprime to
the discriminant of `L`. -/
lemma finrank_cyclotomicField_eq (M : ℕ) [NeZero M]
    (hM : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr L).natAbs) :
    Module.finrank K (CyclotomicField M L) = Module.finrank K L * M.totient := by
  set Ω := CyclotomicField M L
  set ζ := IsCyclotomicExtension.zeta M L Ω with hζ
  have hζprim : IsPrimitiveRoot ζ M := IsCyclotomicExtension.zeta_spec M L Ω
  set Qζ : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ ({ζ} : Set Ω) with hQζ
  set Lq : IntermediateField ℚ Ω := (⊥ : IntermediateField L Ω).restrictScalars ℚ with hLq
  have hdisjL : Qζ ⊓ Lq = ⊥ := by
    rw [hQζ, hLq]
    exact intersect_cyclotomic_eq_bot_gen (F := L) M hM ζ hζprim
  haveI hQζcyc : IsCyclotomicExtension {M} ℚ ↥Qζ := by
    rw [hQζ]
    exact (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin M ℚ Ω _
      hζprim).mpr rfl
  haveI hQζgal : IsGalois ℚ ↥Qζ := IsCyclotomicExtension.isGalois {M} ℚ ↥Qζ
  haveI hQζfd : FiniteDimensional ℚ ↥Qζ := by
    rw [hQζ]
    exact IntermediateField.finiteDimensional_adjoin (S := ({ζ} : Set Ω)) (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      exact hx ▸ (hζprim.isIntegral (NeZero.pos M)).tower_top)
  have hfrQζ : Module.finrank ℚ ↥Qζ = M.totient := by
    rw [IsCyclotomicExtension.finrank ↥Qζ (Polynomial.cyclotomic.irreducible_rat (NeZero.pos M))]
  haveI hLqfd : FiniteDimensional ℚ ↥Lq := by
    rw [hLq]
    exact FiniteDimensional.trans ℚ L ↥(⊥ : IntermediateField L Ω)
  have hsup : Qζ ⊔ Lq = ⊤ := by
    rw [hQζ, hLq, sup_comm]
    exact sup_restrictScalars_adjoin_zeta_eq_top_rat M
  have hLD : Qζ.LinearDisjoint ↥Lq :=
    @IntermediateField.LinearDisjoint.of_inf_eq_bot ℚ Ω _ _ _ Qζ Lq hQζgal hQζfd hLqfd hdisjL
  have hfrLq : Module.finrank ℚ ↥Lq = Module.finrank ℚ L := by
    change Module.finrank ℚ ↥(⊥ : IntermediateField L Ω) = Module.finrank ℚ L
    rw [← Module.finrank_mul_finrank ℚ L ↥(⊥ : IntermediateField L Ω),
      (IntermediateField.botEquiv L Ω).toLinearEquiv.finrank_eq, Module.finrank_self, mul_one]
  have htop : Module.finrank ℚ ↥(⊤ : IntermediateField ℚ Ω) = Module.finrank ℚ Ω :=
    (IntermediateField.topEquiv (F := ℚ) (E := Ω)).toLinearEquiv.finrank_eq
  have hfr : Module.finrank ℚ Ω = M.totient * Module.finrank ℚ L := by
    rw [← htop, ← hsup, IntermediateField.LinearDisjoint.finrank_sup hLD, hfrQζ, hfrLq]
  have h1 : Module.finrank ℚ L * Module.finrank L Ω = Module.finrank ℚ Ω :=
    Module.finrank_mul_finrank ℚ L Ω
  have h3 : Module.finrank ℚ L * Module.finrank L Ω = Module.finrank ℚ L * M.totient := by
    rw [h1, hfr, mul_comm]
  have h2 : Module.finrank L Ω = M.totient :=
    Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := ℚ) (M := L)) h3
  rw [← Module.finrank_mul_finrank K L Ω, h2]

/-- **Arithmetic input of Artin's lemma.** -/
theorem exists_mod_data (n a : ℕ) (ha : 1 < a) (hn : 0 < n) (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime) (haT : ∀ p : ℕ, p.Prime → p ∣ a → p ∈ T) :
    ∃ M b : ℕ, 1 < M ∧ (∀ p ∈ T, ¬ p ∣ M) ∧ (∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ b) ∧
      (∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ a) ∧
      n ∣ orderOf ((a : ZMod M)) ∧ n ∣ orderOf ((b : ZMod M)) ∧
      (∀ i j : ℕ, (a : ZMod M) ^ i * (b : ZMod M) ^ j = 1 → n ∣ i ∧ n ∣ j) := by
  obtain ⟨M, b, hM0, hMT, hMa0, hMb, hordA, hordB, hind⟩ :=
    exists_mod_order_independent (2 * n) a ha (by omega) T hT
  have hM1 : 1 < M := by
    by_contra hcon
    have hM1' : M = 1 := by omega
    haveI : Subsingleton (ZMod M) := ZMod.subsingleton_iff.mpr hM1'
    have h1 : orderOf ((a : ZMod M)) = 1 := orderOf_eq_one_iff.mpr (Subsingleton.elim _ _)
    rw [h1] at hordA
    have := Nat.le_of_dvd (by norm_num) hordA
    omega
  have hMa : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ a := by
    intro p hp hpM hpa
    exact hMT p (haT p hp hpa) hpM
  have haunit : IsUnit ((a : ZMod M)) := by
    rw [ZMod.isUnit_iff_coprime]
    by_contra hc
    obtain ⟨p, hp, hpa, hpM⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    exact hMa p hp hpM hpa
  have hbunit : IsUnit ((b : ZMod M)) := by
    rw [ZMod.isUnit_iff_coprime]
    by_contra hc
    obtain ⟨p, hp, hpb, hpM⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    exact hMb p hp hpM hpb
  refine ⟨M, b, hM1, hMT, hMb, hMa,
    dvd_trans (dvd_mul_left n 2) hordA, dvd_trans (dvd_mul_left n 2) hordB, ?_⟩
  intro i j hij
  let A : (ZMod M)ˣ := haunit.unit
  let B : (ZMod M)ˣ := hbunit.unit
  have hA : ((A : (ZMod M)ˣ) : ZMod M) = (a : ZMod M) := IsUnit.unit_spec haunit
  have hB : ((B : (ZMod M)ˣ) : ZMod M) = (b : ZMod M) := IsUnit.unit_spec hbunit
  have hij' : A ^ i * B ^ j = 1 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_one, hA, hB]
    exact hij
  have hBpos : 0 < orderOf B := by
    rw [← Nat.card_zpowers]
    exact Nat.card_pos
  have hBpow : B ^ (j * orderOf B) = 1 := by
    rw [mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  have hle : j ≤ j * orderOf B := Nat.le_mul_of_pos_right j hBpos
  have hsplit : B ^ (j * orderOf B - j) * B ^ j = B ^ (j * orderOf B) := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  have haux : B ^ (j * orderOf B - j) = (B ^ j)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, hsplit, hBpow]
  have hA1 : A ^ i = 1 := by
    have h1 : A ^ i = (B ^ j)⁻¹ := (eq_inv_iff_mul_eq_one).mpr hij'
    have h2 : A ^ i = B ^ (j * orderOf B - j) := by rw [h1, haux]
    have h3 : (a : ZMod M) ^ i = (b : ZMod M) ^ (j * orderOf B - j) := by
      have hc := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) h2
      simpa only [Units.val_pow_eq_pow_val, hA, hB] using hc
    have h4 := hind i (j * orderOf B - j) h3
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, hA]
    exact h4
  have hB1 : B ^ j = 1 := by
    rw [hA1, one_mul] at hij'
    exact hij'
  have hordAeq : orderOf A = orderOf ((a : ZMod M)) := by
    rw [← orderOf_units (y := A), hA]
  have hordBeq : orderOf B = orderOf ((b : ZMod M)) := by
    rw [← orderOf_units (y := B), hB]
  exact ⟨dvd_trans (dvd_trans (dvd_mul_left n 2) hordA)
      (hordAeq ▸ orderOf_dvd_iff_pow_eq_one.mpr hA1),
    dvd_trans (dvd_trans (dvd_mul_left n 2) hordB)
      (hordBeq ▸ orderOf_dvd_iff_pow_eq_one.mpr hB1)⟩

/-- The absolute norm of a prime ideal of a number field is at least `2`. -/
theorem one_lt_absNorm_heightOneSpectrum (K : Type*) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : 1 < Ideal.absNorm 𝔭.asIdeal := by
  haveI : 𝔭.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal 𝔭.isPrime 𝔭.ne_bot
  haveI : Field (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.Quotient.field 𝔭.asIdeal
  haveI : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot 𝔭.asIdeal 𝔭.ne_bot
  haveI : Fintype (𝓞 K ⧸ 𝔭.asIdeal) := Fintype.ofFinite _
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

/-- **A Frobenius at `𝔭` raises a primitive `M`-th root of unity to the `N𝔭`-th power.** -/
theorem isFrobAt_zeta_pow (M : ℕ) [NeZero M] {ζ : CyclotomicField M L}
    (hζ : IsPrimitiveRoot ζ M) (𝔭 : HeightOneSpectrum (𝓞 K))
    (h𝔭M : (M : 𝓞 K) ∉ 𝔭.asIdeal)
    (P : HeightOneSpectrum (𝓞 (CyclotomicField M L)))
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

/-- The finite set of rational primes which the auxiliary modulus must avoid. -/
def avoidSet (m a : ℕ) (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    (S : Finset ℕ) : Finset ℕ :=
  S ∪ m.primeFactors ∪ a.primeFactors ∪ (NumberField.discr K).natAbs.primeFactors ∪
    (NumberField.discr L).natAbs.primeFactors

lemma mem_avoidSet_of_mem_S {m a : ℕ} {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] {S : Finset ℕ} {p : ℕ} (h : p ∈ S) : p ∈ avoidSet m a K L S := by
  rw [avoidSet]
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_union_left _ h)))

lemma mem_avoidSet_of_dvd_m {m a : ℕ} {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] {S : Finset ℕ} {p : ℕ} (hp : p.Prime) (hm : m ≠ 0) (h : p ∣ m) :
    p ∈ avoidSet m a K L S := by
  rw [avoidSet]
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, h, hm⟩))))

lemma mem_avoidSet_of_dvd_a {m a : ℕ} {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] {S : Finset ℕ} {p : ℕ} (hp : p.Prime) (ha : a ≠ 0) (h : p ∣ a) :
    p ∈ avoidSet m a K L S := by
  rw [avoidSet]
  exact Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, h, ha⟩)))

lemma mem_avoidSet_of_dvd_discK {m a : ℕ} {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] {S : Finset ℕ} {p : ℕ} (hp : p.Prime)
    (h : p ∣ (NumberField.discr K).natAbs) : p ∈ avoidSet m a K L S := by
  rw [avoidSet]
  exact Finset.mem_union_left _ (Finset.mem_union_right _
    (Nat.mem_primeFactors.mpr ⟨hp, h, (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)).ne'⟩))

lemma mem_avoidSet_of_dvd_discL {m a : ℕ} {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] {S : Finset ℕ} {p : ℕ} (hp : p.Prime)
    (h : p ∣ (NumberField.discr L).natAbs) : p ∈ avoidSet m a K L S := by
  rw [avoidSet]
  exact Finset.mem_union_right _
    (Nat.mem_primeFactors.mpr ⟨hp, h, (Int.natAbs_pos.mpr (NumberField.discr_ne_zero L)).ne'⟩)

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

/-- **Independence in a finite abelian group, with integer exponents.** -/
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
end


variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

theorem auxiliary_field_single {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] (m : ℕ)
    (hm : 0 < m) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h𝔭 : (m : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal) :
    ∃ (M : ℕ) (_ : NeZero M), M.Coprime m ∧ (∀ p ∈ S, ¬ p ∣ M) ∧
      (∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ Ideal.absNorm 𝔭.asIdeal) ∧
      Disjoint ((⊥ : IntermediateField L (CyclotomicField M L)).restrictScalars K)
        (IntermediateField.adjoin K
          ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} :
            Set (CyclotomicField M L))) ∧
      ∃ E : IntermediateField K (CyclotomicField M L),
        Disjoint E ((⊥ : IntermediateField L (CyclotomicField M L)).restrictScalars K) ∧
        (E.restrictScalars ℚ) ⊔ (IntermediateField.adjoin ℚ
          ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} :
            Set (CyclotomicField M L))) = ⊤ ∧
        NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥E) 𝔭 1 := by
  classical
  -- ## Step 0: numerology
  have hnpos : 0 < Nat.card (L ≃ₐ[K] L) := by
    rw [IsGalois.card_aut_eq_finrank K L]
    exact Module.finrank_pos
  obtain ⟨σ, hσgen⟩ := IsCyclic.exists_generator (α := (L ≃ₐ[K] L))
  have ha : 1 < Ideal.absNorm 𝔭.asIdeal := one_lt_absNorm_heightOneSpectrum K 𝔭
  -- ## Step 1: the arithmetic data
  set T : Finset ℕ := avoidSet m (Ideal.absNorm 𝔭.asIdeal) K L S with hTdef
  have hTprime : ∀ p ∈ T, p.Prime := by
    intro p hp
    rw [hTdef, avoidSet] at hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · rcases Finset.mem_union.mp hp with hp | hp
        · rcases Finset.mem_union.mp hp with hp | hp
          · exact hS p hp
          · exact Nat.prime_of_mem_primeFactors hp
        · exact Nat.prime_of_mem_primeFactors hp
      · exact Nat.prime_of_mem_primeFactors hp
    · exact Nat.prime_of_mem_primeFactors hp
  obtain ⟨M, b, hM1, hMT, hMb, hMa, hordA, hordB, hindM⟩ :=
    exists_mod_data (Nat.card (L ≃ₐ[K] L)) (Ideal.absNorm 𝔭.asIdeal) ha hnpos T hTprime
      (fun p hp hpa => by rw [hTdef]; exact mem_avoidSet_of_dvd_a hp (by omega) hpa)
  haveI hMne : NeZero M := ⟨by omega⟩
  have hMdiscL : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr L).natAbs := by
    intro p hp hpM hpd
    exact hMT p (by rw [hTdef]; exact mem_avoidSet_of_dvd_discL hp hpd) hpM
  refine ⟨M, hMne, ?_, ?_, ?_, ?_, ?_⟩
  · -- `M` is coprime to `m`
    by_contra hc
    obtain ⟨p, hp, hpM, hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    exact hMT p (by rw [hTdef]; exact mem_avoidSet_of_dvd_m hp hm.ne' hpm) hpM
  · exact fun p hp hpM => hMT p (by rw [hTdef]; exact mem_avoidSet_of_mem_S hp) hpM
  · intro p hp hpM hpa
    exact hMT p (by rw [hTdef]; exact mem_avoidSet_of_dvd_a hp (by omega) hpa) hpM
  · -- `L ∩ K(ζ_M) = K`
    exact disjoint_restrictScalars_adjoin_zeta (K := K) (L := L) M hMdiscL
  · -- ## The auxiliary field
    set Ω := CyclotomicField M L
    set ζ := IsCyclotomicExtension.zeta M L Ω with hζdef
    have hζ : IsPrimitiveRoot ζ M := IsCyclotomicExtension.zeta_spec M L Ω
    haveI hgalΩ : IsGalois K Ω := isGalois_cyclotomicField (K := K) (L := L) M
    -- the character `Ψ = (ρ, χ)`
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
        finrank_cyclotomicField_eq (K := K) (L := L) M hMdiscL, Nat.card_prod,
        IsGalois.card_aut_eq_finrank K L, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    haveI : Fintype (Gal(Ω/K)) := Fintype.ofFinite _
    haveI : Fintype (Gal(L/K) × (ZMod M)ˣ) := Fintype.ofFinite _
    have hΨbij : Function.Bijective Ψ := by
      rw [Fintype.bijective_iff_injective_and_card]
      exact ⟨hΨinj, by rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]; exact hcard⟩
    let Ψe : Gal(Ω/K) ≃* Gal(L/K) × (ZMod M)ˣ := MulEquiv.ofBijective Ψ hΨbij
    -- ## the auxiliary element `σ̃`
    have hbunit : IsUnit ((b : ZMod M)) := by
      rw [ZMod.isUnit_iff_coprime]
      by_contra hc
      obtain ⟨p, hp, hpb, hpM⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
      exact hMb p hp hpM hpb
    let bu : (ZMod M)ˣ := hbunit.unit
    have hbuval : ((bu : (ZMod M)ˣ) : ZMod M) = (b : ZMod M) := IsUnit.unit_spec hbunit
    let σtilde : Gal(Ω/K) := Ψe.symm (σ, bu)
    have hΨσtilde : Ψ σtilde = (σ, bu) := Ψe.apply_symm_apply (σ, bu)
    have hρσtilde : ρ σtilde = σ := by
      rw [show ρ σtilde = (Ψ σtilde).1 from rfl, hΨσtilde]
    have hχσtilde : χ σtilde = bu := by
      rw [show χ σtilde = (Ψ σtilde).2 from rfl, hΨσtilde]
    -- ## the Frobenius element
    obtain ⟨P, hP⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := Ω) 𝔭
    obtain ⟨F, hF⟩ := NK.Chebotarev.exists_isFrobAt (K := K) (L := Ω) 𝔭 P hP
    have hM_p : (M : 𝓞 K) ∉ 𝔭.asIdeal := by
      intro hmem
      haveI : 𝔭.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal 𝔭.isPrime 𝔭.ne_bot
      haveI hfld : Field (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.Quotient.field 𝔭.asIdeal
      haveI hfin : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot 𝔭.asIdeal 𝔭.ne_bot
      haveI hft : Fintype (𝓞 K ⧸ 𝔭.asIdeal) := Fintype.ofFinite _
      have hMzero : ((M : ℕ) : 𝓞 K ⧸ 𝔭.asIdeal) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk 𝔭.asIdeal) M]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      have hpM : ringChar (𝓞 K ⧸ 𝔭.asIdeal) ∣ M := ringChar.dvd hMzero
      have hpcop : Nat.Coprime M (Ideal.absNorm 𝔭.asIdeal) := by
        by_contra hc
        obtain ⟨q, hq, hqM, hqa⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
        exact hMT q (by rw [hTdef]; exact mem_avoidSet_of_dvd_a hq (by omega) hqa) hqM
      have hpa : ringChar (𝓞 K ⧸ 𝔭.asIdeal) ∣ Ideal.absNorm 𝔭.asIdeal := by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
        exact ringChar.dvd (Nat.cast_card_eq_zero _)
      have hpid : ringChar (𝓞 K ⧸ 𝔭.asIdeal) ∣ 1 := by
        rw [← Nat.coprime_iff_gcd_eq_one.mp hpcop]
        exact Nat.dvd_gcd hpM hpa
      exact CharP.ringChar_ne_one (Nat.dvd_one.mp hpid)
    have hFζ : F ζ = ζ ^ Ideal.absNorm 𝔭.asIdeal :=
      isFrobAt_zeta_pow (K := K) (L := L) M hζ 𝔭 hM_p P hP F hF
    have hχF : ((χ F : (ZMod M)ˣ) : ZMod M) = (Ideal.absNorm 𝔭.asIdeal : ZMod M) := by
      have h := autToPow_eq_of_pow_eq (K := K) hζ F (Ideal.absNorm 𝔭.asIdeal) hFζ
      simpa [χ] using h
    -- ## the subgroup `H` and the field `E`
    haveI hcomm : IsMulCommutative (Gal(Ω/K)) := ⟨⟨fun x y => hΨinj (by
      rw [map_mul, map_mul, mul_comm'])⟩⟩
    let H : Subgroup (Gal(Ω/K)) := Subgroup.zpowers F ⊔ Subgroup.zpowers σtilde
    let E : IntermediateField K Ω := IntermediateField.fixedField H
    have hHnormal : H.Normal := Subgroup.normal_of_isMulCommutative H
    haveI hHnormalI : H.Normal := hHnormal
    haveI hEgal : IsGalois K ↥E := IsGalois.of_fixedField_normal_subgroup H
    have hFmem : F ∈ H := (le_sup_left : Subgroup.zpowers F ≤ H) (Subgroup.mem_zpowers F)
    have hσmem : σtilde ∈ H :=
      (le_sup_right : Subgroup.zpowers σtilde ≤ H) (Subgroup.mem_zpowers σtilde)
    have hcommΓ : ∀ x y : Gal(Ω/K), x * y = y * x :=
      fun x y => hΨinj (by rw [map_mul, map_mul, mul_comm'])
    -- ## the key computation `H ∩ ker χ = 1`
    have hHker : ∀ h ∈ H, χ h = 1 → h = 1 := by
      letI : CommGroup (Gal(Ω/K)) := { mul_comm := hcommΓ }
      intro h hh hχ1
      have hh' : h ∈ Subgroup.zpowers F ⊔ Subgroup.zpowers σtilde := hh
      obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp hh'
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [← hyz] at hχ1
      rw [← hyz]
      have hχeq : (χ F) ^ i * bu ^ j = 1 := by
        rw [map_mul, map_zpow, map_zpow, hχσtilde] at hχ1
        exact hχ1
      have hind_units : ∀ p q : ℕ, (χ F) ^ p * bu ^ q = 1 →
          Nat.card (L ≃ₐ[K] L) ∣ p ∧ Nat.card (L ≃ₐ[K] L) ∣ q := by
        intro p q hpq
        refine hindM p q ?_
        have hc := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) hpq
        simpa only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one, hbuval, hχF] using hc
      have hordχF : Nat.card (L ≃ₐ[K] L) ∣ orderOf (χ F) := by
        rw [← orderOf_units (y := χ F), hχF]
        exact hordA
      have hordbu : Nat.card (L ≃ₐ[K] L) ∣ orderOf bu := by
        rw [← orderOf_units (y := bu), hbuval]
        exact hordB
      have hordχF0 : orderOf (χ F) ≠ 0 := by
        rw [← Nat.card_zpowers]; exact Nat.card_pos.ne'
      have hordbu0 : orderOf bu ≠ 0 := by
        rw [← Nat.card_zpowers]; exact Nat.card_pos.ne'
      obtain ⟨hiZ, hjZ⟩ :=
        int_dvd_of_zpow_mul_eq_one hnpos hordχF0 hordbu0 hordχF hordbu hind_units i j hχeq
      have hρeq : (ρ F) ^ i * σ ^ j = 1 := by
        have h1 : (ρ F) ^ i = 1 := by
          rw [← orderOf_dvd_iff_zpow_eq_one]
          exact dvd_trans (Int.natCast_dvd_natCast.mpr (orderOf_dvd_natCard (ρ F))) hiZ
        have h2 : σ ^ j = 1 := by
          rw [← orderOf_dvd_iff_zpow_eq_one]
          have hordσ : orderOf σ = Nat.card (L ≃ₐ[K] L) := by
            have hσtop : Subgroup.zpowers σ = ⊤ := by
              refine le_antisymm le_top (fun x _ => hσgen x)
            rw [← Nat.card_zpowers σ, hσtop, Nat.card_congr (Subgroup.topEquiv).toEquiv]
          rw [hordσ]
          exact hjZ
        rw [h1, h2, one_mul]
      have hΨh : Ψ (F ^ i * σtilde ^ j) = 1 := by
        rw [map_mul, map_zpow, map_zpow]
        refine Prod.ext ?_ ?_
        · rw [show ((Ψ F) ^ i * (Ψ σtilde) ^ j).1 = (ρ F) ^ i * (ρ σtilde) ^ j from by
              simp [Ψ, MonoidHom.prod_apply], hρσtilde]
          exact hρeq
        · rw [show ((Ψ F) ^ i * (Ψ σtilde) ^ j).2 = (χ F) ^ i * (χ σtilde) ^ j from by
              simp [Ψ, MonoidHom.prod_apply], hχσtilde]
          exact hχeq
      exact hΨinj (by rw [hΨh, map_one])
    -- ## `E ∩ L = K`
    have hEdisj : Disjoint E ((⊥ : IntermediateField L Ω).restrictScalars K) := by
      rw [disjoint_iff]
      refine le_bot_iff.mp (fun x hx => ?_)
      rw [IntermediateField.mem_inf] at hx
      obtain ⟨hxE, hxA⟩ := hx
      rw [IntermediateField.mem_restrictScalars] at hxA
      obtain ⟨l, rfl⟩ := IntermediateField.mem_bot.mp hxA
      have hfx : σtilde (algebraMap L Ω l) = algebraMap L Ω l :=
        (IntermediateField.mem_fixedField_iff H _).mp hxE σtilde hσmem
      have hsl : σ l = l := by
        have h1 : (σtilde.restrictNormal L) l = l := by
          apply (algebraMap L Ω).injective
          rw [AlgEquiv.restrictNormal_commutes (F := K) (K₁ := Ω) (K₂ := Ω) σtilde L l]
          exact hfx
        have h2 : (ρ σtilde) l = l := h1
        rw [hρσtilde] at h2
        exact h2
      have hσtop : Subgroup.zpowers σ = ⊤ := by
        refine le_antisymm le_top (fun x _ => hσgen x)
      have hlK : l ∈ (⊥ : IntermediateField K L) := by
        have hlf : l ∈ IntermediateField.fixedField (Subgroup.zpowers σ) := by
          rw [IntermediateField.mem_fixedField_iff]
          intro f hf
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
          exact zpow_apply_fixed σ hsl k
        rw [hσtop, IsGalois.fixedField_top] at hlf
        exact hlf
      obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hlK
      rw [IntermediateField.mem_bot]
      exact ⟨c, by rw [IsScalarTower.algebraMap_apply K L Ω, hc]⟩
    -- ## `E · ℚ(ζ) = Ω`
    have hEjoin : (E.restrictScalars ℚ) ⊔
        (IntermediateField.adjoin ℚ ({ζ} : Set Ω)) = ⊤ := by
      have hker : (IntermediateField.adjoin K ({ζ} : Set Ω)).fixingSubgroup = χ.ker := by
        ext τ
        rw [IntermediateField.mem_fixingSubgroup_iff, MonoidHom.mem_ker]
        constructor
        · intro hτ
          have hζτ : τ ζ = ζ := hτ ζ (IntermediateField.subset_adjoin K _ (Set.mem_singleton ζ))
          have hspec : ζ ^ (((χ τ : (ZMod M)ˣ) : ZMod M)).val = τ ζ :=
            IsPrimitiveRoot.autToPow_spec K hζ τ
          rw [hζτ] at hspec
          have hval : (((χ τ : (ZMod M)ˣ) : ZMod M)).val = 1 := by
            exact hζ.pow_inj (i := (((χ τ : (ZMod M)ˣ) : ZMod M)).val) (j := 1)
              (ZMod.val_lt _) (by omega) (by simpa using hspec)
          refine Units.ext ?_
          rw [Units.val_one, ← ZMod.natCast_zmod_val ((χ τ : (ZMod M)ˣ) : ZMod M), hval]
          simp
        · intro hτ
          have hτζ : τ ζ = ζ := by
            have hspec := IsPrimitiveRoot.autToPow_spec K hζ τ
            rw [show ((χ τ : (ZMod M)ˣ) : ZMod M) = 1 from by rw [hτ, Units.val_one],
              show ((1 : ZMod M)).val = 1 from ZMod.val_one'' (by omega)] at hspec
            simpa using hspec.symm
          have hle : IntermediateField.adjoin K ({ζ} : Set Ω) ≤
              IntermediateField.fixedField (Subgroup.zpowers τ) := by
            rw [IntermediateField.adjoin_le_iff]
            intro w hw
            rw [Set.mem_singleton_iff] at hw
            subst hw
            change ζ ∈ IntermediateField.fixedField (Subgroup.zpowers τ)
            rw [IntermediateField.mem_fixedField_iff]
            intro f hf
            obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
            exact zpow_apply_fixed τ hτζ k
          rw [IntermediateField.le_iff_le] at hle
          exact (IntermediateField.mem_fixingSubgroup_iff
            (IntermediateField.adjoin K ({ζ} : Set Ω)) τ).mp (Subgroup.zpowers_le.mp hle)
      have hsupK : E ⊔ IntermediateField.adjoin K ({ζ} : Set Ω) = ⊤ := by
        have hfix : (E ⊔ IntermediateField.adjoin K ({ζ} : Set Ω)).fixingSubgroup = ⊥ := by
          rw [IntermediateField.fixingSubgroup_sup,
            show E.fixingSubgroup = H from IntermediateField.fixingSubgroup_fixedField H, hker]
          exact le_antisymm (fun x hx => hHker x hx.1 hx.2) bot_le
        have htop := IsGalois.fixedField_fixingSubgroup
          (E ⊔ IntermediateField.adjoin K ({ζ} : Set Ω))
        rw [hfix, IntermediateField.fixedField_bot] at htop
        exact htop.symm
      -- `E(ζ) = Ω` as `ℚ`-level fields, by transport along `adjoin`.
      have hset : (IntermediateField.adjoin K ((↑E ∪ ({ζ} : Set Ω)) : Set Ω) :
          IntermediateField K Ω) = ⊤ := by
        rw [IntermediateField.adjoin_union, IntermediateField.adjoin_self]
        exact hsupK
      have hJeq : IntermediateField.adjoin ℚ
          ((↑(E.restrictScalars ℚ) ∪ ({ζ} : Set Ω)) : Set Ω) =
          (E.restrictScalars ℚ) ⊔ IntermediateField.adjoin ℚ ({ζ} : Set Ω) := by
        rw [IntermediateField.adjoin_union, IntermediateField.adjoin_self]
      have hsub : ((IntermediateField.adjoin K ((↑E ∪ ({ζ} : Set Ω)) : Set Ω) :
            IntermediateField K Ω) : Set Ω) ⊆
          ((IntermediateField.adjoin ℚ
            ((↑(E.restrictScalars ℚ) ∪ ({ζ} : Set Ω)) : Set Ω) :
            IntermediateField ℚ Ω) : Set Ω) := by
        refine (IntermediateField.adjoin_subset_adjoin_iff (F := K) (F' := ℚ)).mpr ⟨?_, ?_⟩
        · rintro x ⟨k, rfl⟩
          refine IntermediateField.subset_adjoin ℚ _ (Or.inl ?_)
          exact E.algebraMap_mem' k
        · intro x hx
          refine IntermediateField.subset_adjoin ℚ _ ?_
          rcases hx with hx | hx
          · exact Or.inl hx
          · exact Or.inr hx
      refine eq_top_iff.mpr (fun x _ => ?_)
      have hx : x ∈ (IntermediateField.adjoin K ((↑E ∪ ({ζ} : Set Ω)) : Set Ω) :
          IntermediateField K Ω) := by rw [hset]; trivial
      have := hsub hx
      rwa [hJeq] at this
    refine ⟨E, hEdisj, hEjoin, ?_⟩
    -- ## `IsFrobAtPrime 𝔭 1`
    refine ⟨P.under (𝓞 ↥E), ?_, ?_⟩
    · refine Ideal.LiesOver.mk ?_
      rw [NK.Chebotarev.under_asIdeal, Ideal.under_under]
      exact hP.over
    · have h1 : NK.Chebotarev.IsFrobAt (K := K) (L := ↥E) (P.under (𝓞 ↥E))
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) E F) :=
        NK.Chebotarev.IsFrobAtRestrictNormalHom (K := K) (M := Ω) E hP hF
      have h2 : (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) E F) = 1 := by
        ext x
        have hval : ((AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) E F) x : Ω) =
            F (x : Ω) :=
          AlgEquiv.restrictNormal_commutes (F := K) (K₁ := Ω) (K₂ := Ω) F ↥E x
        rw [hval, AlgEquiv.one_apply]
        exact (IntermediateField.mem_fixedField_iff H (x : Ω)).mp x.2 F hFmem
      rwa [h2] at h1

end NK.CFTLib.ARL
