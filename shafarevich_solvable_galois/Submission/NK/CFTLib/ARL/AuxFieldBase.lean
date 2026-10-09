import Mathlib
import Submission.NK.CFTLib.ARL.AuxField
import Submission.NK.CFTLib.ARL.auxField_arith
import Submission.NK.CFTLib.ARL.disjoint_restrictScalars_adjoin_zeta
import Submission.NK.CFTLib.ARL.isGalois_cyclotomicField_over_base
import Submission.NK.CFTLib.ARL.autToPow_eq_of_pow_eq
import Submission.NK.Chebotarev.Basic
import Submission.NK.Chebotarev.IsFrobAtRestrictNormalHom
import Submission.NK.FieldTheory.Galois.exists_prod_restrictNormalHom_of_card
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Artin's auxiliary-field lemma (existence form)

This module proves `NK.CFTLib.ARL.auxField_exists_one`: for a finite cyclic extension `L/K` of
number fields and `m > 0`, the auxiliary-field hypothesis `NK.CFTLib.ARL.AuxFieldHyp K L m` of
Artin's lemma (Lang, *Algebraic Number Theory*, Ch. X §2; Childress, *CFT*, Lemma 2.8) holds.

The construction: choose the modulus `M` and the auxiliary prime `ℓ` with the arithmetic property
`NK.CFTLib.ARL.auxField_arith` (`ℓ ^ u · N𝔭 ^ v = 1 (mod M) ⟹ [L:K] ∣ u` and `∣ v`); inside
`Ω = L(ζ_M)` one has `Gal(Ω/K) ≅ Gal(L/K) × Gal(K(ζ_M)/K)`, and for each `𝔭 ∈ s` one takes
`E_𝔭 = Ω ^ H` for `H = ⟨δ, Φ_𝔭⟩`, where `δ` has `L`-component a generator of `Gal(L/K)` and
`K(ζ_M)`-component the automorphism of `K(ζ_M)/K` induced by `ζ ↦ ζ ^ ℓ`, while `Φ_𝔭` is a
Frobenius element at `𝔭`.  The defining properties of `H` are that `δ` (with a fixed `L`-part)
lies in every `H` while `H ∩ Gal(Ω/K(ζ_M)) = 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace NK.CFTLib.ARL

open IntermediateField

/-! ## Auxiliary facts about `L(ζ_M)` -/

/-- In a cyclotomic extension of level `M`, the standard primitive `M`-th root of unity generates
the whole field over the base. -/
theorem adjoin_zeta_eq_top_base {K L : Type*} [Field K] [Field L] [Algebra K L]
    (M : ℕ) [NeZero M] [IsCyclotomicExtension {M} K L] :
    IntermediateField.adjoin K
      ({IsCyclotomicExtension.zeta M K L} : Set L) = ⊤ := by
  haveI : IsCyclotomicExtension {M} K ↥(⊤ : IntermediateField K L) :=
    IsCyclotomicExtension.equiv (S := {M}) (A := K) (B := L)
      (C := ↥(⊤ : IntermediateField K L)) (IntermediateField.topEquiv.symm)
  exact ((IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin M K L
    (⊤ : IntermediateField K L) (IsCyclotomicExtension.zeta_spec M K L)).mp inferInstance).symm

/-- **`L(ζ_M) = L ⊔ K(ζ_M)`** as intermediate fields of `CyclotomicField M L` over `K`. -/
theorem sup_restrictScalars_adjoin_zeta_eq_top_base {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] (M : ℕ) [NeZero M] :
    (⊥ : IntermediateField L (CyclotomicField M L)).restrictScalars K ⊔
      IntermediateField.adjoin K
        ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} :
          Set (CyclotomicField M L)) = ⊤ := by
  set Ω := CyclotomicField M L
  set ζ := IsCyclotomicExtension.zeta M L Ω with hζ
  set A : IntermediateField K Ω := (⊥ : IntermediateField L Ω).restrictScalars K with hA
  set B : IntermediateField K Ω := IntermediateField.adjoin K ({ζ} : Set Ω) with hB
  have htop : (⊤ : IntermediateField L Ω) = IntermediateField.adjoin L ({ζ} : Set Ω) := by
    haveI : IsCyclotomicExtension {M} L ↥(⊤ : IntermediateField L Ω) :=
      IsCyclotomicExtension.equiv {M} L Ω (IntermediateField.topEquiv (F := L)).symm
    exact (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin M L Ω ⊤
      (IsCyclotomicExtension.zeta_spec M L Ω)).mp inferInstance
  have hsub : (IntermediateField.adjoin L ({ζ} : Set Ω) : Set Ω) ⊆
      (IntermediateField.adjoin K ((A ⊔ B : IntermediateField K Ω) : Set Ω)) := by
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
      ((A ⊔ B : IntermediateField K Ω) : Set Ω) ≤ A ⊔ B :=
    IntermediateField.adjoin_le_iff.mpr (fun x hx => hx)
  have huniv : (IntermediateField.adjoin L ({ζ} : Set Ω) : Set Ω) = Set.univ := by
    rw [← htop]
    rfl
  change A ⊔ B = ⊤
  refine le_antisymm le_top ?_
  intro x hx
  exact hle (hsub (huniv ▸ Set.mem_univ x))

/-- A form of `IntermediateField.LinearDisjoint.of_inf_eq_bot` whose `IsGalois` instance is an
explicit argument (type class search does not reliably find it at the application site). -/
theorem ld_of_inf_eq_bot {F E : Type*} [Field F] [Field E] [Algebra F E]
    {A B : IntermediateField F E} [IsGalois F ↥A] [FiniteDimensional F ↥A]
    [FiniteDimensional F ↥B] (h : A ⊓ B = ⊥) : A.LinearDisjoint ↥B :=
  IntermediateField.LinearDisjoint.of_inf_eq_bot h

/-- **The degree of `K(ζ_M)` over `K`**: `[K(ζ_M) : K] = φ(M)`, whenever no prime divisor of `M`
divides the discriminant of `K`. -/
theorem finrank_adjoin_zeta_eq_totient {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (M : ℕ) [NeZero M]
    (hM : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr K).natAbs) :
    Module.finrank K (IntermediateField.adjoin K
      ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} : Set (CyclotomicField M L))) =
      M.totient := by
  classical
  set Ω := CyclotomicField M L
  set ζ := IsCyclotomicExtension.zeta M L Ω with hζdef
  have hζ : IsPrimitiveRoot ζ M := IsCyclotomicExtension.zeta_spec M L Ω
  set Qζ : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ ({ζ} : Set Ω) with hQζ
  set Kq : IntermediateField ℚ Ω := (⊥ : IntermediateField K Ω).restrictScalars ℚ with hKq
  set T : IntermediateField K Ω := IntermediateField.adjoin K ({ζ} : Set Ω) with hT
  have hdisjK : Qζ ⊓ Kq = ⊥ := by
    rw [hQζ, hKq]
    exact intersect_cyclotomic_eq_bot_gen (F := K) M hM ζ hζ
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
  haveI hTfd : FiniteDimensional K ↥T := by
    rw [hT]
    exact IntermediateField.finiteDimensional_adjoin (S := ({ζ} : Set Ω)) (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      exact hx ▸ (hζ.isIntegral (NeZero.pos M)).tower_top)
  have hfrQζ : Module.finrank ℚ ↥Qζ = M.totient :=
    IsCyclotomicExtension.finrank ↥Qζ (Polynomial.cyclotomic.irreducible_rat (NeZero.pos M))
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
  have hTℚ : T.restrictScalars ℚ = Qζ ⊔ Kq := by
    have hsup : (Qζ ⊔ Kq : IntermediateField ℚ Ω) =
        IntermediateField.adjoin ℚ ((Qζ : Set Ω) ∪ (Kq : Set Ω)) := by
      rw [IntermediateField.adjoin_union, IntermediateField.adjoin_self,
        IntermediateField.adjoin_self]
    apply SetLike.coe_injective
    rw [IntermediateField.coe_restrictScalars, hsup]
    apply Set.Subset.antisymm
    · rw [hT, IntermediateField.adjoin_subset_adjoin_iff]
      constructor
      · intro y hy
        exact IntermediateField.subset_adjoin ℚ _
          (Set.subset_union_right ((IntermediateField.mem_restrictScalars ℚ).mpr
            ((IntermediateField.mem_bot).mpr hy)))
      · intro y hy
        rw [Set.mem_singleton_iff] at hy
        exact hy.symm ▸ (IntermediateField.subset_adjoin ℚ _ (Set.subset_union_left hζQ))
    · rw [hT, IntermediateField.adjoin_subset_adjoin_iff]
      exact ⟨fun r hr => by
        obtain ⟨t, rfl⟩ := hr
        rw [IsScalarTower.algebraMap_apply ℚ K Ω]
        exact (IntermediateField.adjoin K ({ζ} : Set Ω)).algebraMap_mem t,
        fun y hy => by
          rcases hy with hy | hy
          · exact hQζT hy
          · exact hKqT hy⟩
  have h1 : Module.finrank ℚ K * Module.finrank K ↥T = Module.finrank ℚ ↥T :=
    Module.finrank_mul_finrank ℚ K ↥T
  have h2 : Module.finrank ℚ ↥T = Module.finrank ℚ K * M.totient := by
    have heq : Module.finrank ℚ ↥T = Module.finrank ℚ ↥(Qζ ⊔ Kq) := by
      rw [show Module.finrank ℚ ↥T = Module.finrank ℚ ↥(T.restrictScalars ℚ) from rfl, hTℚ]
    rw [heq]
    have hLDK : Qζ.LinearDisjoint ↥Kq :=
      @ld_of_inf_eq_bot ℚ Ω _ _ _ Qζ Kq hQζgal _ _ hdisjK
    rw [IntermediateField.LinearDisjoint.finrank_sup hLDK, hfrQζ, hfrKq]
    ring
  rw [h2] at h1
  exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h1

/-- **Cyclotomic reciprocity in automorphism form.**  If `K(ζ_M)/K` has degree `φ(M)` (i.e. `K`
contains no `p`-th root of unity for `p ∣ M`), then every `k` coprime to `M` is realised by an
automorphism: there is `σ ∈ Gal(K(ζ_M)/K)` with `σ ζ_M = ζ_M ^ k`. -/
theorem exists_algEquiv_zeta_pow {K B : Type} [Field K] [Field B] [Algebra K B]
    (M : ℕ) [NeZero M] [IsCyclotomicExtension {M} K B]
    (hcard : Module.finrank K B = M.totient) {k : ℕ} (hk : Nat.Coprime k M) :
    ∃ σ : B ≃ₐ[K] B,
      σ (IsCyclotomicExtension.zeta M K B) = (IsCyclotomicExtension.zeta M K B) ^ k := by
  classical
  set ζ := IsCyclotomicExtension.zeta M K B with hζdef
  have hζ : IsPrimitiveRoot ζ M := IsCyclotomicExtension.zeta_spec M K B
  haveI : IsGalois K B := IsCyclotomicExtension.isGalois {M} K B
  haveI : FiniteDimensional K B := IsCyclotomicExtension.finiteDimensional {M} K B
  haveI : Fintype (ZMod M)ˣ := Fintype.ofFinite _
  have hcard' : Nat.card (B ≃ₐ[K] B) = Nat.card (ZMod M)ˣ := by
    rw [IsGalois.card_aut_eq_finrank, hcard, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hinj : Function.Injective (hζ.autToPow K) := IsPrimitiveRoot.autToPow_injective K hζ
  have hbij : Function.Bijective (hζ.autToPow K) :=
    (Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard'⟩
  set σ : B ≃ₐ[K] B :=
    (MulEquiv.ofBijective (hζ.autToPow K) hbij).symm (ZMod.unitOfCoprime k hk) with hσdef
  have hσspec : hζ.autToPow K σ = ZMod.unitOfCoprime k hk := by
    rw [hσdef]
    simp
  refine ⟨σ, ?_⟩
  have hspec := IsPrimitiveRoot.autToPow_spec K hζ σ
  rw [hσspec] at hspec
  rw [← hspec]
  have hk' : ζ ^ k = ζ ^ (k % M) := by
    conv_lhs => rw [← Nat.mod_add_div k M]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  have hval : ((ZMod.unitOfCoprime k hk : (ZMod M)ˣ) : ZMod M).val = k % M := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  rw [hk', hval]


/-- **Cyclotomic reciprocity: realising any exponent coprime to `M` by an automorphism**, for an
arbitrary primitive `M`-th root `μ` generating a cyclotomic extension of degree `φ(M)`. -/
theorem exists_algEquiv_primitiveRoot_pow {K B : Type} [Field K] [Field B] [Algebra K B]
    (M : ℕ) [NeZero M] [IsCyclotomicExtension {M} K B]
    (hcard : Module.finrank K B = M.totient) {μ : B} (hμ : IsPrimitiveRoot μ M)
    {k : ℕ} (hk : Nat.Coprime k M) :
    ∃ σ : B ≃ₐ[K] B, σ μ = μ ^ k := by
  classical
  haveI : IsGalois K B := IsCyclotomicExtension.isGalois {M} K B
  haveI : FiniteDimensional K B := IsCyclotomicExtension.finiteDimensional {M} K B
  haveI : Fintype (ZMod M)ˣ := Fintype.ofFinite _
  have hcard' : Nat.card (B ≃ₐ[K] B) = Nat.card (ZMod M)ˣ := by
    rw [IsGalois.card_aut_eq_finrank, hcard, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hinj : Function.Injective (hμ.autToPow K) := IsPrimitiveRoot.autToPow_injective K hμ
  have hbij : Function.Bijective (hμ.autToPow K) :=
    (Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard'⟩
  set σ : B ≃ₐ[K] B :=
    (MulEquiv.ofBijective (hμ.autToPow K) hbij).symm (ZMod.unitOfCoprime k hk) with hσdef
  have hσspec : hμ.autToPow K σ = ZMod.unitOfCoprime k hk := by
    rw [hσdef]
    simp
  refine ⟨σ, ?_⟩
  have hspec := IsPrimitiveRoot.autToPow_spec K hμ σ
  rw [hσspec] at hspec
  rw [← hspec]
  have hk' : μ ^ k = μ ^ (k % M) := by
    conv_lhs => rw [← Nat.mod_add_div k M]
    rw [pow_add, pow_mul, hμ.pow_eq_one, one_pow, mul_one]
  have hval : ((ZMod.unitOfCoprime k hk : (ZMod M)ˣ) : ZMod M).val = k % M := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  rw [hk', hval]

/-- **A Frobenius at `𝔭` raises a primitive `M`-th root of unity to the `N𝔭`-th power.** -/
theorem isFrobAt_zeta_pow_base {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (M : ℕ) [NeZero M]
    {ζ : CyclotomicField M L} (hζ : IsPrimitiveRoot ζ M) (𝔭 : HeightOneSpectrum (𝓞 K))
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

/-- The subgroup generated by two commuting elements, described explicitly. -/
def closurePairSubgroup {G : Type*} [Group G] (a b : G) (hab : Commute a b) : Subgroup G where
  carrier := {x | ∃ i j : ℤ, a ^ i * b ^ j = x}
  one_mem' := ⟨0, 0, by simp⟩
  mul_mem' := by
    rintro x y ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
    refine ⟨i + k, j + l, ?_⟩
    calc a ^ (i + k) * b ^ (j + l)
        = a ^ i * a ^ k * (b ^ j * b ^ l) := by rw [zpow_add, zpow_add]
      _ = a ^ i * (a ^ k * b ^ j) * b ^ l := by group
      _ = a ^ i * (b ^ j * a ^ k) * b ^ l := by rw [(hab.zpow_zpow k j).eq]
      _ = a ^ i * b ^ j * (a ^ k * b ^ l) := by group
  inv_mem' := by
    rintro x ⟨i, j, rfl⟩
    refine ⟨-i, -j, ?_⟩
    rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]
    exact (hab.zpow_zpow (-i) (-j)).eq

theorem closure_pair_eq {G : Type*} [Group G] {a b : G} (hab : Commute a b) :
    Subgroup.closure ({a, b} : Set G) = closurePairSubgroup a b hab := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with h | h
    · subst h; exact ⟨1, 0, by simp⟩
    · subst h; exact ⟨0, 1, by simp⟩
  · intro x hx
    obtain ⟨i, j, rfl⟩ := hx
    exact mul_mem (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) i)
      (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) j)

/-- **Independence in a finite abelian group, with integer exponents.**  If `a ^ i * b ^ j = 1`
forces `n ∣ i` and `n ∣ j` for natural exponents, the same holds for integer exponents. -/
lemma int_dvd_of_zpow_mul_eq_one_base {n : ℕ} (hn : 0 < n) {H : Type*} [CommGroup H] {a b : H}
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

end NK.CFTLib.ARL
