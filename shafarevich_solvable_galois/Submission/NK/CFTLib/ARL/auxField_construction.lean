import Mathlib.Computability.Reduce
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Submission.NK.CFTLib.ARL.AuxField
import Submission.NK.CFTLib.ARL.disjoint_restrictScalars_adjoin_zeta
import Submission.NK.CFTLib.ARL.inertiaDeg_one_isFrobAtPrime_one
import Submission.NK.CFTLib.ARL.isGalois_cyclotomicField_over_base
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The auxiliary field of Artin's lemma, fixed-modulus form

This module proves `NK.CFTLib.ARL.auxField_construction`: given a finite cyclic extension
`L/K` of number fields, a modulus `M` (coprime to the relevant data), a rational prime `ℓ` with
`ℓ ∤ M` whose class in `(ZMod M)ˣ` is "independent" of the norms of the primes in a finite set
`s` (hypothesis `hrel`), and a finite set of primes `s` at which `(M) ∉ 𝔭`, there are a field
`E ⊆ L(ζ_M)` with `E ∩ L = K` and, for each `𝔭 ∈ s`, a subfield `E𝔭 ≤ E` with
`E𝔭 · ℚ(ζ_M) = L(ζ_M)` and `𝔭` splitting completely in `E𝔭/K`.

The construction is the standard one: `Ω := L(ζ_M)`, `Γ := Gal(Ω/K) ≅ Gal(L/K) × (ZMod M)ˣ`,
`σtilde ∈ Γ` a lift of a generator `σ` of `Gal(L/K)` with cyclotomic component `ℓ`, and
`E𝔭 := Ω^{⟨F𝔭, σtilde⟩}` for `F𝔭` a Frobenius at a prime above `𝔭`; `E` is the fixed field of the
intersection of the groups `⟨F𝔭, σtilde⟩`.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace NK.CFTLib.ARL

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Generating the cyclotomic field by its standard primitive root -/

/-- In a cyclotomic extension of level `M`, the standard primitive `M`-th root of unity generates
the whole field over the base. -/
theorem aux_adjoin_zeta_eq_top (M : ℕ) [NeZero M] :
    IntermediateField.adjoin L ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} :
      Set (CyclotomicField M L)) = ⊤ := by
  have htop : IsCyclotomicExtension {M} L ↥(⊤ : IntermediateField L (CyclotomicField M L)) :=
    IsCyclotomicExtension.equiv (S := {M}) (A := L) (B := CyclotomicField M L)
      (C := ↥(⊤ : IntermediateField L (CyclotomicField M L))) (IntermediateField.topEquiv.symm)
  have h := (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin M L
    (CyclotomicField M L) (⊤ : IntermediateField L (CyclotomicField M L))
    (IsCyclotomicExtension.zeta_spec M L _)).mp htop
  exact h.symm

/-! ## `L(ζ_M) = L ⊔ K(ζ_M)` (and the same with `ℚ` in place of `K`) -/

/-- **`L(ζ_M) = L ⊔ K(ζ_M)`** as intermediate fields of `CyclotomicField M L` over `K`. -/
theorem aux_sup_restrictScalars_adjoin_zeta_eq_top (M : ℕ) [NeZero M] :
    (⊥ : IntermediateField L (CyclotomicField M L)).restrictScalars K ⊔
      IntermediateField.adjoin K
        ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} :
          Set (CyclotomicField M L)) = ⊤ := by
  set Ω := CyclotomicField M L
  set ζ := IsCyclotomicExtension.zeta M L Ω with hζdef
  set A : IntermediateField K Ω := (⊥ : IntermediateField L Ω).restrictScalars K with hA
  set B : IntermediateField K Ω := IntermediateField.adjoin K ({ζ} : Set Ω) with hB
  have htop : (⊤ : IntermediateField L Ω) =
      IntermediateField.adjoin L ({ζ} : Set Ω) := (aux_adjoin_zeta_eq_top (L := L) M).symm
  have hsub : (IntermediateField.adjoin L ({ζ} : Set Ω) : Set Ω) ⊆
      (IntermediateField.adjoin K
        ((A ⊔ B : IntermediateField K Ω) : Set Ω)) := by
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

/-- **`L(ζ_M) = L ⊔ ℚ(ζ_M)`** as intermediate fields of `CyclotomicField M L` over `ℚ`. -/
theorem aux_sup_restrictScalars_adjoin_zeta_eq_top_rat (M : ℕ) [NeZero M] :
    (⊥ : IntermediateField L (CyclotomicField M L)).restrictScalars ℚ ⊔
      IntermediateField.adjoin ℚ
        ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} :
          Set (CyclotomicField M L)) = ⊤ := by
  set Ω := CyclotomicField M L
  set ζ := IsCyclotomicExtension.zeta M L Ω with hζdef
  set A : IntermediateField ℚ Ω := (⊥ : IntermediateField L Ω).restrictScalars ℚ with hA
  set B : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ ({ζ} : Set Ω) with hB
  have htop : (⊤ : IntermediateField L Ω) =
      IntermediateField.adjoin L ({ζ} : Set Ω) := (aux_adjoin_zeta_eq_top (L := L) M).symm
  have hsub : (IntermediateField.adjoin L ({ζ} : Set Ω) : Set Ω) ⊆
      (IntermediateField.adjoin ℚ
        ((A ⊔ B : IntermediateField ℚ Ω) : Set Ω)) := by
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
      ((A ⊔ B : IntermediateField ℚ Ω) : Set Ω) ≤ A ⊔ B :=
    IntermediateField.adjoin_le_iff.mpr (fun x hx => hx)
  have huniv : (IntermediateField.adjoin L ({ζ} : Set Ω) : Set Ω) = Set.univ := by
    rw [← htop]
    rfl
  change A ⊔ B = ⊤
  refine le_antisymm le_top ?_
  intro x hx
  exact hle (hsub (huniv ▸ Set.mem_univ x))

/-! ## The degree of `L(ζ_M)` over `K` -/

/-- **The degree of `L(ζ_M)` over `K`**: `[L(ζ_M) : K] = [L : K] · φ(M)` for `M` coprime to the
discriminant of `L`. -/
theorem aux_finrank_cyclotomicField (M : ℕ) [NeZero M]
    (hM : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr L).natAbs) :
    Module.finrank K (CyclotomicField M L) = Module.finrank K L * M.totient := by
  set Ω := CyclotomicField M L
  set ζ : Ω := IsCyclotomicExtension.zeta M L Ω with hζdef
  have hζ : IsPrimitiveRoot ζ M := IsCyclotomicExtension.zeta_spec M L Ω
  haveI hSTL : IsScalarTower ℚ L Ω := IsScalarTower.of_algebraMap_eq (fun x => by simp)
  haveI hSTK : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq (fun x => by simp)
  let Qζ : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ ({ζ} : Set Ω)
  let Lq : IntermediateField ℚ Ω := (⊥ : IntermediateField L Ω).restrictScalars ℚ
  have hQζdef : Qζ = IntermediateField.adjoin ℚ ({ζ} : Set Ω) := rfl
  have hLqdef : Lq = (⊥ : IntermediateField L Ω).restrictScalars ℚ := rfl
  have hinf : Qζ ⊓ Lq = ⊥ := by
    rw [hQζdef, hLqdef]
    exact intersect_cyclotomic_eq_bot_gen (F := L) M hM ζ hζ
  have hsup : Qζ ⊔ Lq = ⊤ := by
    rw [hQζdef, hLqdef, sup_comm]
    exact aux_sup_restrictScalars_adjoin_zeta_eq_top_rat (L := L) M
  haveI hcyc : IsCyclotomicExtension {M} ℚ ↥Qζ := by
    rw [hQζdef]
    exact hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have hgalQ : IsGalois ℚ ↥Qζ := IsCyclotomicExtension.isGalois {M} ℚ ↥Qζ
  have hfdQ : FiniteDimensional ℚ ↥Qζ := IsCyclotomicExtension.finiteDimensional {M} ℚ ↥Qζ
  have hfdLq : FiniteDimensional ℚ ↥Lq := by
    rw [hLqdef]
    exact FiniteDimensional.trans ℚ L ↥(⊥ : IntermediateField L Ω)
  have hLD : Qζ.LinearDisjoint ↥Lq :=
    @IntermediateField.LinearDisjoint.of_inf_eq_bot ℚ Ω _ _ _ Qζ Lq hgalQ hfdQ hfdLq hinf
  have hfrQ : Module.finrank ℚ ↥Qζ = M.totient :=
    IsCyclotomicExtension.finrank ↥Qζ (Polynomial.cyclotomic.irreducible_rat (NeZero.pos M))
  have hfrLq : Module.finrank ℚ ↥Lq = Module.finrank ℚ L := by
    change Module.finrank ℚ ↥(⊥ : IntermediateField L Ω) = Module.finrank ℚ L
    rw [← Module.finrank_mul_finrank ℚ L ↥(⊥ : IntermediateField L Ω),
      (IntermediateField.botEquiv L Ω).toLinearEquiv.finrank_eq, Module.finrank_self, mul_one]
  have hΩLq : Module.finrank ↥Lq Ω = M.totient := by
    have h := hLD.finrank_right_eq_finrank hsup
    rwa [hfrQ] at h
  have hLΩ : Module.finrank L Ω = M.totient := by
    have h1 : Module.finrank ℚ L * Module.finrank ↥Lq Ω = Module.finrank ℚ Ω := by
      rw [← hfrLq]; exact Module.finrank_mul_finrank ℚ ↥Lq Ω
    have h2 : Module.finrank ℚ L * Module.finrank L Ω = Module.finrank ℚ Ω :=
      Module.finrank_mul_finrank ℚ L Ω
    have h3 : Module.finrank ℚ L * Module.finrank ↥Lq Ω
        = Module.finrank ℚ L * Module.finrank L Ω := by rw [h1, h2]
    rw [hΩLq] at h3
    exact (Nat.eq_of_mul_eq_mul_left Module.finrank_pos h3).symm
  rw [← Module.finrank_mul_finrank K L Ω, hLΩ]

/-! ## Auxiliary group-theoretic and order-theoretic lemmas -/

/-- The subgroup generated by two commuting elements, described explicitly: in a group `G` with
commuting `a b`, the closure of `{a, b}` is the set of elements `a ^ i * b ^ j` (`i j : ℤ`). -/
def zpair {G : Type*} [Group G] (a b : G) (hab : Commute a b) : Subgroup G where
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

/-- A power of an element fixing `a` still fixes `a`. -/
lemma aux_zpow_apply_fixed {F E : Type*} [Field F] [Field E] [Algebra F E] (x : E ≃ₐ[F] E)
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
lemma aux_int_dvd_of_zpow_mul_eq_one {n : ℕ} (hn : 0 < n) {H : Type*} [CommGroup H] {a b : H}
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

/-! ## Frobenius elements and the cyclotomic character -/

/-- **A Frobenius at `𝔭` raises an `M`-th root of unity to the `N𝔭`-th power.** -/
theorem aux_frob_zeta_pow (M : ℕ) [NeZero M] {ζ : L} (hζ : IsPrimitiveRoot ζ M)
    (P : NK.Chebotarev.PrimeIdeal L) (𝔭 : NK.Chebotarev.PrimeIdeal K)
    (hP : P.asIdeal.LiesOver 𝔭.asIdeal) (hM𝔭 : (M : 𝓞 K) ∉ 𝔭.asIdeal) (F : Gal(L/K))
    (hF : NK.Chebotarev.IsFrobAt P F) : F ζ = ζ ^ Ideal.absNorm 𝔭.asIdeal := by
  have hζint : IsPrimitiveRoot hζ.toInteger M := hζ.toInteger_isPrimitiveRoot
  have hcoe : algebraMap (𝓞 L) L hζ.toInteger = ζ := hζ.coe_toInteger
  have hMP : (M : 𝓞 L) ∉ P.asIdeal := by
    intro hmem
    apply hM𝔭
    have h' : algebraMap (𝓞 K) (𝓞 L) (M : 𝓞 K) ∈ P.asIdeal := by
      rwa [map_natCast]
    exact (Ideal.mem_of_liesOver (P := P.asIdeal) (p := 𝔭.asIdeal)
      (x := (M : 𝓞 K))).mpr h'
  have h1 : galRestrict (𝓞 K) K L (𝓞 L) F hζ.toInteger
      = hζ.toInteger ^ Nat.card (𝓞 K ⧸ P.asIdeal.under (𝓞 K)) :=
    AlgHom.IsArithFrobAt.apply_of_pow_eq_one hF hζint.pow_eq_one hMP
  have h2 := congrArg (algebraMap (𝓞 L) L) h1
  rw [map_pow, algebraMap_galRestrict_apply] at h2
  rw [hcoe, ← hP.over] at h2
  have habs : Nat.card (𝓞 K ⧸ 𝔭.asIdeal) = Ideal.absNorm 𝔭.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rwa [habs] at h2

/-- **The cyclotomic character of a Frobenius element is `N𝔭`.** -/
theorem aux_frob_autToPow_eq_absNorm (M : ℕ) [NeZero M] {ζ : L} (hζ : IsPrimitiveRoot ζ M)
    (P : NK.Chebotarev.PrimeIdeal L) (𝔭 : NK.Chebotarev.PrimeIdeal K)
    (hP : P.asIdeal.LiesOver 𝔭.asIdeal) (hM𝔭 : (M : 𝓞 K) ∉ 𝔭.asIdeal) (F : Gal(L/K))
    (hF : NK.Chebotarev.IsFrobAt P F) :
    ((hζ.autToPow K F : (ZMod M)ˣ) : ZMod M) = (Ideal.absNorm 𝔭.asIdeal : ZMod M) :=
  autToPow_eq_of_pow_eq (K := K) hζ F (Ideal.absNorm 𝔭.asIdeal)
    (aux_frob_zeta_pow (K := K) (L := L) M hζ P 𝔭 hP hM𝔭 F hF)

/-- **The elements fixing `K(ζ_M)` pointwise have trivial cyclotomic component.** -/
theorem aux_fixingSubgroup_adjoin_zeta_le_ker (M : ℕ) [NeZero M] {ζ : L}
    (hζ : IsPrimitiveRoot ζ M) :
    (IntermediateField.adjoin K ({ζ} : Set L)).fixingSubgroup ≤ (hζ.autToPow K).ker := by
  intro h hh
  rw [MonoidHom.mem_ker]
  have hζh : h ζ = ζ :=
    (IntermediateField.mem_fixingSubgroup_iff _ h).mp hh ζ
      (IntermediateField.subset_adjoin K _ (Set.mem_singleton ζ))
  have hspec : ζ ^ (((hζ.autToPow K h : (ZMod M)ˣ) : ZMod M)).val = ζ := by
    rw [IsPrimitiveRoot.autToPow_spec K hζ h]
    exact hζh
  by_cases hM1 : M = 1
  · haveI : Subsingleton (ZMod M) := ZMod.subsingleton_iff.mpr hM1
    exact Subsingleton.elim _ _
  · have hM2 : 1 < M := by
      have := NeZero.pos M
      omega
    have hval : (((hζ.autToPow K h : (ZMod M)ˣ) : ZMod M)).val = 1 :=
      hζ.pow_inj (i := (((hζ.autToPow K h : (ZMod M)ˣ) : ZMod M)).val) (j := 1)
        (ZMod.val_lt _) hM2 (by simpa using hspec)
    refine Units.ext ?_
    rw [Units.val_one, ← ZMod.natCast_zmod_val ((hζ.autToPow K h : (ZMod M)ˣ) : ZMod M), hval]
    simp

/-! ## The passage from the `K`-level compositum to the `ℚ`-level one -/

/-- If `A` is a `K`-intermediate field of `Ω` containing `K`, then the `K`-compositum of `A` with
`K(ζ)` is contained in the `ℚ`-compositum of `A` with `ℚ(ζ)`. -/
theorem aux_sup_adjoin_subset {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower K L Ω] [Algebra ℚ Ω] [IsScalarTower ℚ L Ω] [IsScalarTower ℚ K Ω]
    (A : IntermediateField K Ω) (ζ : Ω) :
    ((A ⊔ IntermediateField.adjoin K ({ζ} : Set Ω) : IntermediateField K Ω) : Set Ω) ⊆
      (((A.restrictScalars ℚ) ⊔ IntermediateField.adjoin ℚ ({ζ} : Set Ω) :
        IntermediateField ℚ Ω) : Set Ω) := by
  let S1 : IntermediateField ℚ Ω := A.restrictScalars ℚ
  let S2 : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ ({ζ} : Set Ω)
  let S : IntermediateField ℚ Ω := S1 ⊔ S2
  have hS1le : S1 ≤ S := le_sup_left
  have hS2le : S2 ≤ S := le_sup_right
  intro x hx
  have hsup : (A ⊔ IntermediateField.adjoin K ({ζ} : Set Ω) : IntermediateField K Ω) =
      IntermediateField.adjoin K ((A : Set Ω) ∪ ({ζ} : Set Ω)) := by
    rw [IntermediateField.adjoin_union, show IntermediateField.adjoin K (A : Set Ω) = A from
      le_antisymm (IntermediateField.adjoin_le_iff.mpr le_rfl) (IntermediateField.subset_adjoin K _)]
  rw [hsup] at hx
  exact IntermediateField.adjoin_induction K (p := fun x _ => x ∈ S)
    (fun y hy => by
      rcases hy with hy | hy
      · exact hS1le ((IntermediateField.mem_restrictScalars ℚ).mpr hy)
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact hS2le (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton ζ)))
    (fun c => hS1le ((IntermediateField.mem_restrictScalars ℚ).mpr (A.algebraMap_mem c)))
    (fun y z _ _ hy hz => S.add_mem hy hz)
    (fun y _ hy => S.inv_mem hy)
    (fun y z _ _ hy hz => S.mul_mem hy hz)
    hx

theorem auxField_construction (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (m : ℕ) (hm : 0 < m) (s : Finset (NK.Chebotarev.PrimeIdeal K)) (S : Finset ℕ)
    (M : ℕ) [NeZero M] (ell : ℕ) (hell : ell.Prime)
    (hcopm : M.Coprime m) (havoid : ∀ p ∈ S, ¬ p ∣ M) (hellM : ¬ ell ∣ M)
    (hab : ∀ p : ℕ, p.Prime → p ∣ M → ∀ 𝔭 ∈ s, ¬ p ∣ Ideal.absNorm 𝔭.asIdeal)
    (hdiscrK : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr K).natAbs)
    (hdiscrL : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr L).natAbs)
    (hnotmem : ∀ 𝔭 ∈ s, (M : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal)
    (hrel : ∀ 𝔭 ∈ s, ∀ u v : ℕ,
      ((ell : ZMod M)) ^ u * (((Ideal.absNorm 𝔭.asIdeal : ℕ)) : ZMod M) ^ v = 1 →
        Module.finrank K L ∣ u ∧ Module.finrank K L ∣ v) :
    ∃ E : IntermediateField K (CyclotomicField M L),
      Disjoint E ((⊥ : IntermediateField L (CyclotomicField M L)).restrictScalars K) ∧
      (∀ 𝔭 ∈ s, ∃ E𝔭 : IntermediateField K (CyclotomicField M L),
        E𝔭 ≤ E ∧
        (E𝔭.restrictScalars ℚ) ⊔ (IntermediateField.adjoin ℚ
          ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} :
            Set (CyclotomicField M L))) = ⊤ ∧
        NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥E𝔭) 𝔭 1) := by
  classical
  set Ω := CyclotomicField M L
  set ζ : Ω := IsCyclotomicExtension.zeta M L Ω with hζdef
  have hζ : IsPrimitiveRoot ζ M := IsCyclotomicExtension.zeta_spec M L Ω
  haveI hgalΩ : IsGalois K Ω := isGalois_cyclotomicField_over_base (K := K) (L := L) M
  haveI hfdΩ : FiniteDimensional K Ω := inferInstance
  -- ## The product map `Ψ = (ρ, χ)`
  let ρ : Gal(Ω/K) →* Gal(L/K) := AlgEquiv.restrictNormalHom L
  let χ : Gal(Ω/K) →* (ZMod M)ˣ := hζ.autToPow K
  let Ψ : Gal(Ω/K) →* Gal(L/K) × (ZMod M)ˣ := ρ.prod χ
  have htopadjoin : Algebra.adjoin K (Set.range (algebraMap L Ω) ∪ {ζ}) = ⊤ := by
    have hgen : IntermediateField.adjoin K (Set.range (algebraMap L Ω) ∪ {ζ}) = ⊤ := by
      rw [eq_top_iff, ← aux_sup_restrictScalars_adjoin_zeta_eq_top (K := K) (L := L) M]
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
  have hΨinj : Function.Injective Ψ := by
    intro x y hxy
    have hρ : ρ x = ρ y := congrArg Prod.fst hxy
    have hχ : χ x = χ y := congrArg Prod.snd hxy
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
    rw [IsGalois.card_aut_eq_finrank K Ω, aux_finrank_cyclotomicField (K := K) (L := L) M hdiscrL,
      Nat.card_prod, IsGalois.card_aut_eq_finrank K L, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient M]
  haveI : Fintype (Gal(Ω/K)) := Fintype.ofFinite _
  haveI : Fintype (Gal(L/K) × (ZMod M)ˣ) := Fintype.ofFinite _
  have hΨbij : Function.Bijective Ψ := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hΨinj, by rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]; exact hcard⟩
  let Ψe : Gal(Ω/K) ≃* Gal(L/K) × (ZMod M)ˣ := MulEquiv.ofBijective Ψ hΨbij
  -- ## The generator `σ`, the unit `ℓ` and the auxiliary automorphism `σtilde`
  obtain ⟨σ, hσgen⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  have hℓunit : IsUnit ((ell : ZMod M)) :=
    (ZMod.isUnit_iff_coprime ell M).mpr ((hell.coprime_iff_not_dvd).mpr hellM)
  let ℓu : (ZMod M)ˣ := hℓunit.unit
  have hℓuval : ((ℓu : (ZMod M)ˣ) : ZMod M) = (ell : ZMod M) := IsUnit.unit_spec hℓunit
  let σtilde : Gal(Ω/K) := Ψe.symm (σ, ℓu)
  have hΨσtilde : Ψ σtilde = (σ, ℓu) := Ψe.apply_symm_apply (σ, ℓu)
  have hρσtilde : σtilde.restrictNormal L = σ := by
    rw [show σtilde.restrictNormal L = (Ψ σtilde).1 from rfl, hΨσtilde]
  have hχσtilde : χ σtilde = ℓu := by
    rw [show χ σtilde = (Ψ σtilde).2 from rfl, hΨσtilde]
  haveI hmmLK : IsMulCommutative (Gal(L/K)) := IsCyclic.isMulCommutative
  haveI hmmU : IsMulCommutative ((ZMod M)ˣ) := inferInstance
  haveI hmmProd : IsMulCommutative (Gal(L/K) × (ZMod M)ˣ) := inferInstance
  have hcommΨ : ∀ x y : Gal(Ω/K), Ψ x * Ψ y = Ψ y * Ψ x :=
    fun x y => (IsMulCommutative.is_comm (M := Gal(L/K) × (ZMod M)ˣ)).comm (Ψ x) (Ψ y)
  have hcomm : ∀ x y : Gal(Ω/K), x * y = y * x := fun x y =>
    hΨinj (by rw [map_mul, map_mul]; exact hcommΨ x y)
  haveI hmmΓ : IsMulCommutative (Gal(Ω/K)) := ⟨⟨hcomm⟩⟩
  -- ## The Frobenius elements at the primes of `s`
  have hPexists : ∀ 𝔭 : s, ∃ P : NK.Chebotarev.PrimeIdeal Ω,
      P.asIdeal.LiesOver ((𝔭 : NK.Chebotarev.PrimeIdeal K)).asIdeal :=
    fun 𝔭 => NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := Ω) (𝔭 : _)
  let P𝔭 : s → NK.Chebotarev.PrimeIdeal Ω := fun 𝔭 => Classical.choose (hPexists 𝔭)
  have hP𝔭 : ∀ 𝔭 : s, (P𝔭 𝔭).asIdeal.LiesOver
      ((𝔭 : NK.Chebotarev.PrimeIdeal K)).asIdeal :=
    fun 𝔭 => Classical.choose_spec (hPexists 𝔭)
  have hFexists : ∀ 𝔭 : s, ∃ F : Gal(Ω/K), NK.Chebotarev.IsFrobAt (P𝔭 𝔭) F :=
    fun 𝔭 => NK.Chebotarev.exists_isFrobAt (K := K) (L := Ω) (𝔭 : _) (P𝔭 𝔭) (hP𝔭 𝔭)
  let F𝔭 : s → Gal(Ω/K) := fun 𝔭 => Classical.choose (hFexists 𝔭)
  have hF𝔭 : ∀ 𝔭 : s, NK.Chebotarev.IsFrobAt (P𝔭 𝔭) (F𝔭 𝔭) :=
    fun 𝔭 => Classical.choose_spec (hFexists 𝔭)
  -- ## The subgroups `H𝔭 = ⟨F𝔭, σtilde⟩`, the global `H` and the field `E`
  let H𝔭 : s → Subgroup Gal(Ω/K) :=
    fun 𝔭 => zpair (F𝔭 𝔭) σtilde (hcomm (F𝔭 𝔭) σtilde)
  let H : Subgroup Gal(Ω/K) := ⨅ 𝔭 : s, H𝔭 𝔭
  let E : IntermediateField K Ω := IntermediateField.fixedField H
  have hσtilde_mem : ∀ 𝔭 : s, σtilde ∈ H𝔭 𝔭 := fun 𝔭 => ⟨0, 1, by simp⟩
  have hF𝔭_mem : ∀ 𝔭 : s, F𝔭 𝔭 ∈ H𝔭 𝔭 := fun 𝔭 => ⟨1, 0, by simp⟩
  have hσtilde_memH : σtilde ∈ H := Subgroup.mem_iInf.mpr hσtilde_mem
  have hE𝔭_le : ∀ 𝔭 : s, IntermediateField.fixedField (H𝔭 𝔭) ≤ E :=
    fun 𝔭 => IntermediateField.fixedField_le (iInf_le (fun 𝔭 : s => H𝔭 𝔭) 𝔭)
  -- ## The cyclotomic component of `F𝔭` is `N𝔭`
  have hFχ : ∀ 𝔭 : s, ((χ (F𝔭 𝔭) : (ZMod M)ˣ) : ZMod M)
      = (Ideal.absNorm ((𝔭 : NK.Chebotarev.PrimeIdeal K)).asIdeal : ZMod M) :=
    fun 𝔭 => aux_frob_autToPow_eq_absNorm (K := K) (L := Ω) M hζ (P𝔭 𝔭)
      (𝔭 : _) (hP𝔭 𝔭) (hnotmem (𝔭 : _) 𝔭.2) (F𝔭 𝔭) (hF𝔭 𝔭)
  -- ## `H𝔭 ∩ ker χ = 1`
  have hHker : ∀ 𝔭 : s, ∀ h ∈ H𝔭 𝔭, χ h = 1 → h = 1 := by
    intro 𝔭 h hh hχ1
    obtain ⟨i, j, hij⟩ := hh
    have hind : ∀ p q : ℕ, (χ (F𝔭 𝔭)) ^ p * ℓu ^ q = 1 →
        Module.finrank K L ∣ p ∧ Module.finrank K L ∣ q := by
      intro p q hpq
      have hc := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) hpq
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one, hℓuval,
        hFχ 𝔭] at hc
      have hc' : ((ell : ZMod M)) ^ q
          * (((Ideal.absNorm ((𝔭 : NK.Chebotarev.PrimeIdeal K)).asIdeal : ℕ)) : ZMod M) ^ p = 1 := by
        rw [mul_comm]
        exact hc
      obtain ⟨hq, hp⟩ := hrel (𝔭 : _) 𝔭.2 q p hc'
      exact ⟨hp, hq⟩
    have hindχ : Module.finrank K L ∣ orderOf (χ (F𝔭 𝔭)) := by
      have h1 : (χ (F𝔭 𝔭)) ^ (orderOf (χ (F𝔭 𝔭))) * ℓu ^ 0 = 1 := by
        rw [pow_orderOf_eq_one, pow_zero, mul_one]
      exact (hind _ _ h1).1
    have hindℓ : Module.finrank K L ∣ orderOf ℓu := by
      have h1 : (χ (F𝔭 𝔭)) ^ 0 * ℓu ^ (orderOf ℓu) = 1 := by
        rw [pow_orderOf_eq_one, pow_zero, one_mul]
      exact (hind _ _ h1).2
    have hordχ0 : orderOf (χ (F𝔭 𝔭)) ≠ 0 := by
      rw [← Nat.card_zpowers]; exact Nat.card_pos.ne'
    have hordℓ0 : orderOf ℓu ≠ 0 := by
      rw [← Nat.card_zpowers]; exact Nat.card_pos.ne'
    have hχeq : (χ (F𝔭 𝔭)) ^ i * ℓu ^ j = 1 := by
      have h := hχ1
      rw [← hij, map_mul, map_zpow, map_zpow, hχσtilde] at h
      exact h
    obtain ⟨hiZ, hjZ⟩ := aux_int_dvd_of_zpow_mul_eq_one (n := Module.finrank K L)
      Module.finrank_pos hordχ0 hordℓ0 hindχ hindℓ hind i j hχeq
    have hρeq : ((F𝔭 𝔭).restrictNormal L) ^ i * σ ^ j = 1 := by
      have h1 : ((F𝔭 𝔭).restrictNormal L) ^ i = 1 := by
        refine orderOf_dvd_iff_zpow_eq_one.mp (dvd_trans ?_ hiZ)
        rw [← IsGalois.card_aut_eq_finrank K L]
        exact Int.natCast_dvd_natCast.mpr (orderOf_dvd_natCard ((F𝔭 𝔭).restrictNormal L))
      have h2 : σ ^ j = 1 := by
        have hordσ : orderOf σ = Module.finrank K L := by
          rw [← Nat.card_zpowers σ, (Subgroup.eq_top_iff' (Subgroup.zpowers σ)).mpr hσgen,
            Nat.card_congr (Subgroup.topEquiv).toEquiv, IsGalois.card_aut_eq_finrank K L]
        exact orderOf_dvd_iff_zpow_eq_one.mp (by rw [hordσ]; exact hjZ)
      rw [h1, h2, one_mul]
    have hΨh : Ψ ((F𝔭 𝔭) ^ i * σtilde ^ j) = 1 := by
      have hρh : ρ ((F𝔭 𝔭) ^ i * σtilde ^ j) = 1 := by
        rw [map_mul, map_zpow, map_zpow]
        rw [show ρ σtilde = σ from hρσtilde]
        exact hρeq
      have hχh : χ ((F𝔭 𝔭) ^ i * σtilde ^ j) = 1 := by
        rw [map_mul, map_zpow, map_zpow, hχσtilde]
        exact hχeq
      exact Prod.ext hρh hχh
    rw [← hij]
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
      (IntermediateField.mem_fixedField_iff H _).mp hxE σtilde hσtilde_memH
    have hsl : σ l = l := by
      have h1 : algebraMap L Ω ((σtilde.restrictNormal L) l) = algebraMap L Ω l := by
        rw [AlgEquiv.restrictNormal_commutes (F := K) (K₁ := Ω) (K₂ := Ω) σtilde L l]
        exact hfx
      rw [hρσtilde] at h1
      exact (algebraMap L Ω).injective h1
    have hσtop : Subgroup.zpowers σ = ⊤ := (Subgroup.eq_top_iff' (Subgroup.zpowers σ)).mpr hσgen
    have hlK : l ∈ (⊥ : IntermediateField K L) := by
      have hlf : l ∈ IntermediateField.fixedField (Subgroup.zpowers σ) := by
        rw [IntermediateField.mem_fixedField_iff]
        intro f hf
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
        exact aux_zpow_apply_fixed σ hsl k
      rw [hσtop, IsGalois.fixedField_top] at hlf
      exact hlf
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hlK
    rw [IntermediateField.mem_bot]
    exact ⟨c, by rw [IsScalarTower.algebraMap_apply K L Ω, hc]⟩
  -- ## `E𝔭 ⊔ K(ζ) = Ω`
  have hkerχ : (IntermediateField.adjoin K ({ζ} : Set Ω)).fixingSubgroup ≤ χ.ker :=
    aux_fixingSubgroup_adjoin_zeta_le_ker (K := K) (L := Ω) M hζ
  have hjoinK : ∀ 𝔭 : s, IntermediateField.fixedField (H𝔭 𝔭) ⊔
      IntermediateField.adjoin K ({ζ} : Set Ω) = ⊤ := by
    intro 𝔭
    have hfix : (IntermediateField.fixedField (H𝔭 𝔭) ⊔
        IntermediateField.adjoin K ({ζ} : Set Ω)).fixingSubgroup = ⊥ := by
      rw [IntermediateField.fixingSubgroup_sup,
        show (IntermediateField.fixedField (H𝔭 𝔭)).fixingSubgroup = H𝔭 𝔭 from
          IntermediateField.fixingSubgroup_fixedField (H𝔭 𝔭)]
      refine le_antisymm ?_ bot_le
      intro x hx
      exact hHker 𝔭 x hx.1 (hkerχ hx.2)
    rw [← IsGalois.fixedField_fixingSubgroup (F := K) (E := Ω)
      (IntermediateField.fixedField (H𝔭 𝔭) ⊔ IntermediateField.adjoin K ({ζ} : Set Ω)), hfix,
      IntermediateField.fixedField_bot]
  -- ## The `ℚ`-level join
  have hjoinℚ : ∀ 𝔭 : s,
      ((IntermediateField.fixedField (H𝔭 𝔭)).restrictScalars ℚ) ⊔
        (IntermediateField.adjoin ℚ ({ζ} : Set Ω)) = ⊤ := by
    intro 𝔭
    let S : IntermediateField ℚ Ω :=
      ((IntermediateField.fixedField (H𝔭 𝔭)).restrictScalars ℚ) ⊔
        (IntermediateField.adjoin ℚ ({ζ} : Set Ω))
    have hsub : ((IntermediateField.fixedField (H𝔭 𝔭) ⊔
        IntermediateField.adjoin K ({ζ} : Set Ω) : IntermediateField K Ω) : Set Ω)
        ⊆ (S : Set Ω) :=
      aux_sup_adjoin_subset (K := K) (L := L) (Ω := Ω)
        (IntermediateField.fixedField (H𝔭 𝔭)) ζ
    have hcoe : (S : Set Ω) = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro x
      exact hsub (by rw [hjoinK 𝔭]; exact Set.mem_univ x)
    exact SetLike.coe_injective (by simpa using hcoe)
  haveI hH𝔭normal : ∀ 𝔭 : s, (H𝔭 𝔭).Normal :=
    fun 𝔭 => Subgroup.normal_of_isMulCommutative _
  haveI hE𝔭gal : ∀ 𝔭 : s, IsGalois K ↥(IntermediateField.fixedField (H𝔭 𝔭)) :=
    fun 𝔭 => IsGalois.of_fixedField_normal_subgroup (H𝔭 𝔭)
  -- ## `𝔭` splits completely in `E𝔭/K`
  have hfrob : ∀ 𝔭 : s,
      NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥(IntermediateField.fixedField (H𝔭 𝔭)))
        (𝔭 : NK.Chebotarev.PrimeIdeal K) 1 := by
    intro 𝔭
    refine ⟨(P𝔭 𝔭).under (𝓞 ↥(IntermediateField.fixedField (H𝔭 𝔭))), ?_, ?_⟩
    · refine Ideal.LiesOver.mk ?_
      rw [NK.Chebotarev.under_asIdeal, Ideal.under_under]
      exact (hP𝔭 𝔭).over
    · have h1 : NK.Chebotarev.IsFrobAt (K := K)
          (L := ↥(IntermediateField.fixedField (H𝔭 𝔭)))
          ((P𝔭 𝔭).under (𝓞 ↥(IntermediateField.fixedField (H𝔭 𝔭))))
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω)
            (IntermediateField.fixedField (H𝔭 𝔭)) (F𝔭 𝔭)) :=
        NK.Chebotarev.IsFrobAtRestrictNormalHom (K := K) (M := Ω)
          (IntermediateField.fixedField (H𝔭 𝔭)) (hP𝔭 𝔭) (hF𝔭 𝔭)
      have h2 : (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω)
          (IntermediateField.fixedField (H𝔭 𝔭)) (F𝔭 𝔭)) = 1 := by
        apply AlgEquiv.ext
        intro x
        apply Subtype.ext
        show ((AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω)
              (IntermediateField.fixedField (H𝔭 𝔭)) (F𝔭 𝔭)) x : Ω) = (1 : ↥(IntermediateField.fixedField (H𝔭 𝔭)) ≃ₐ[K]
                ↥(IntermediateField.fixedField (H𝔭 𝔭))) x
        rw [show ((AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω)
              (IntermediateField.fixedField (H𝔭 𝔭)) (F𝔭 𝔭)) x : Ω) = (F𝔭 𝔭) (x : Ω) from
            AlgEquiv.restrictNormal_commutes (F := K) (K₁ := Ω) (K₂ := Ω) (χ := F𝔭 𝔭)
              (E := ↥(IntermediateField.fixedField (H𝔭 𝔭))) (x := x),
          AlgEquiv.one_apply]
        exact (IntermediateField.mem_fixedField_iff (H𝔭 𝔭) (x : Ω)).mp x.2 (F𝔭 𝔭) (hF𝔭_mem 𝔭)
      rwa [h2] at h1
  exact ⟨E, hEdisj, fun 𝔭 h𝔭 => ⟨IntermediateField.fixedField (H𝔭 ⟨𝔭, h𝔭⟩),
    hE𝔭_le ⟨𝔭, h𝔭⟩, hjoinℚ ⟨𝔭, h𝔭⟩, hfrob ⟨𝔭, h𝔭⟩⟩⟩

end NK.CFTLib.ARL
