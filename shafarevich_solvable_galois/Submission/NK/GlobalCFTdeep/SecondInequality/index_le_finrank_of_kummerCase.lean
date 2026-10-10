import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.Commons.FieldTheory.Galois.le_finrank_of_coprime_intermediate
import Submission.NK.GlobalCFTdeep.Herbrand.CyclicHerbrandQuotient
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.SecondInequality

open NK.GlobalCFT

/-- **The composite of the inclusion `C_F → C_E` with the norm `N_{E/F}` is the
`[E : F]`-th power map**, for a finite Galois extension `E / F` of number fields.

The inclusion `ψ` carries a class to a Galois-invariant class; the norm of an invariant class is
the product of its conjugates, i.e. its `|Gal(E/F)| = [E : F]`-th power. -/
theorem normClassHom_inclusion_eq_pow_of_isGalois
    {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (u : Place E → Place F) (hu : ∀ w : Place E, Place.LiesOver w (u w))
    (φ : Idele F →* Idele E)
    (hφ : ∀ (x : Idele F) (w : Place E),
      φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)))
    (ψ : IdeleClassGroup F →* IdeleClassGroup E)
    (hψ : ∀ x : Idele F, ψ (IdeleClassGroup.mk F x) = IdeleClassGroup.mk E (φ x))
    (x : IdeleClassGroup F) :
    IdeleClassGroup.normClassHom F E (ψ x) = x ^ Module.finrank F E := by
  have hinv : ∀ σ : E ≃ₐ[F] E, σ • (ψ x) = ψ x :=
    (Inclusion.globalCFT_invariants_ideleClassGroup u hu φ hφ ψ hψ (ψ x)).mpr ⟨x, rfl⟩
  have hprod : ψ (IdeleClassGroup.normClassHom F E (ψ x)) =
      ∏ σ : E ≃ₐ[F] E, σ • (ψ x) :=
    globalCFT_normClassHom_eq_prod_smul u hu φ hφ ψ hψ (ψ x)
  have hcard : Nat.card (E ≃ₐ[F] E) = Module.finrank F E := IsGalois.card_aut_eq_finrank F E
  have h1 : (∏ σ : E ≃ₐ[F] E, σ • (ψ x)) = (ψ x) ^ Module.finrank F E := by
    rw [Finset.prod_congr rfl (fun σ _ => hinv σ), Finset.prod_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, hcard]
  have h2 : ψ (IdeleClassGroup.normClassHom F E (ψ x)) = ψ (x ^ Module.finrank F E) := by
    rw [hprod, h1, map_pow]
  exact Inclusion.globalCFT_ideleClassGroup_inclusion_injective u hu φ hφ ψ hψ h2

/-- **The abstract index comparison of Milne's Lemma 6.1.**  Let `ψ : A →* B` be an inclusion of
idèle class groups, `Nm : B →* A` the corresponding norm, `N ≤ A`, `N' ≤ B` the norm subgroups of
the two extensions `E/F` and `E'/F'`.  If

* `Nm ∘ ψ` is the `m`-th power map,
* all `N'`-norms lie in `N`,
* `N` contains all `p`-th powers,
* `m` and `p` are coprime, and `B ⧸ N'` is finite,

then `[A : N] ≤ [B : N']`. -/
theorem index_le_index_of_inclusion_data
    {A B : Type} [CommGroup A] [CommGroup B]
    (ψ : A →* B) (Nm : B →* A) (N : Subgroup A) (N' : Subgroup B) (m p : ℕ)
    (hcop : Nat.Coprime m p)
    (hNm : ∀ y ∈ N', Nm y ∈ N)
    (hid : ∀ x : A, Nm (ψ x) = x ^ m)
    (hpow : ∀ x : A, x ^ p ∈ N)
    (hfin : Finite (B ⧸ N')) :
    N.index ≤ N'.index := by
  classical
  haveI : Finite (B ⧸ N') := hfin
  set f : A →* B ⧸ N' := (QuotientGroup.mk' N').comp ψ with hf
  have hker : f.ker ≤ N := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : ψ x ∈ N' := by
      have hx1 : (QuotientGroup.mk' N') (ψ x) = 1 := hx
      exact (QuotientGroup.eq_one_iff (ψ x)).mp hx1
    have hm : x ^ m ∈ N := by rw [← hid x]; exact hNm (ψ x) hx'
    exact Commons.FieldTheory.Galois.mem_of_pow_mem_of_coprime N x hcop hm (hpow x)
  have hidx : f.ker.index = Nat.card f.range := Subgroup.index_ker f
  haveI : Finite f.range := Finite.of_injective Subtype.val Subtype.val_injective
  have hpos : 0 < f.ker.index := by
    rw [hidx]
    exact Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩
  have hdvd : N.index ∣ f.ker.index := Subgroup.index_dvd_of_le hker
  have h1 : N.index ≤ f.ker.index := Nat.le_of_dvd hpos hdvd
  have hle : Nat.card f.range ≤ Nat.card (B ⧸ N') :=
    Nat.card_le_card_of_injective (Subtype.val : f.range → B ⧸ N') Subtype.val_injective
  have h2 : f.ker.index ≤ N'.index := by
    rw [hidx, Subgroup.index_eq_card]; exact hle
  exact h1.trans h2

/-- **`K(\zeta_p)` is a Galois extension of `K`.**  More precisely, the subfield of `M` generated
over `K` by all `p`-th roots of unity (for `p` prime) is a cyclotomic extension of `K`, hence
Galois over `K`. -/
theorem kummerAdjoin_isGalois {K M : Type} [Field K] [Field M] [Algebra K M]
    {p : ℕ} (hp : p.Prime) {ζ : M} (hζ : IsPrimitiveRoot ζ p) :
    IsGalois K ↥(IntermediateField.adjoin K ({b : M | b ^ p = 1} : Set M)) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hset : ({b : M | ∃ n ∈ ({p} : Set ℕ), n ≠ 0 ∧ b ^ n = 1} : Set M) =
      {b : M | b ^ p = 1} := by
    ext b
    constructor
    · rintro ⟨n, hn, _, hb⟩
      rw [Set.mem_singleton_iff] at hn
      subst hn
      exact hb
    · intro hb
      exact ⟨p, rfl, hp.ne_zero, hb⟩
  have hinst : IsCyclotomicExtension ({p} : Set ℕ) K
      ↥(IntermediateField.adjoin K
        ({b : M | ∃ n ∈ ({p} : Set ℕ), n ≠ 0 ∧ b ^ n = 1} : Set M)) :=
    IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot
      (S := ({p} : Set ℕ)) (K := K) (L := M) (fun n hn _ => by
        rw [Set.mem_singleton_iff] at hn
        subst hn
        exact ⟨ζ, hζ⟩)
  rw [hset] at hinst
  haveI := hinst
  exact IsCyclotomicExtension.isGalois ({p} : Set ℕ) K _

/-- **The degree bound `[K(\zeta_p) : K] ≤ p - 1`.**  The subfield generated over `K` by the
`p`-th roots of unity is `K⟮ζ⟯` for a primitive root `ζ`, whose degree over `K` is the degree of
the minimal polynomial of `ζ`, which divides the `p`-th cyclotomic polynomial of degree `p - 1`. -/
theorem kummerAdjoin_finrank_le {K M : Type} [Field K] [Field M] [Algebra K M]
    {p : ℕ} (hp : p.Prime) {ζ : M} (hζ : IsPrimitiveRoot ζ p) :
    Module.finrank K ↥(IntermediateField.adjoin K ({b : M | b ^ p = 1} : Set M)) ≤ p - 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hset : IntermediateField.adjoin K ({b : M | b ^ p = 1} : Set M) =
      IntermediateField.adjoin K ({ζ} : Set M) := by
    refine le_antisymm ?_ ?_
    · rw [IntermediateField.adjoin_le_iff]
      intro b hb
      obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hb
      have hmem : ζ ∈ (IntermediateField.adjoin K ({ζ} : Set M) : Set M) :=
        IntermediateField.subset_adjoin K ({ζ} : Set M) (by simp)
      have hpw := IntermediateField.pow_mem (S := IntermediateField.adjoin K ({ζ} : Set M))
        hmem (i : ℤ)
      rw [zpow_natCast] at hpw
      rwa [← hi]
    · rw [IntermediateField.adjoin_le_iff]
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      subst hb
      exact IntermediateField.subset_adjoin K ({b : M | b ^ p = 1} : Set M) hζ.pow_eq_one
  rw [hset]
  have hint : IsIntegral K ζ :=
    ⟨Polynomial.X ^ p - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hp.ne_zero, by
      simp [hζ.pow_eq_one]⟩
  rw [IntermediateField.adjoin.finrank hint]
  have hdvd : minpoly K ζ ∣ Polynomial.cyclotomic p K := by
    apply minpoly.dvd
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      Polynomial.map_cyclotomic p (algebraMap K M), ← Polynomial.IsRoot.def]
    exact hζ.isRoot_cyclotomic hp.pos
  calc (minpoly K ζ).natDegree ≤ (Polynomial.cyclotomic p K).natDegree :=
        Polynomial.natDegree_le_of_dvd hdvd (Polynomial.cyclotomic_ne_zero p K)
    _ = p - 1 := by rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hp]

/-- The subfield generated over `K` by the `p`-th roots of unity inside `M`; for `p` prime this
is `K(\zeta_p)`. -/
abbrev kummerSub (K M : Type*) [Field K] [Field M] [Algebra K M] (p : ℕ) : IntermediateField K M :=
  IntermediateField.adjoin K ({b : M | b ^ p = 1} : Set M)

/-- **The Kummer setup.**  Let `L / K` be a finite Galois extension of number fields of prime
degree `p` and let `M = L(\zeta_p)`.  Then the subfield `K(\zeta_p) ≤ M` has index `p` in `M`;
consequently `M / K(\zeta_p)` is cyclic of degree `p`, i.e. the hypotheses of the Kummer case of
the second inequality are met. -/
theorem kummerSub_card_algEquiv {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card (L ≃ₐ[K] L) = p)
    {ζ : CyclotomicField p L} (hζ : IsPrimitiveRoot ζ p) :
    Module.finrank ↥(kummerSub K (CyclotomicField p L) p) (CyclotomicField p L) = p ∧
      Nat.card ((CyclotomicField p L) ≃ₐ[↥(kummerSub K (CyclotomicField p L) p)]
        (CyclotomicField p L)) = p ∧
      IsCyclic ((CyclotomicField p L) ≃ₐ[↥(kummerSub K (CyclotomicField p L) p)]
        (CyclotomicField p L)) ∧
      IsGalois ↥(kummerSub K (CyclotomicField p L) p) (CyclotomicField p L) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  let M := CyclotomicField p L
  let H : IntermediateField K M := kummerSub K M p
  let Ls : IntermediateField K M := (IsScalarTower.toAlgHom K L M).fieldRange
  haveI : IsCyclotomicExtension ({p} : Set ℕ) L M :=
    CyclotomicField.isCyclotomicExtension (K := L) p
  have hLs : Module.finrank K ↥Ls = p := by
    have e : L ≃ₐ[K] ↥Ls := AlgHom.equivFieldRange (IsScalarTower.toAlgHom K L M)
    rw [← e.toLinearEquiv.finrank_eq, ← IsGalois.card_aut_eq_finrank K L, hcard]
  have hHle : Module.finrank K ↥H ≤ p - 1 := kummerAdjoin_finrank_le hp hζ
  have hcop : Nat.Coprime (Module.finrank K ↥Ls) (Module.finrank K ↥H) := by
    rw [hLs]
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hdvd => ?_
    refine absurd (Nat.le_of_dvd (Module.finrank_pos) hdvd) (not_le_of_gt ?_)
    exact lt_of_le_of_lt hHle (Nat.pred_lt hp.ne_zero)
  have hsup : Ls ⊔ H = ⊤ := by
    have hgen : Algebra.adjoin L ({b : M | b ^ p = 1} : Set M) = ⊤ := by
      have hset : ({b : M | ∃ n ∈ ({p} : Set ℕ), n ≠ 0 ∧ b ^ n = 1} : Set M) =
          {b : M | b ^ p = 1} := by
        ext b
        constructor
        · rintro ⟨n, hn, -, hb⟩
          rw [Set.mem_singleton_iff] at hn
          subst hn; exact hb
        · intro hb; exact ⟨p, rfl, hp.ne_zero, hb⟩
      have hiff := (IsCyclotomicExtension.iff_adjoin_eq_top ({p} : Set ℕ) L M).mp
        (CyclotomicField.isCyclotomicExtension (K := L) p)
      rw [hset] at hiff
      exact hiff.2
    have hmem : ∀ x ∈ Algebra.adjoin L ({b : M | b ^ p = 1} : Set M),
        x ∈ (Ls ⊔ H : IntermediateField K M) := by
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem y hy =>
          exact (show (H : IntermediateField K M) ≤ Ls ⊔ H from le_sup_right)
            (IntermediateField.subset_adjoin K _ hy)
      | algebraMap l =>
          exact (show Ls ≤ Ls ⊔ H from le_sup_left)
            (AlgHom.mem_fieldRange.mpr ⟨l, rfl⟩)
      | add y z hy hz ihy ihz => exact add_mem ihy ihz
      | mul y z hy hz ihy ihz => exact mul_mem ihy ihz
    refine le_antisymm le_top ?_
    intro x _
    exact hmem x (by rw [hgen]; trivial)
  haveI : IsGalois K ↥Ls := by
    have h : IsGalois K ↥(IsScalarTower.toAlgHom K L M).fieldRange :=
      IsGalois.of_algEquiv (AlgHom.equivFieldRange (IsScalarTower.toAlgHom K L M))
    exact h
  have hLD : Ls.LinearDisjoint ↥H := IntermediateField.LinearDisjoint.of_finrank_coprime hcop
  have hfr : Module.finrank ↥H M = p := by
    rw [hLD.finrank_right_eq_finrank hsup, hLs]
  haveI : IsGalois ↥H M := IsGalois.sup_right Ls H hsup
  have hMcard : Nat.card (M ≃ₐ[↥H] M) = p := by
    rw [IsGalois.card_aut_eq_finrank ↥H M, hfr]
  have hcyc : IsCyclic (M ≃ₐ[↥H] M) := isCyclic_of_prime_card hMcard
  exact ⟨hfr, hMcard, hcyc, ‹IsGalois ↥H M›⟩

/-- The degree of `K(\zeta_p)` over `K` is coprime to `p`. -/
theorem kummerSub_finrank_coprime {K M : Type} [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M]
    {p : ℕ} (hp : p.Prime) {ζ : M} (hζ : IsPrimitiveRoot ζ p) :
    Nat.Coprime (Module.finrank K ↥(kummerSub K M p)) p := by
  have hle : Module.finrank K ↥(kummerSub K M p) ≤ p - 1 := kummerAdjoin_finrank_le hp hζ
  refine ((Nat.Prime.coprime_iff_not_dvd hp).mpr ?_).symm
  intro hdvd
  refine absurd (Nat.le_of_dvd (Module.finrank_pos) hdvd) (not_le_of_gt ?_)
  exact lt_of_le_of_lt hle (Nat.pred_lt hp.ne_zero)

theorem index_le_finrank_of_kummerCase
    (hK : ∀ {K' L' : Type} [Field K'] [NumberField K'] [Field L'] [NumberField L']
      [Algebra K' L'] [FiniteDimensional K' L'] [IsGalois K' L'] [IsCyclic (L' ≃ₐ[K'] L')]
      {p : ℕ}, p.Prime → Nat.card (L' ≃ₐ[K'] L') = p → ∀ {ζ : K'}, IsPrimitiveRoot ζ p →
      (NK.GlobalCFT.Idele.normClassSubgroup K' L').index ≤ Module.finrank K' L')
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    [Fact (Nat.Prime (Nat.card (L ≃ₐ[K] L)))] :
    (NK.GlobalCFT.Idele.normClassSubgroup K L).index ≤ Module.finrank K L := by
  classical
  set p := Nat.card (L ≃ₐ[K] L) with hpdef
  have hp : p.Prime := hpdef ▸ Fact.out
  have hcard : Nat.card (L ≃ₐ[K] L) = p := hpdef.symm
  have hfl : Module.finrank K L = p := by
    rw [← IsGalois.card_aut_eq_finrank K L, hcard]
  by_cases hroot : ∃ ζ : K, IsPrimitiveRoot ζ p
  · obtain ⟨ζ, hζ⟩ := hroot
    exact hK hp hcard hζ
  · haveI : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨ζ, hζ⟩ : ∃ ζ : CyclotomicField p L, IsPrimitiveRoot ζ p := by
      have h := CyclotomicField.isCyclotomicExtension (K := L) p
      rw [isCyclotomicExtension_iff] at h
      exact h.1 (by simp) hp.ne_zero
    let M := CyclotomicField p L
    let H : IntermediateField K M := kummerSub K M p
    obtain ⟨hfr, hMcard, hcyc, hgalHM⟩ := kummerSub_card_algEquiv hp hcard hζ
    haveI : IsCyclic (M ≃ₐ[↥H] M) := hcyc
    haveI : IsGalois ↥H M := hgalHM
    haveI : IsGalois K ↥H := kummerAdjoin_isGalois hp hζ
    have hζH : ζ ∈ H := IntermediateField.subset_adjoin K _ hζ.pow_eq_one
    have hζ' : IsPrimitiveRoot (⟨ζ, hζH⟩ : ↥H) p :=
      IsPrimitiveRoot.of_map_of_injective (f := (algebraMap ↥H M)) (by simpa using hζ)
        (RingHom.injective _)
    have hKM : (Idele.normClassSubgroup ↥H M).index ≤ Module.finrank ↥H M :=
      hK (K' := ↥H) (L' := M) hp hMcard hζ'
    have h1ineq : Module.finrank ↥H M ≤ (Idele.normClassSubgroup ↥H M).index :=
      NK.GlobalCFT.first_inequality_of_herbrandQuotient
        (NK.GlobalCFT.globalCFT_H0Computation (K := ↥H) (L := M))
        (NK.GlobalCFTdeep.cyclicHerbrandQuotient.herbrand (K := ↥H) (L := M))
    have hidx : (Idele.normClassSubgroup ↥H M).index = p :=
      le_antisymm (hKM.trans (le_of_eq hfr)) ((le_of_eq hfr.symm).trans h1ineq)
    have hfin : Finite (IdeleClassGroup ↥H ⧸ Idele.normClassSubgroup ↥H M) :=
      Subgroup.index_ne_zero_iff_finite.mp (by rw [hidx]; exact hp.ne_zero)
    obtain ⟨u, hu⟩ : ∃ u : Place ↥H → Place K, ∀ w, Place.LiesOver w (u w) :=
      ⟨fun w => Classical.choose (Inclusion.globalCFT_exists_placeUnder (K := K) (L := ↥H) w),
        fun w => Classical.choose_spec
          (Inclusion.globalCFT_exists_placeUnder (K := K) (L := ↥H) w)⟩
    obtain ⟨φ, hφ⟩ := Inclusion.globalCFT_ideleInclusion_exists (K := K) (L := ↥H) u hu
    obtain ⟨ψ, hψ⟩ :=
      Inclusion.globalCFT_ideleClassGroup_inclusion_exists (K := K) (L := ↥H) u hu φ hφ
    have hid : ∀ x : IdeleClassGroup K,
        IdeleClassGroup.normClassHom K ↥H (ψ x) = x ^ Module.finrank K ↥H :=
      fun x => normClassHom_inclusion_eq_pow_of_isGalois u hu φ hφ ψ hψ x
    have hNm : ∀ y ∈ Idele.normClassSubgroup ↥H M,
        IdeleClassGroup.normClassHom K ↥H y ∈ Idele.normClassSubgroup K L := by
      intro y hy
      obtain ⟨z, rfl⟩ := Idele.mem_normClassSubgroup.mp hy
      rw [NormGroup.globalCFT_normClassHom_trans (K := K) (L := ↥H) (M := M) z]
      exact (show Idele.normClassSubgroup K M ≤ Idele.normClassSubgroup K L from
          Idele.normClassSubgroup_le_of_tower)
        (Idele.mem_normClassSubgroup.mpr ⟨z, rfl⟩)
    obtain ⟨u₂, hu₂⟩ : ∃ u : Place L → Place K, ∀ w, Place.LiesOver w (u w) :=
      ⟨fun w => Classical.choose (Inclusion.globalCFT_exists_placeUnder (K := K) (L := L) w),
        fun w => Classical.choose_spec
          (Inclusion.globalCFT_exists_placeUnder (K := K) (L := L) w)⟩
    obtain ⟨φ₂, hφ₂⟩ := Inclusion.globalCFT_ideleInclusion_exists (K := K) (L := L) u₂ hu₂
    obtain ⟨ψ₂, hψ₂⟩ :=
      Inclusion.globalCFT_ideleClassGroup_inclusion_exists (K := K) (L := L) u₂ hu₂ φ₂ hφ₂
    have hid₂ := normClassHom_inclusion_eq_pow_of_isGalois u₂ hu₂ φ₂ hφ₂ ψ₂ hψ₂
    have hpow : ∀ x : IdeleClassGroup K, x ^ p ∈ Idele.normClassSubgroup K L := by
      intro x
      rw [← hfl, ← hid₂ x]
      exact Idele.mem_normClassSubgroup.mpr ⟨ψ₂ x, rfl⟩
    have hcop : Nat.Coprime (Module.finrank K ↥H) p := kummerSub_finrank_coprime hp hζ
    have hmain : (Idele.normClassSubgroup K L).index ≤ (Idele.normClassSubgroup ↥H M).index :=
      index_le_index_of_inclusion_data ψ (IdeleClassGroup.normClassHom K ↥H)
        (Idele.normClassSubgroup K L) (Idele.normClassSubgroup ↥H M) (Module.finrank K ↥H) p
        hcop hNm hid hpow hfin
    rw [hfl]
    exact hmain.trans (hKM.trans (le_of_eq hfr))

end NK.GlobalCFTdeep.SecondInequality
