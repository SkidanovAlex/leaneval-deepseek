import Mathlib
import Submission.NK.CFTLib.ARL.Cyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxHeartbeats 400000

/-!
# `L ∩ K(ζ_M) = K` for `L/K` Galois and `M` coprime to `discr L`

This module proves `NK.CFTLib.ARL.disjoint_restrictScalars_adjoin_zeta`, the statement that the
image of `L` in `L(ζ_M)` meets `K(ζ_M)` exactly in `K`, whenever no prime divisor of `M` divides
the discriminant of `L`.

The proof generalises `NK.CFTLib.ArtinReciprocityIdeal.cyclotomic_inf_eq_bot` (the case `M = q`
prime) from a prime to an arbitrary natural number.  The arithmetic input is the ℚ-level statement
`intersect_cyclotomic_eq_bot_gen`: a number field unramified at all prime divisors of `M` meets
`ℚ(ζ_M)` in `ℚ`, proved by the discriminant argument (`E := ℚ(ζ_M) ∩ F` has
`discr E ∣ discr ℚ(ζ_M)` and `discr E ∣ discr F`; every prime dividing `discr ℚ(ζ_M)` divides `M`,
by `prime_dvd_of_dvd_discr_cyclotomic`; hence `discr E = ±1` and `E = ℚ`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open scoped NumberField
open IntermediateField

noncomputable section

namespace NK.CFTLib.ARL

/-- **Every prime dividing the discriminant of a cyclotomic extension of `ℚ` of conductor `M`
divides `M`.**  Indeed, if `p ∤ M` then `p` is unramified in `K = ℚ(ζ_M)`
(`IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd`), so `p ∤ discr K`. -/
theorem prime_dvd_of_dvd_discr_cyclotomic {K : Type*} [Field K] [NumberField K] (M : ℕ) [NeZero M]
    [IsCyclotomicExtension {M} ℚ K] {p : ℕ} (hp : p.Prime)
    (h : p ∣ (NumberField.discr K).natAbs) : p ∣ M := by
  by_contra hpm
  haveI : Fact p.Prime := ⟨hp⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hnd : ¬ (p : ℤ) ∣ NumberField.discr K := by
    rw [NumberField.not_dvd_discr_iff_forall_liesOver K (𝓞 K) hpZ]
    intro P hPmax hP
    haveI : P.IsPrime := hPmax.isPrime
    haveI : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := hP
    exact Ideal.ramificationIdx_eq_one_iff.mp
      (IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p K P hpm)
  exact hnd (by rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]; exact h)

/-- **A number field `E` embedded both in a cyclotomic field of conductor `M` and in a number
field `F` unramified at the prime divisors of `M` is `ℚ`.**  Discriminant form of the key input:
`discr E` divides both `discr(ℚ(ζ_M))` (whose prime divisors divide `M`) and `discr F` (whose
prime divisors are avoided by the hypothesis), hence `discr E = ±1` and `[E : ℚ] = 1`. -/
theorem finrank_eq_one_of_isCyclotomic_of_unramified_gen
    {E K F : Type*} [Field E] [NumberField E] [Field K] [NumberField K] [Field F] [NumberField F]
    (M : ℕ) [NeZero M] [IsCyclotomicExtension {M} ℚ K]
    (hunr : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr F).natAbs)
    (i₁ : E →+* K) (i₂ : E →+* F) : Module.finrank ℚ E = 1 := by
  letI algK : Algebra E K := i₁.toAlgebra
  letI algF : Algebra E F := i₂.toAlgebra
  have h1 : NumberField.discr E ∣ NumberField.discr K := NumberField.discr_dvd_discr E K
  have h2 : NumberField.discr E ∣ NumberField.discr F := NumberField.discr_dvd_discr E F
  -- No prime divides `discr E`.
  have hnone : (NumberField.discr E).natAbs = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hne
    have hpK : p ∣ (NumberField.discr K).natAbs :=
      dvd_trans hpn (Int.natAbs_dvd_natAbs.mpr h1)
    have hpF : p ∣ (NumberField.discr F).natAbs :=
      dvd_trans hpn (Int.natAbs_dvd_natAbs.mpr h2)
    exact hunr p hp (prime_dvd_of_dvd_discr_cyclotomic M hp hpK) hpF
  have hunit : IsUnit (NumberField.discr E) := by
    rcases Int.natAbs_eq_iff.mp hnone with h | h <;> rw [h] <;> simp
  -- so `discr E = ±1`, forcing `[E : ℚ] = 1`.
  by_contra hne
  have hgt : 1 < Module.finrank ℚ E := by
    have := Module.finrank_pos (R := ℚ) (M := E)
    omega
  have h2' := NumberField.abs_discr_gt_two (K := E) hgt
  rw [Int.isUnit_iff_abs_eq.mp hunit] at h2'
  omega

/-- **A number field unramified at the prime divisors of `M` meets `ℚ(ζ_M)` in `ℚ`.**  Let `F` be
a number field embedded as a subfield of a field `Ω`, let `M ≥ 1` be such that no prime divisor of
`M` divides `discr F`, and let `ζ ∈ Ω` be a primitive `M`-th root of unity.  Then
`ℚ(ζ) ∩ F = ℚ` inside `Ω`.

This is `NK.CFTLib.RouteB.intersect_cyclotomic_eq_bot` with the prime `q` replaced by an
arbitrary `M`; the proof is identical, with `finrank_eq_one_of_isCyclotomic_of_unramified_gen` in
place of `finrank_eq_one_of_isCyclotomic_of_unramified`. -/
theorem intersect_cyclotomic_eq_bot_gen {F Ω : Type*} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [Algebra ℚ Ω] [IsScalarTower ℚ F Ω]
    (M : ℕ) [NeZero M]
    (hunr : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr F).natAbs)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ M) :
    (IntermediateField.adjoin ℚ ({ζ} : Set Ω) : IntermediateField ℚ Ω) ⊓
      (⊥ : IntermediateField F Ω).restrictScalars ℚ = ⊥ := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  -- `ζ` is algebraic over `ℚ` (it is a root of `X ^ M - 1`).
  have hζalg : IsAlgebraic ℚ ζ := by
    refine ⟨Polynomial.X ^ M - Polynomial.C 1, ?_, ?_⟩
    · exact (Polynomial.monic_X_pow_sub_C (1 : ℚ) (NeZero.ne M)).ne_zero
    · simp [Polynomial.aeval_X_pow, hζ.pow_eq_one]
  -- The two subfields of `Ω` whose intersection is to be computed.
  let K₁ : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ ({ζ} : Set Ω)
  let K₂ : IntermediateField ℚ Ω := (⊥ : IntermediateField F Ω).restrictScalars ℚ
  change K₁ ⊓ K₂ = ⊥
  -- `ℚ⟮ζ⟯` is a cyclotomic extension of conductor `M`.
  have hm : K₁.toSubalgebra = Algebra.adjoin ℚ ({ζ} : Set Ω) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζalg]
  have e1 := Subalgebra.equivOfEq _ _ hm
  have hcycA := by
    letI : Algebra ℚ ↥K₁ := K₁.algebra'
    haveI h0 : IsCyclotomicExtension {M} ℚ ↥(Algebra.adjoin ℚ ({ζ} : Set Ω)) :=
      hζ.adjoin_isCyclotomicExtension ℚ
    exact IsCyclotomicExtension.equiv {M} ℚ ↥(Algebra.adjoin ℚ ({ζ} : Set Ω)) e1.symm
  -- `↥K₁` carries two (provably equal) `ℚ`-algebra structures; we work in the canonical one.
  have heq : (K₁).algebra' = (DivisionRing.toRatAlgebra : Algebra ℚ ↥K₁) := Subsingleton.elim _ _
  haveI hcyc1 : IsCyclotomicExtension {M} ℚ ↥K₁ := heq ▸ hcycA
  haveI hN1 : NumberField ↥K₁ := IsCyclotomicExtension.numberField {M} ℚ ↥K₁
  -- The intersection, transported to `F` along `algebraMap F Ω`.
  let φ : F →ₐ[ℚ] Ω := IsScalarTower.toAlgHom ℚ F Ω
  let E_F : IntermediateField ℚ F := K₁.comap φ
  haveI hE : NumberField ↥E_F := NumberField.of_intermediateField (K := ℚ) (L := F) E_F
  have hi1 : ↥E_F →+* ↥K₁ := by
    refine (AlgHom.codRestrict (φ.comp E_F.val) K₁.toSubalgebra (fun y => ?_)).toRingHom
    exact y.2
  have hi2 : ↥E_F →+* F := E_F.val.toRingHom
  have hfin : Module.finrank ℚ ↥E_F = 1 :=
    finrank_eq_one_of_isCyclotomic_of_unramified_gen M hunr hi1 hi2
  have hEF : E_F = ⊥ := IntermediateField.finrank_eq_one_iff.mp hfin
  -- Elementwise conclusion: every element of the intersection lies in the image of `ℚ`.
  rw [eq_bot_iff]
  intro x hx
  rw [IntermediateField.mem_inf] at hx
  obtain ⟨hx1, hx2⟩ := hx
  rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_bot] at hx2
  obtain ⟨f, rfl⟩ := hx2
  rw [IntermediateField.mem_bot]
  have hf : f ∈ E_F := hx1
  rw [hEF, IntermediateField.mem_bot] at hf
  obtain ⟨c, rfl⟩ := hf
  exact ⟨c, IsScalarTower.algebraMap_apply ℚ F Ω c⟩

/-- A form of `IntermediateField.LinearDisjoint.of_inf_eq_bot` whose `IsGalois` instance is an
explicit argument (the type-class search does not reliably find it at the application site when
the ambient field's `ℚ`-algebra structure is a local instance). -/
private theorem ld_of_inf_eq_bot {F E : Type*} [Field F] [Field E] [Algebra F E]
    {A B : IntermediateField F E} [IsGalois F ↥A] [FiniteDimensional F ↥A]
    [FiniteDimensional F ↥B] (h : A ⊓ B = ⊥) : A.LinearDisjoint ↥B :=
  IntermediateField.LinearDisjoint.of_inf_eq_bot h

/-- **The image of `L` in `L(ζ_M)` meets `K(ζ_M)` in `K`** (general form, for an arbitrary ambient
field `Ω` containing a primitive `M`-th root of unity `ζ`).

Both `S := L` and `T := K(ζ_M)` contain `K`; the `ℚ`-level disjointness inputs
`ℚ(ζ) ⊓ L = ℚ` and `ℚ(ζ) ⊓ K = ℚ` (`intersect_cyclotomic_eq_bot_gen`) compute the degrees
`[T : K] = φ(M)` and `[K : S ⊔ T] = [S : K]·φ(M)`, whence `S.LinearDisjoint T` and
`S ⊓ T = ⊥`. -/
theorem disjoint_restrictScalars_adjoin_zeta_gen {K L Ω : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    (M : ℕ) [NeZero M]
    (hM : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr L).natAbs)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ M) :
    Disjoint ((⊥ : IntermediateField L Ω).restrictScalars K)
      (IntermediateField.adjoin K ({ζ} : Set Ω)) := by
  classical
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  haveI hTowerL : IsScalarTower ℚ L Ω :=
    IsScalarTower.of_algebraMap_eq fun x => by simp [map_ratCast]
  haveI hTowerK : IsScalarTower ℚ K Ω :=
    IsScalarTower.of_algebraMap_eq fun x => by simp [map_ratCast]
  -- The hypothesis at `K`, using `discr K ∣ discr L`.
  have hMK : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr K).natAbs := by
    have hd : (NumberField.discr K).natAbs ∣ (NumberField.discr L).natAbs :=
      Int.natAbs_dvd_natAbs.mpr (NumberField.discr_dvd_discr K L)
    intro p hp hpm hpk
    exact hM p hp hpm (dvd_trans hpk hd)
  -- ## The subfields of `Ω` playing a role
  set Qζ : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ ({ζ} : Set Ω) with hQζ
  set Lq : IntermediateField ℚ Ω := (⊥ : IntermediateField L Ω).restrictScalars ℚ with hLq
  set Kq : IntermediateField ℚ Ω := (⊥ : IntermediateField K Ω).restrictScalars ℚ with hKq
  set S : IntermediateField K Ω := (⊥ : IntermediateField L Ω).restrictScalars K with hS
  set T : IntermediateField K Ω := IntermediateField.adjoin K ({ζ} : Set Ω) with hT
  rw [disjoint_iff]
  change S ⊓ T = ⊥
  -- ## `ℚ(ζ)` is disjoint from the images of `K` and of `L`
  have hdisjL : Qζ ⊓ Lq = ⊥ := by
    rw [hQζ, hLq]
    exact intersect_cyclotomic_eq_bot_gen (F := L) M hM ζ hζ
  have hdisjK : Qζ ⊓ Kq = ⊥ := by
    rw [hQζ, hKq]
    exact intersect_cyclotomic_eq_bot_gen (F := K) M hMK ζ hζ
  -- ## `ℚ(ζ)` as a cyclotomic field
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
  -- ## finiteness / degrees of the images
  haveI hKqfd : FiniteDimensional ℚ ↥Kq := by
    rw [hKq]
    exact FiniteDimensional.trans ℚ K ↥(⊥ : IntermediateField K Ω)
  haveI hLqfd : FiniteDimensional ℚ ↥Lq := by
    rw [hLq]
    exact FiniteDimensional.trans ℚ L ↥(⊥ : IntermediateField L Ω)
  haveI hSfd : FiniteDimensional K ↥S := by
    rw [hS]
    exact FiniteDimensional.trans K L ↥(⊥ : IntermediateField L Ω)
  haveI hTfd : FiniteDimensional K ↥T := by
    rw [hT]
    exact IntermediateField.finiteDimensional_adjoin (S := ({ζ} : Set Ω)) (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      exact hx ▸ (hζ.isIntegral (NeZero.pos M)).tower_top)
  have hfrKq : Module.finrank ℚ ↥Kq = Module.finrank ℚ K := by
    have h : Module.finrank ℚ ↥(⊥ : IntermediateField K Ω) = Module.finrank ℚ K := by
      rw [← Module.finrank_mul_finrank ℚ K ↥(⊥ : IntermediateField K Ω),
        (IntermediateField.botEquiv K Ω).toLinearEquiv.finrank_eq, Module.finrank_self, mul_one]
    exact h
  have hfrLq : Module.finrank ℚ ↥Lq = Module.finrank K L * Module.finrank ℚ K := by
    have hbot : Module.finrank ℚ ↥Lq = Module.finrank ℚ L := by
      have h : Module.finrank ℚ ↥(⊥ : IntermediateField L Ω) = Module.finrank ℚ L := by
        rw [← Module.finrank_mul_finrank ℚ L ↥(⊥ : IntermediateField L Ω),
          (IntermediateField.botEquiv L Ω).toLinearEquiv.finrank_eq, Module.finrank_self, mul_one]
      exact h
    rw [hbot, ← Module.finrank_mul_finrank ℚ K L, mul_comm]
  have hfrS : Module.finrank K ↥S = Module.finrank K L := by
    rw [show Module.finrank K ↥S = Module.finrank K ↥(⊥ : IntermediateField L Ω) from rfl,
      ← Module.finrank_mul_finrank K L ↥(⊥ : IntermediateField L Ω),
      (IntermediateField.botEquiv L Ω).toLinearEquiv.finrank_eq, Module.finrank_self, mul_one]
  -- ## `T` restricted to `ℚ` is `Kq ⊔ Qζ`
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
  have hSℚ : S.restrictScalars ℚ = Lq := by
    rw [hS, hLq]
    refine SetLike.ext fun x => ?_
    simp [IntermediateField.mem_restrictScalars]
  have hKq_le_Lq : Kq ≤ Lq := by
    intro x hx
    have hxK : x ∈ (⊥ : IntermediateField K Ω) :=
      (IntermediateField.mem_restrictScalars ℚ).mp (hKq ▸ hx)
    obtain ⟨y, rfl⟩ := (IntermediateField.mem_bot).mp hxK
    rw [hLq]
    exact (IntermediateField.mem_restrictScalars ℚ).mpr
      ((IntermediateField.mem_bot).mpr ⟨algebraMap K L y, by
        rw [IsScalarTower.algebraMap_apply K L Ω]⟩)
  -- ## `[K : T] = φ(M)`
  have hfrT : Module.finrank K ↥T = M.totient := by
    have h1 : Module.finrank ℚ K * Module.finrank K ↥T = Module.finrank ℚ ↥T :=
      Module.finrank_mul_finrank ℚ K ↥T
    have h2 : Module.finrank ℚ ↥T = Module.finrank ℚ K * M.totient := by
      have heq : Module.finrank ℚ ↥T = Module.finrank ℚ ↥(Kq ⊔ Qζ) := by
        rw [show Module.finrank ℚ ↥T = Module.finrank ℚ ↥(T.restrictScalars ℚ) from rfl, hTℚ]
      rw [heq, sup_comm]
      have hLDK : Qζ.LinearDisjoint ↥Kq :=
        @ld_of_inf_eq_bot ℚ Ω _ _ _ Qζ Kq hQζgal _ _ hdisjK
      rw [IntermediateField.LinearDisjoint.finrank_sup hLDK, hfrQζ, hfrKq]
      ring
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h1
  -- ## `[K : S ⊔ T] = [L : K] * φ(M)`
  have hfrSup : Module.finrank K ↥(S ⊔ T) = Module.finrank K L * M.totient := by
    have h1 : Module.finrank ℚ K * Module.finrank K ↥(S ⊔ T) = Module.finrank ℚ ↥(S ⊔ T) :=
      Module.finrank_mul_finrank ℚ K ↥(S ⊔ T)
    have h2 : Module.finrank ℚ ↥(S ⊔ T) =
        Module.finrank ℚ K * (Module.finrank K L * M.totient) := by
      have heq : Module.finrank ℚ ↥(S ⊔ T) = Module.finrank ℚ ↥(Lq ⊔ Qζ) := by
        rw [show Module.finrank ℚ ↥(S ⊔ T) =
            Module.finrank ℚ ↥((S ⊔ T).restrictScalars ℚ) from rfl,
          ← IntermediateField.restrictScalars_sup ℚ S T, hSℚ, hTℚ, ← sup_assoc,
          sup_eq_left.mpr hKq_le_Lq]
      rw [heq, sup_comm]
      have hLD_L : Qζ.LinearDisjoint ↥Lq :=
        @ld_of_inf_eq_bot ℚ Ω _ _ _ Qζ Lq hQζgal _ _ hdisjL
      rw [IntermediateField.LinearDisjoint.finrank_sup hLD_L, hfrQζ, hfrLq]
      ring
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h1
  have hLD_eq : Module.finrank K ↥(S ⊔ T) = Module.finrank K ↥S * Module.finrank K ↥T := by
    rw [hfrSup, hfrS, hfrT]
  exact IntermediateField.LinearDisjoint.inf_eq_bot
    (IntermediateField.LinearDisjoint.of_finrank_sup hLD_eq)

/-- **`L ∩ K(ζ_M) = K` in `L(ζ_M)`**: the image of `L` in `CyclotomicField M L = L(ζ_M)` meets
`K(ζ_M)` exactly in `K`, for `L/K` finite Galois and `M` not divisible by any prime ramified in
`L/ℚ`. -/
theorem disjoint_restrictScalars_adjoin_zeta {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (M : ℕ) [NeZero M]
    (hM : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr L).natAbs) :
    Disjoint ((⊥ : IntermediateField L (CyclotomicField M L)).restrictScalars K)
      (IntermediateField.adjoin K
        ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} : Set (CyclotomicField M L))) := by
  exact disjoint_restrictScalars_adjoin_zeta_gen (Ω := CyclotomicField M L) M hM _
    (IsCyclotomicExtension.zeta_spec M L (CyclotomicField M L))

end NK.CFTLib.ARL
