import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.NK.CFTLib.RouteB.exists_cyclic_subfield_of_isCyclotomic
import Submission.NK.CFTLib.RouteB.intersect_cyclotomic_eq_bot

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option linter.style.haveILetI false

open scoped NumberField
open IntermediateField

namespace NK.GFC

/-! ## Auxiliary constructions -/

/-- The ring hom `↥L → Ωb` given by the composite inclusion `↥L ↪ ↥E ↪ Ωb`, for
`L : IntermediateField K ↥E` and `E : IntermediateField K Ωb`. -/
noncomputable def restrictToAmbient {K Ωb : Type} [Field K] [Field Ωb] [Algebra K Ωb]
    (E : IntermediateField K Ωb) (L : IntermediateField K ↥E) : ↥L →+* Ωb :=
  (E.val.comp L.val).toRingHom

/-- The range of `restrictToAmbient E L` is the image `L.lift` of `L` in `Ωb`. -/
theorem range_restrictToAmbient {K Ωb : Type} [Field K] [Field Ωb] [Algebra K Ωb]
    (E : IntermediateField K Ωb) (L : IntermediateField K ↥E) :
    Set.range (restrictToAmbient E L) = (IntermediateField.lift L : Set Ωb) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact (IntermediateField.mem_lift x.1).mpr x.2
  · intro hz
    have hzE : z ∈ E := IntermediateField.lift_le L hz
    exact ⟨⟨⟨z, hzE⟩, (IntermediateField.mem_lift (⟨z, hzE⟩ : ↥E)).mp hz⟩, rfl⟩

/-- `Ω.restrictScalars K` with the scalar-tower instance supplied explicitly.  (The implicit
instance search for `IsScalarTower K ↥L Ω` misfires here because `SMul ↥L Ωb` is resolved through
the `SetLike` machinery rather than through the given `Algebra ↥L Ωb` instance.) -/
noncomputable def restrictScalarsExplicit {K E : Type*} [Field K] [Field E] [Algebra K E]
    {L' : Type*} [Field L'] [Algebra K L'] [Algebra L' E] (h : IsScalarTower K L' E)
    (Ω : IntermediateField L' E) : IntermediateField K E :=
  @IntermediateField.restrictScalars K E L' _ _ _ _ _ _ h Ω

/-- **The auxiliary prime.**  For every `n ≥ 1` and number fields `K, L` there is a prime `q` with
`n ∣ q - 1` and `q ∤ |disc K|`, `q ∤ |disc L|`.

Proof: Dirichlet's theorem (`Nat.forall_exists_prime_gt_and_eq_mod`) applied to `1` modulo
`m := n * (|disc K| + |disc L| + 1)` produces a prime `q ≡ 1 [MOD m]`;  a prime congruent to `1`
modulo the positive integer `m` is strictly larger than `m > |disc K|, |disc L|`, hence coprime to
them. -/
theorem aux_prime (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (n : ℕ) (hn : 0 < n) :
    ∃ q : ℕ, Nat.Prime q ∧ n ∣ q - 1 ∧ ¬ q ∣ (NumberField.discr K).natAbs ∧
      ¬ q ∣ (NumberField.discr L).natAbs := by
  classical
  set D : ℕ := (NumberField.discr K).natAbs + (NumberField.discr L).natAbs + 1 with hD
  have hDpos : 0 < D := by omega
  set m : ℕ := n * D with hm
  have hmpos : 0 < m := Nat.mul_pos hn hDpos
  haveI : NeZero m := ⟨hmpos.ne'⟩
  obtain ⟨q, -, hqprime, hqmod⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := m) (a := 1) isUnit_one 0
  have hq2 : 2 ≤ q := hqprime.two_le
  -- `m ∣ q - 1`
  have hm_dvd : m ∣ q - 1 := by
    have hz : ((q : ℤ) : ZMod m) = 1 := by
      rw [← hqmod]; push_cast; ring
    have h1 : (((q : ℤ) - 1 : ℤ) : ZMod m) = 0 := by
      calc (((q : ℤ) - 1 : ℤ) : ZMod m) = ((q : ℤ) : ZMod m) - 1 := by push_cast; ring
        _ = 0 := by rw [hz]; ring
    have h2 : (m : ℤ) ∣ ((q : ℤ) - 1) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp h1
    have h3 : (m : ℤ) ∣ ((q - 1 : ℕ) : ℤ) := by
      rw [show ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 from by omega]
      exact h2
    exact_mod_cast h3
  have hn_dvd : n ∣ q - 1 := dvd_trans (by rw [hm]; exact dvd_mul_right n D) hm_dvd
  -- `q > |disc K|`, `q > |disc L|`
  have hqsub : q - 1 ≠ 0 := by omega
  have hm_le : m ≤ q - 1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hqsub) hm_dvd
  have hDE : D ≤ m := by rw [hm]; exact Nat.le_mul_of_pos_left D hn
  have hqD : D < q := by omega
  refine ⟨q, hqprime, hn_dvd, ?_, ?_⟩
  · intro hdiv
    have hpos : 0 < (NumberField.discr K).natAbs :=
      Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)
    have hle : (NumberField.discr K).natAbs ≤ D := by rw [hD]; omega
    have := Nat.le_of_dvd hpos hdiv
    omega
  · intro hdiv
    have hpos : 0 < (NumberField.discr L).natAbs :=
      Int.natAbs_pos.mpr (NumberField.discr_ne_zero L)
    have hle : (NumberField.discr L).natAbs ≤ D := by rw [hD]; omega
    have := Nat.le_of_dvd hpos hdiv
    omega

/-- **A prime not dividing the discriminant is unramified** (`F` a number field). -/
theorem unramified_of_not_dvd_discr {F : Type} [Field F] [NumberField F] {q : ℕ}
    (hq : Nat.Prime q) (h : ¬ q ∣ (NumberField.discr F).natAbs) :
    ∀ P : Ideal (𝓞 F), P.IsPrime →
      P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) → P.ramificationIdx ℤ = 1 := by
  intro P hP hlies
  have hpZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hnotdvd : ¬ (q : ℤ) ∣ NumberField.discr F := by
    intro hd
    apply h
    have := (Int.natAbs_dvd_natAbs (a := (q : ℤ)) (b := NumberField.discr F)).mpr hd
    simpa using this
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
    (NumberField.not_dvd_discr_iff_forall_liesOver F (𝓞 F) hpZ).mp hnotdvd P hmax hlies
  exact Ideal.ramificationIdx_eq_one P ℤ


/-- A form of `IntermediateField.LinearDisjoint.of_inf_eq_bot` whose `IsGalois` instance is an
explicit argument (the type-class search does not reliably find it at the application site). -/
private theorem ld_of_inf_eq_bot {F E : Type} [Field F] [Field E] [Algebra F E]
    {A B : IntermediateField F E} [IsGalois F ↥A] [FiniteDimensional F ↥A]
    [FiniteDimensional F ↥B] (h : A ⊓ B = ⊥) : A.LinearDisjoint ↥B :=
  IntermediateField.LinearDisjoint.of_inf_eq_bot h

/-- **The auxiliary Galois tower, with the cyclotomic structure of the auxiliary level recorded.**

This refines `NK.CFTLib.RouteB.exists_auxiliary_galois_tower`
(`Submission/Work/CFTLib/RouteB/exists_auxiliary_galois_tower.lean`, proved on disk; a copy with
the import `Submission.NK.CFTLib.fundamentalClassElement` replaced by
`Submission.NK.CFTLib.fundamentalClassInputs` is
`Submission/Work/CFTLib/GFC/exists_auxiliary_galois_tower.lean`): besides the tower
`L₀, M ⊆ E` with `L₀ ≅_K L`, `M/K` cyclic of degree `n = [L:K]`, `L₀ ⊓ M = ⊥`, `L₀ ⊔ M = ⊤`, it
records that the auxiliary extension `E/L₀` is a **subextension of a cyclotomic extension of
`L₀`**: there are a field `Ω`, an `↥L₀`-algebra structure on `Ω`, a prime `q` with
`IsCyclotomicExtension {q} ↥L₀ Ω`, and an injective `↥L₀`-algebra map `φ : E →ₐ[↥L₀] Ω`.

(The embedding must be `↥L₀`-linear, as opposed to only `K`-linear, so that `E` is exhibited as an
`↥L₀`-subfield of the cyclotomic field `Ω`.)

The point of the refinement: with it, the cyclotomic case of the Artin reciprocity law
(`NK.CFTLib.artinKillsPrincipal_of_le_isCyclotomicExtension`, base case
`NK.CFTLib.ARL.artinReciprocity_cyclotomic`, both proved) applies to the auxiliary extension
`E/L₀` **unconditionally** — the general reciprocity law is not needed for the Route B comparison
`C_K ⊆ N_{E/L₀}C_E`.  Such an `Ω` is exactly what the existing proof produces internally: there,
`E = L₀ ⊔ MΩ` and `MΩ ⊆ Kζ ⊆ L₀ζ` inside `Ω₀ = AlgebraicClosure L`, with `L₀ ⊓ (Kζ) = K`, so
`L₀ ⊔ Kζ = L₀(ζ)` is cyclotomic of conductor `q` over `L₀`; the existing proof is copied and the
extra data exported at the end (taking `Ω` to be the subfield generated over `↥L₀` by the `q`-th
roots of unity, and `φ` the inclusion). -/
theorem exists_auxiliary_galois_tower_cyclotomic (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra K E)
      (_ : FiniteDimensional K E) (_ : IsGalois K E) (L₀ M : IntermediateField K E),
      Nonempty (↥L₀ ≃ₐ[K] L) ∧ IsGalois K ↥M ∧ IsCyclic (↥M ≃ₐ[K] ↥M) ∧
      Nat.card (↥M ≃ₐ[K] ↥M) = Nat.card Gal(L/K) ∧
      L₀ ⊓ M = ⊥ ∧ L₀ ⊔ M = ⊤ ∧
      ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra K Ω) (_ : Algebra ↥L₀ Ω)
        (_ : IsScalarTower K ↥L₀ Ω) (_ : FiniteDimensional ↥L₀ Ω)
        (q : ℕ) (_ : Nat.Prime q),
        IsCyclotomicExtension {q} ↥L₀ Ω ∧ ∃ (φ : E →ₐ[↥L₀] Ω), Function.Injective φ := by
  classical
  -- ## Step 1: the auxiliary prime
  set n : ℕ := Nat.card Gal(L/K) with hn
  have hnfr : n = Module.finrank K L := by rw [hn]; exact IsGalois.card_aut_eq_finrank K L
  have hnpos : 0 < n := hnfr ▸ Module.finrank_pos
  obtain ⟨q, hqprime, hndvd, hqK, hqL⟩ := aux_prime K L n hnpos
  haveI : NeZero q := ⟨hqprime.ne_zero⟩
  -- ## Step 2: the ambient field, a primitive root of unity, the subfields
  let Ωb := AlgebraicClosure L
  haveI hQKΩb : IsScalarTower ℚ K Ωb := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    simp [map_ratCast]
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ωb q
  set Qζ : IntermediateField ℚ Ωb := IntermediateField.adjoin ℚ ({ζ} : Set Ωb) with hQζ
  set Lq : IntermediateField ℚ Ωb := (⊥ : IntermediateField L Ωb).restrictScalars ℚ with hLq
  set Kq : IntermediateField ℚ Ωb := (⊥ : IntermediateField K Ωb).restrictScalars ℚ with hKq
  set L₀ : IntermediateField K Ωb := (⊥ : IntermediateField L Ωb).restrictScalars K with hL0
  set Kζ : IntermediateField K Ωb := IntermediateField.adjoin K ({ζ} : Set Ωb) with hKζ
  -- ## Step 3: `ℚ(ζ)` meets the images of `K` and `L` trivially
  have hdisjL : Qζ ⊓ Lq = ⊥ :=
    NK.CFTLib.RouteB.intersect_cyclotomic_eq_bot (F := L) q hqprime
      (unramified_of_not_dvd_discr (F := L) hqprime hqL) ζ hζ
  have hdisjK : Qζ ⊓ Kq = ⊥ :=
    NK.CFTLib.RouteB.intersect_cyclotomic_eq_bot (F := K) q hqprime
      (unramified_of_not_dvd_discr (F := K) hqprime hqK) ζ hζ
  -- ## Step 4: finranks and the Galois/cyclotomic structure of `ℚ(ζ)`
  haveI hQζcyc : IsCyclotomicExtension {q} ℚ ↥Qζ := by
    rw [hQζ]
    exact (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin q ℚ Ωb _ hζ).mpr rfl
  haveI hQζgal : IsGalois ℚ ↥Qζ := IsCyclotomicExtension.isGalois {q} ℚ ↥Qζ
  haveI hQζfd : FiniteDimensional ℚ ↥Qζ := by
    rw [hQζ]
    exact IntermediateField.finiteDimensional_adjoin (S := ({ζ} : Set Ωb)) (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      exact hx ▸ (hζ.isIntegral hqprime.pos).tower_top)
  have hfrQζ : Module.finrank ℚ ↥Qζ = q - 1 := by
    rw [IsCyclotomicExtension.finrank ↥Qζ (Polynomial.cyclotomic.irreducible_rat hqprime.pos),
      Nat.totient_prime hqprime]
  haveI hLqfd : FiniteDimensional ℚ ↥Lq := by
    rw [hLq]; exact FiniteDimensional.trans ℚ L ↥(⊥ : IntermediateField L Ωb)
  haveI hKqfd : FiniteDimensional ℚ ↥Kq := by
    rw [hKq]; exact FiniteDimensional.trans ℚ K ↥(⊥ : IntermediateField K Ωb)
  have hfrLq : Module.finrank ℚ ↥Lq = n * Module.finrank ℚ K := by
    have hbot : Module.finrank ℚ ↥Lq = Module.finrank ℚ L := by
      have h : Module.finrank ℚ ↥(⊥ : IntermediateField L Ωb) = Module.finrank ℚ L := by
        rw [← Module.finrank_mul_finrank ℚ L ↥(⊥ : IntermediateField L Ωb),
          (IntermediateField.botEquiv L Ωb).toLinearEquiv.finrank_eq, Module.finrank_self, mul_one]
      exact h
    rw [hbot, ← Module.finrank_mul_finrank ℚ K L, ← hnfr, mul_comm]
  have hfrKq : Module.finrank ℚ ↥Kq = Module.finrank ℚ K := by
    have h : Module.finrank ℚ ↥(⊥ : IntermediateField K Ωb) = Module.finrank ℚ K := by
      rw [← Module.finrank_mul_finrank ℚ K ↥(⊥ : IntermediateField K Ωb),
        (IntermediateField.botEquiv K Ωb).toLinearEquiv.finrank_eq, Module.finrank_self, mul_one]
    exact h
  -- ## Step 5: `K(ζ)` is the compositum of `K` and `ℚ(ζ)`
  have hζQ : ζ ∈ (Qζ : Set Ωb) := by
    rw [hQζ]; exact IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton ζ)
  have hζK : ζ ∈ (Kζ : Set Ωb) := by
    rw [hKζ]; exact IntermediateField.subset_adjoin K _ (Set.mem_singleton ζ)
  have hKK : (Kq : Set Ωb) ⊆ (Kζ : Set Ωb) := by
    intro y hy
    obtain ⟨c, rfl⟩ := (IntermediateField.mem_bot).mp
      ((IntermediateField.mem_restrictScalars ℚ).mp (hKq ▸ hy))
    rw [hKζ]
    exact (IntermediateField.adjoin K ({ζ} : Set Ωb)).algebraMap_mem c
  have hQK : (Qζ : Set Ωb) ⊆ (Kζ : Set Ωb) := by
    rw [hQζ, hKζ, IntermediateField.adjoin_subset_adjoin_iff]
    exact ⟨fun r hr => by
      obtain ⟨t, rfl⟩ := hr
      rw [IsScalarTower.algebraMap_apply ℚ K Ωb]
      exact (IntermediateField.adjoin K ({ζ} : Set Ωb)).algebraMap_mem t,
      fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        exact hy.symm ▸ hζK⟩
  have hKζq : Kζ.restrictScalars ℚ = Kq ⊔ Qζ := by
    have hsup : (Kq ⊔ Qζ : IntermediateField ℚ Ωb) =
        IntermediateField.adjoin ℚ ((Kq : Set Ωb) ∪ (Qζ : Set Ωb)) := by
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
        rw [IsScalarTower.algebraMap_apply ℚ K Ωb]
        exact (IntermediateField.adjoin K ({ζ} : Set Ωb)).algebraMap_mem t,
        fun y hy => by
          rcases hy with hy | hy
          · exact hKK hy
          · exact hQK hy⟩
  have hL0q : L₀.restrictScalars ℚ = Lq := by
    rw [hL0, hLq]
    apply SetLike.ext
    intro x
    rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_restrictScalars,
      IntermediateField.mem_restrictScalars]
  have hKq_le_Lq : Kq ≤ Lq := by
    intro x hx
    have hxK : x ∈ (⊥ : IntermediateField K Ωb) :=
      (IntermediateField.mem_restrictScalars ℚ).mp (hKq ▸ hx)
    obtain ⟨y, rfl⟩ := (IntermediateField.mem_bot).mp hxK
    rw [hLq]
    exact (IntermediateField.mem_restrictScalars ℚ).mpr
      ((IntermediateField.mem_bot).mpr ⟨algebraMap K L y, by
        rw [IsScalarTower.algebraMap_apply K L Ωb]⟩)
  -- ## Step 6: `[K(ζ) : K] = q - 1`
  haveI hKζfd : FiniteDimensional K ↥Kζ := by
    rw [hKζ]
    exact IntermediateField.finiteDimensional_adjoin (S := ({ζ} : Set Ωb)) (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      exact hx ▸ (hζ.isIntegral hqprime.pos).tower_top)
  haveI hL0fd : FiniteDimensional K ↥L₀ := by
    rw [hL0]
    exact FiniteDimensional.trans K L ↥(⊥ : IntermediateField L Ωb)
  have hfrKζ : Module.finrank K ↥Kζ = q - 1 := by
    have h1 : Module.finrank ℚ K * Module.finrank K ↥Kζ = Module.finrank ℚ ↥Kζ :=
      Module.finrank_mul_finrank ℚ K ↥Kζ
    have h2 : Module.finrank ℚ ↥Kζ = Module.finrank ℚ K * (q - 1) := by
      have heq : Module.finrank ℚ ↥Kζ = Module.finrank ℚ ↥(Kq ⊔ Qζ) := by
        rw [show Module.finrank ℚ ↥Kζ = Module.finrank ℚ ↥(Kζ.restrictScalars ℚ) from rfl,
          hKζq]
      rw [heq, sup_comm]
      have hLDK : Qζ.LinearDisjoint ↥Kq :=
        @ld_of_inf_eq_bot ℚ Ωb _ _ _ Qζ Kq hQζgal _ _ hdisjK
      rw [IntermediateField.LinearDisjoint.finrank_sup hLDK, hfrQζ, hfrKq]
      ring
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h1
  -- ## Step 7: `L₀ ⊓ K(ζ) = ⊥`
  have hfrL0 : Module.finrank K ↥L₀ = n := by
    have h1 : Module.finrank K ↥L₀ = Module.finrank K L := by
      have h3 := Module.finrank_mul_finrank K L ↥(⊥ : IntermediateField L Ωb)
      have h2 : Module.finrank L ↥(⊥ : IntermediateField L Ωb) = 1 := by
        rw [(IntermediateField.botEquiv L Ωb).toLinearEquiv.finrank_eq, Module.finrank_self]
      rw [h2, mul_one] at h3
      exact h3.symm
    rw [h1, ← hnfr]
  have hfrSupK : Module.finrank K ↥(L₀ ⊔ Kζ) = n * (q - 1) := by
    have h1 : Module.finrank ℚ K * Module.finrank K ↥(L₀ ⊔ Kζ) =
        Module.finrank ℚ ↥(L₀ ⊔ Kζ) :=
      Module.finrank_mul_finrank ℚ K ↥(L₀ ⊔ Kζ)
    have h2 : Module.finrank ℚ ↥(L₀ ⊔ Kζ) = Module.finrank ℚ K * (n * (q - 1)) := by
      have heq : Module.finrank ℚ ↥(L₀ ⊔ Kζ) = Module.finrank ℚ ↥(Lq ⊔ Qζ) := by
        rw [show Module.finrank ℚ ↥(L₀ ⊔ Kζ) =
            Module.finrank ℚ ↥((L₀ ⊔ Kζ).restrictScalars ℚ) from rfl,
          ← IntermediateField.restrictScalars_sup ℚ L₀ Kζ, hL0q, hKζq,
          ← sup_assoc, sup_eq_left.mpr hKq_le_Lq]
      rw [heq, sup_comm]
      have hLD_L : Qζ.LinearDisjoint ↥Lq :=
        @ld_of_inf_eq_bot ℚ Ωb _ _ _ Qζ Lq hQζgal _ _ hdisjL
      rw [IntermediateField.LinearDisjoint.finrank_sup hLD_L, hfrQζ, hfrLq]
      ring
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h1
  have hLD_eq : Module.finrank K ↥(L₀ ⊔ Kζ) = Module.finrank K ↥L₀ * Module.finrank K ↥Kζ := by
    rw [hfrSupK, hfrL0, hfrKζ]
  have hinf : L₀ ⊓ Kζ = ⊥ :=
    IntermediateField.LinearDisjoint.inf_eq_bot (IntermediateField.LinearDisjoint.of_finrank_sup hLD_eq)

  -- ## Step 8: the cyclic subfield `M` of `K(ζ)`
  haveI hKζcyc : IsCyclotomicExtension {q} K ↥Kζ :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin q K Ωb Kζ hζ).mpr rfl
  haveI hKζgal : IsGalois K ↥Kζ := IsCyclotomicExtension.isGalois {q} K ↥Kζ
  have hcard : n ∣ Nat.card Gal(↥Kζ/K) := by
    rw [IsGalois.card_aut_eq_finrank K ↥Kζ, hfrKζ]
    exact hndvd
  obtain ⟨M, hMgal, hMcyc, hMcard⟩ :=
    NK.CFTLib.RouteB.exists_cyclic_subfield_of_isCyclotomic (K := K) (L := ↥Kζ) hqprime hKζcyc hcard
  let MΩb : IntermediateField K Ωb := IntermediateField.lift M
  haveI hMΩbgal : IsGalois K ↥MΩb :=
    IsGalois.of_algEquiv (IntermediateField.liftAlgEquiv M)
  haveI : Finite (↥M ≃ₐ[K] ↥M) :=
    Nat.finite_of_card_ne_zero (by rw [hMcard]; exact hnpos.ne')
  haveI hMfd : FiniteDimensional K ↥M := IsGalois.finiteDimensional_of_finite K ↥M
  haveI hMΩbfd : FiniteDimensional K ↥MΩb :=
    LinearEquiv.finiteDimensional (IntermediateField.liftAlgEquiv M).toLinearEquiv
  have hMΩbcyc : IsCyclic (↥MΩb ≃ₐ[K] ↥MΩb) :=
    (MulEquiv.isCyclic (AlgEquiv.autCongr (IntermediateField.liftAlgEquiv M))).mp hMcyc
  have hMΩbcard : Nat.card (↥MΩb ≃ₐ[K] ↥MΩb) = n := by
    rw [← Nat.card_congr (AlgEquiv.autCongr (IntermediateField.liftAlgEquiv M)).toEquiv]
    exact hMcard
  have hMle : MΩb ≤ Kζ := IntermediateField.lift_le M
  have hinf2 : L₀ ⊓ MΩb = ⊥ := by
    have h : L₀ ⊓ MΩb ≤ L₀ ⊓ Kζ := inf_le_inf_left L₀ hMle
    rw [hinf] at h
    exact le_bot_iff.mp h
  -- `L₀` is Galois over `K` (it is the image of `L`)
  have hL0range : (IsScalarTower.toAlgHom K L Ωb).fieldRange = L₀ := by
    rw [hL0]
    apply SetLike.ext
    intro x
    rw [AlgHom.mem_fieldRange]
    constructor
    · rintro ⟨y, rfl⟩
      exact (IntermediateField.mem_restrictScalars K).mpr
        ((IntermediateField.mem_bot).mpr ⟨y, rfl⟩)
    · intro hx
      obtain ⟨y, hy⟩ := (IntermediateField.mem_bot).mp
        ((IntermediateField.mem_restrictScalars K).mp hx)
      exact ⟨y, hy⟩
  haveI hL0gal : IsGalois K ↥L₀ := by
    rw [← hL0range]
    exact IsGalois.of_algEquiv (AlgEquiv.ofInjective (IsScalarTower.toAlgHom K L Ωb)
      (FaithfulSMul.algebraMap_injective L Ωb))
  -- ## Step 9: the final assembly
  haveI : FiniteDimensional K ↥(L₀ ⊔ MΩb) := IntermediateField.finiteDimensional_sup L₀ MΩb
  haveI : NumberField ↥(L₀ ⊔ MΩb) :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (L₀ ⊔ MΩb)
  haveI : IsGalois K ↥(L₀ ⊔ MΩb) := by
    rw [isGalois_iff]
    exact ⟨inferInstance, inferInstance⟩
  let L0' : IntermediateField K ↥(L₀ ⊔ MΩb) := L₀.restrict (le_sup_left : L₀ ≤ L₀ ⊔ MΩb)
  let M' : IntermediateField K ↥(L₀ ⊔ MΩb) := MΩb.restrict (le_sup_right : MΩb ≤ L₀ ⊔ MΩb)

  -- ## Step 10: the cyclotomic structure of the auxiliary level
  --
  -- We regard `Ωb` as an `↥L0'`-algebra through the composite inclusion
  -- `↥L0' ↪ ↥(L₀ ⊔ MΩb) ↪ Ωb`, and let `Ω` be the subfield of `Ωb` generated over `↥L0'` by the
  -- `q`-th roots of unity.  Then `E = ↥(L₀ ⊔ MΩb) ⊆ Ω` is exhibited as a subextension of the
  -- cyclotomic extension `Ω/↥L0'` of conductor `q`.
  letI instL0Ωb : Algebra ↥L0' Ωb := (restrictToAmbient (L₀ ⊔ MΩb) L0').toAlgebra
  haveI towerL0Ωb : IsScalarTower K ↥L0' Ωb := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    show restrictToAmbient (L₀ ⊔ MΩb) L0' (algebraMap K ↥L0' x) = algebraMap K Ωb x
    rfl
  let Ω : IntermediateField ↥L0' Ωb :=
    IntermediateField.adjoin ↥L0' {b : Ωb | ∃ n ∈ ({q} : Set ℕ), n ≠ 0 ∧ b ^ n = 1}
  -- the `↥L0'`-algebra structure of `↥Ω`, given explicitly (its search tries
  -- `IsScalarTower ↥L0' ↥L0' _` paths first; ~60 CPU-s per use)
  letI algL0Ω : Algebra ↥L0' ↥Ω := Ω.toSubalgebra.algebra
  haveI hCycΩ : IsCyclotomicExtension {q} ↥L0' Ω :=
    IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot ({q} : Set ℕ)
      ↥L0' Ωb (fun n hn _ => by
        rw [Set.mem_singleton_iff] at hn
        exact ⟨ζ, by rwa [hn]⟩)
  haveI hfdΩ : FiniteDimensional ↥L0' Ω :=
    IsCyclotomicExtension.finiteDimensional ({q} : Set ℕ) ↥L0' Ω
  letI instKΩ : Algebra K Ω := Algebra.compHom Ω (algebraMap K ↥L0')
  haveI towerKΩ : IsScalarTower K ↥L0' Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- the algebra maps `↥L0' → Ωb` and `↥L0' → ↥Ω` agree on underlying elements
  have hcoord (x : ↥L0') : algebraMap ↥L0' Ωb x = (↑↑x : Ωb) := rfl
  have key (c : ↥L0') :
      (↑(algebraMap ↥L0' ↥(L₀ ⊔ MΩb) c) : Ωb) = ↑(algebraMap ↥L0' ↥Ω c) := by
    rw [show (↑(algebraMap ↥L0' ↥Ω c) : Ωb) = (↑↑c : Ωb) from rfl]
    rfl
  -- `↑L₀ ⊆ ↑Ω`
  have hL₀Ω : L₀ ≤ restrictScalarsExplicit towerL0Ωb Ω := by
    intro y hy
    have hy' : y ∈ Set.range (algebraMap ↥L0' Ωb) :=
      ⟨⟨⟨y, (SetLike.coe_subset_coe.mpr le_sup_left) hy⟩,
        (IntermediateField.mem_restrict (le_sup_left : L₀ ≤ L₀ ⊔ MΩb)
          ⟨y, (SetLike.coe_subset_coe.mpr le_sup_left) hy⟩).mpr hy⟩,
       by rw [hcoord]⟩
    obtain ⟨x, rfl⟩ := hy'
    exact Ω.algebraMap_mem x
  -- `ζ ∈ ↑Ω`, hence `K(ζ) ⊆ ↑Ω`
  have hζΩ : ζ ∈ (Ω : Set Ωb) :=
    IntermediateField.subset_adjoin ↥L0' _
      ⟨q, by simp, hqprime.ne_zero, hζ.pow_eq_one⟩
  have hKζΩ : Kζ ≤ restrictScalarsExplicit towerL0Ωb Ω := by
    rw [hKζ]
    exact IntermediateField.adjoin_le_iff.mpr (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      rwa [hx])
  have hEΩ : L₀ ⊔ MΩb ≤ restrictScalarsExplicit towerL0Ωb Ω :=
    sup_le hL₀Ω (le_trans hMle hKζΩ)
  -- the embedding of `E` into the cyclotomic field `Ω`, over `↥L0'`
  have hφ : ∃ φ : ↥(L₀ ⊔ MΩb) →ₐ[↥L0'] ↥Ω, Function.Injective φ := by
    refine ⟨{
      toFun := fun x => ⟨x.1, hEΩ x.2⟩,
      map_one' := Subtype.ext rfl,
      map_mul' := fun x y => Subtype.ext rfl,
      map_zero' := Subtype.ext rfl,
      map_add' := fun x y => Subtype.ext rfl,
      commutes' := fun c => Subtype.ext (key c) }, ?_⟩
    intro x y hxy
    have h : (x : Ωb) = (y : Ωb) := congrArg (fun z : ↥Ω => (z : Ωb)) hxy
    exact Subtype.ext h

  refine ⟨↥(L₀ ⊔ MΩb), inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    L0', M', ?_, ?_, ?_, ?_, ?_, ?_,
    ↥Ω, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, q, hqprime,
    hCycΩ, hφ.choose, hφ.choose_spec⟩

  · -- `L₀ ≃ L`
    have h1 : Nonempty (↥L0' ≃ₐ[K] ↥L₀) :=
      ⟨(IntermediateField.restrictAlgEquiv (le_sup_left : L₀ ≤ L₀ ⊔ MΩb)).symm⟩
    obtain ⟨e1⟩ := h1
    exact ⟨e1.trans (hL0range ▸ (AlgEquiv.ofInjective (IsScalarTower.toAlgHom K L Ωb)
      (FaithfulSMul.algebraMap_injective L Ωb)).symm)⟩
  · -- `M / K` Galois
    exact IsGalois.of_algEquiv
      (IntermediateField.restrictAlgEquiv (le_sup_right : MΩb ≤ L₀ ⊔ MΩb))
  · -- `M / K` cyclic
    exact (MulEquiv.isCyclic (AlgEquiv.autCongr
      (IntermediateField.restrictAlgEquiv (le_sup_right : MΩb ≤ L₀ ⊔ MΩb)))).mp hMΩbcyc
  · -- the cardinality
    rw [← Nat.card_congr (AlgEquiv.autCongr
      (IntermediateField.restrictAlgEquiv (le_sup_right : MΩb ≤ L₀ ⊔ MΩb))).toEquiv, hMΩbcard,
      hn]
  · -- the intersection
    rw [← IntermediateField.lift_inj, IntermediateField.lift_inf, IntermediateField.lift_bot,
      IntermediateField.lift_restrict, IntermediateField.lift_restrict, hinf2]
  · -- the supremum
    rw [← IntermediateField.lift_inj, IntermediateField.lift_top, IntermediateField.lift_sup,
      IntermediateField.lift_restrict, IntermediateField.lift_restrict]


end NK.GFC
