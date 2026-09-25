import Mathlib
import Submission.NK.CFTLib.RouteB.plan
import Submission.NK.CFTLib.fundamentalClassInputs
import Submission.NK.CFTLib.RouteB.intersect_cyclotomic_eq_bot
import Submission.NK.CFTLib.RouteB.exists_cyclic_subfield_of_isCyclotomic

/-!
# The auxiliary Galois tower (Route B, lemma 1)

`NK.CFTLib.RouteB.exists_auxiliary_galois_tower`: for a finite Galois extension `L / K` of
number fields there is an overfield `E / K` containing a copy `L₀` of `L` and a **cyclic** subfield
`M / K` of the same degree with `L₀ ⊓ M = ⊥` and `L₀ ⊔ M = ⊤`.

The construction (NSW XII, proof of 12.2.1; Milne, *CFT*, VIII.4):  take a prime `q` with
`q ≡ 1 mod [L:K]` and `q ∤ disc K · disc L`, and let `ζ` be a primitive `q`-th root of unity in
`Ω = AlgebraicClosure L`.  Then `ℚ(ζ) ⊓ K = ℚ` and `ℚ(ζ) ⊓ L = ℚ` (a number field unramified at
`q` meets `ℚ(ζ_q)` in `ℚ`, since `ℚ(ζ_q)` is ramified only at `q`);  consequently
`[L·K(ζ) : K] = [L:K]·[K(ζ):K]` and `L ⊓ K(ζ) = K`.  Finally `K(ζ)/K` is cyclic of degree `q-1`,
so it has a unique subfield `M` of degree `n = [L:K]`, which is cyclic;  as `M ⊆ K(ζ)` we get
`L ⊓ M = K`.
-/

set_option maxHeartbeats 4000000

open scoped NumberField
open IntermediateField

namespace NK.CFTLib.GFC

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

/-! ## The main theorem -/

theorem exists_auxiliary_galois_tower (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra K E)
      (_ : FiniteDimensional K E) (_ : IsGalois K E) (L₀ M : IntermediateField K E),
      Nonempty (↥L₀ ≃ₐ[K] L) ∧ IsGalois K ↥M ∧ IsCyclic (↥M ≃ₐ[K] ↥M) ∧
      Nat.card (↥M ≃ₐ[K] ↥M) = Nat.card Gal(L/K) ∧
      L₀ ⊓ M = ⊥ ∧ L₀ ⊔ M = ⊤ := by
  classical
  -- ## Step 1: the auxiliary prime
  set n : ℕ := Nat.card Gal(L/K) with hn
  have hnfr : n = Module.finrank K L := by rw [hn]; exact IsGalois.card_aut_eq_finrank K L
  have hnpos : 0 < n := hnfr ▸ Module.finrank_pos
  obtain ⟨q, hqprime, hndvd, hqK, hqL⟩ := aux_prime K L n hnpos
  haveI : NeZero q := ⟨hqprime.ne_zero⟩
  -- ## Step 2: the ambient field, a primitive root of unity, the subfields
  let Ω := AlgebraicClosure L
  haveI hQKΩ : IsScalarTower ℚ K Ω := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    simp [map_ratCast]
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω q
  set Qζ : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ ({ζ} : Set Ω) with hQζ
  set Lq : IntermediateField ℚ Ω := (⊥ : IntermediateField L Ω).restrictScalars ℚ with hLq
  set Kq : IntermediateField ℚ Ω := (⊥ : IntermediateField K Ω).restrictScalars ℚ with hKq
  set L₀ : IntermediateField K Ω := (⊥ : IntermediateField L Ω).restrictScalars K with hL0
  set Kζ : IntermediateField K Ω := IntermediateField.adjoin K ({ζ} : Set Ω) with hKζ
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
    exact (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin q ℚ Ω _ hζ).mpr rfl
  haveI hQζgal : IsGalois ℚ ↥Qζ := IsCyclotomicExtension.isGalois {q} ℚ ↥Qζ
  haveI hQζfd : FiniteDimensional ℚ ↥Qζ := by
    rw [hQζ]
    exact IntermediateField.finiteDimensional_adjoin (S := ({ζ} : Set Ω)) (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      exact hx ▸ (hζ.isIntegral hqprime.pos).tower_top)
  have hfrQζ : Module.finrank ℚ ↥Qζ = q - 1 := by
    rw [IsCyclotomicExtension.finrank ↥Qζ (Polynomial.cyclotomic.irreducible_rat hqprime.pos),
      Nat.totient_prime hqprime]
  haveI hLqfd : FiniteDimensional ℚ ↥Lq := by
    rw [hLq]; exact FiniteDimensional.trans ℚ L ↥(⊥ : IntermediateField L Ω)
  haveI hKqfd : FiniteDimensional ℚ ↥Kq := by
    rw [hKq]; exact FiniteDimensional.trans ℚ K ↥(⊥ : IntermediateField K Ω)
  have hfrLq : Module.finrank ℚ ↥Lq = n * Module.finrank ℚ K := by
    have hbot : Module.finrank ℚ ↥Lq = Module.finrank ℚ L := by
      have h : Module.finrank ℚ ↥(⊥ : IntermediateField L Ω) = Module.finrank ℚ L := by
        rw [← Module.finrank_mul_finrank ℚ L ↥(⊥ : IntermediateField L Ω),
          (IntermediateField.botEquiv L Ω).toLinearEquiv.finrank_eq, Module.finrank_self, mul_one]
      exact h
    rw [hbot, ← Module.finrank_mul_finrank ℚ K L, ← hnfr, mul_comm]
  have hfrKq : Module.finrank ℚ ↥Kq = Module.finrank ℚ K := by
    have h : Module.finrank ℚ ↥(⊥ : IntermediateField K Ω) = Module.finrank ℚ K := by
      rw [← Module.finrank_mul_finrank ℚ K ↥(⊥ : IntermediateField K Ω),
        (IntermediateField.botEquiv K Ω).toLinearEquiv.finrank_eq, Module.finrank_self, mul_one]
    exact h
  -- ## Step 5: `K(ζ)` is the compositum of `K` and `ℚ(ζ)`
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
  have hL0q : L₀.restrictScalars ℚ = Lq := by
    rw [hL0, hLq]
    apply SetLike.ext
    intro x
    rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_restrictScalars,
      IntermediateField.mem_restrictScalars]
  have hKq_le_Lq : Kq ≤ Lq := by
    intro x hx
    have hxK : x ∈ (⊥ : IntermediateField K Ω) :=
      (IntermediateField.mem_restrictScalars ℚ).mp (hKq ▸ hx)
    obtain ⟨y, rfl⟩ := (IntermediateField.mem_bot).mp hxK
    rw [hLq]
    exact (IntermediateField.mem_restrictScalars ℚ).mpr
      ((IntermediateField.mem_bot).mpr ⟨algebraMap K L y, by
        rw [IsScalarTower.algebraMap_apply K L Ω]⟩)
  -- ## Step 6: `[K(ζ) : K] = q - 1`
  haveI hKζfd : FiniteDimensional K ↥Kζ := by
    rw [hKζ]
    exact IntermediateField.finiteDimensional_adjoin (S := ({ζ} : Set Ω)) (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      exact hx ▸ (hζ.isIntegral hqprime.pos).tower_top)
  haveI hL0fd : FiniteDimensional K ↥L₀ := by
    rw [hL0]
    exact FiniteDimensional.trans K L ↥(⊥ : IntermediateField L Ω)
  have hfrKζ : Module.finrank K ↥Kζ = q - 1 := by
    have h1 : Module.finrank ℚ K * Module.finrank K ↥Kζ = Module.finrank ℚ ↥Kζ :=
      Module.finrank_mul_finrank ℚ K ↥Kζ
    have h2 : Module.finrank ℚ ↥Kζ = Module.finrank ℚ K * (q - 1) := by
      have heq : Module.finrank ℚ ↥Kζ = Module.finrank ℚ ↥(Kq ⊔ Qζ) := by
        rw [show Module.finrank ℚ ↥Kζ = Module.finrank ℚ ↥(Kζ.restrictScalars ℚ) from rfl,
          hKζq]
      rw [heq, sup_comm]
      have hLDK : Qζ.LinearDisjoint ↥Kq :=
        @ld_of_inf_eq_bot ℚ Ω _ _ _ Qζ Kq hQζgal _ _ hdisjK
      rw [IntermediateField.LinearDisjoint.finrank_sup hLDK, hfrQζ, hfrKq]
      ring
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h1
  -- ## Step 7: `L₀ ⊓ K(ζ) = ⊥`
  have hfrL0 : Module.finrank K ↥L₀ = n := by
    have h1 : Module.finrank K ↥L₀ = Module.finrank K L := by
      have h3 := Module.finrank_mul_finrank K L ↥(⊥ : IntermediateField L Ω)
      have h2 : Module.finrank L ↥(⊥ : IntermediateField L Ω) = 1 := by
        rw [(IntermediateField.botEquiv L Ω).toLinearEquiv.finrank_eq, Module.finrank_self]
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
        @ld_of_inf_eq_bot ℚ Ω _ _ _ Qζ Lq hQζgal _ _ hdisjL
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
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin q K Ω Kζ hζ).mpr rfl
  haveI hKζgal : IsGalois K ↥Kζ := IsCyclotomicExtension.isGalois {q} K ↥Kζ
  have hcard : n ∣ Nat.card Gal(↥Kζ/K) := by
    rw [IsGalois.card_aut_eq_finrank K ↥Kζ, hfrKζ]
    exact hndvd
  obtain ⟨M, hMgal, hMcyc, hMcard⟩ :=
    NK.CFTLib.RouteB.exists_cyclic_subfield_of_isCyclotomic (K := K) (L := ↥Kζ) hqprime hKζcyc hcard
  let MΩ : IntermediateField K Ω := IntermediateField.lift M
  haveI hMΩgal : IsGalois K ↥MΩ :=
    IsGalois.of_algEquiv (IntermediateField.liftAlgEquiv M)
  haveI : Finite (↥M ≃ₐ[K] ↥M) :=
    Nat.finite_of_card_ne_zero (by rw [hMcard]; exact hnpos.ne')
  haveI hMfd : FiniteDimensional K ↥M := IsGalois.finiteDimensional_of_finite K ↥M
  haveI hMΩfd : FiniteDimensional K ↥MΩ :=
    LinearEquiv.finiteDimensional (IntermediateField.liftAlgEquiv M).toLinearEquiv
  have hMΩcyc : IsCyclic (↥MΩ ≃ₐ[K] ↥MΩ) :=
    (MulEquiv.isCyclic (AlgEquiv.autCongr (IntermediateField.liftAlgEquiv M))).mp hMcyc
  have hMΩcard : Nat.card (↥MΩ ≃ₐ[K] ↥MΩ) = n := by
    rw [← Nat.card_congr (AlgEquiv.autCongr (IntermediateField.liftAlgEquiv M)).toEquiv]
    exact hMcard
  have hMle : MΩ ≤ Kζ := IntermediateField.lift_le M
  have hinf2 : L₀ ⊓ MΩ = ⊥ := by
    have h : L₀ ⊓ MΩ ≤ L₀ ⊓ Kζ := inf_le_inf_left L₀ hMle
    rw [hinf] at h
    exact le_bot_iff.mp h
  -- `L₀` is Galois over `K` (it is the image of `L`)
  have hL0range : (IsScalarTower.toAlgHom K L Ω).fieldRange = L₀ := by
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
    exact IsGalois.of_algEquiv (AlgEquiv.ofInjective (IsScalarTower.toAlgHom K L Ω)
      (FaithfulSMul.algebraMap_injective L Ω))
  -- ## Step 9: the final assembly
  haveI : FiniteDimensional K ↥(L₀ ⊔ MΩ) := IntermediateField.finiteDimensional_sup L₀ MΩ
  haveI : NumberField ↥(L₀ ⊔ MΩ) :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (L₀ ⊔ MΩ)
  haveI : IsGalois K ↥(L₀ ⊔ MΩ) := by
    rw [isGalois_iff]
    exact ⟨inferInstance, inferInstance⟩
  let L0' : IntermediateField K ↥(L₀ ⊔ MΩ) := L₀.restrict (le_sup_left : L₀ ≤ L₀ ⊔ MΩ)
  let M' : IntermediateField K ↥(L₀ ⊔ MΩ) := MΩ.restrict (le_sup_right : MΩ ≤ L₀ ⊔ MΩ)
  refine ⟨↥(L₀ ⊔ MΩ), inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    L0', M', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `L₀ ≃ L`
    have h1 : Nonempty (↥L0' ≃ₐ[K] ↥L₀) :=
      ⟨(IntermediateField.restrictAlgEquiv (le_sup_left : L₀ ≤ L₀ ⊔ MΩ)).symm⟩
    obtain ⟨e1⟩ := h1
    exact ⟨e1.trans (hL0range ▸ (AlgEquiv.ofInjective (IsScalarTower.toAlgHom K L Ω)
      (FaithfulSMul.algebraMap_injective L Ω)).symm)⟩
  · -- `M / K` Galois
    exact IsGalois.of_algEquiv
      (IntermediateField.restrictAlgEquiv (le_sup_right : MΩ ≤ L₀ ⊔ MΩ))
  · -- `M / K` cyclic
    exact (MulEquiv.isCyclic (AlgEquiv.autCongr
      (IntermediateField.restrictAlgEquiv (le_sup_right : MΩ ≤ L₀ ⊔ MΩ)))).mp hMΩcyc
  · -- the cardinality
    rw [← Nat.card_congr (AlgEquiv.autCongr
      (IntermediateField.restrictAlgEquiv (le_sup_right : MΩ ≤ L₀ ⊔ MΩ))).toEquiv, hMΩcard,
      hn]
  · -- the intersection
    rw [← IntermediateField.lift_inj, IntermediateField.lift_inf, IntermediateField.lift_bot,
      IntermediateField.lift_restrict, IntermediateField.lift_restrict, hinf2]
  · -- the supremum
    rw [← IntermediateField.lift_inj, IntermediateField.lift_top, IntermediateField.lift_sup,
      IntermediateField.lift_restrict, IntermediateField.lift_restrict]

end NK.CFTLib.GFC
