import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.pt_char_pTorsion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

set_option linter.style.haveILetI false

open scoped IntermediateField

/-! ## Auxiliary degree computations for cyclotomic levels

We record three independent facts about the cyclotomic levels `k(ζ_{p^N})` that the main theorem
needs.

* `finrank_adjoin_primitiveRoot_dvd_totient`: `[k(ζ) : k]` divides the order of `(ℤ/nℤ)ˣ`, hence
  `n.totient`, for `ζ` a primitive `n`-th root of unity.  This is the classical statement that
  `Gal(k(ζ)/k)` embeds into the automorphism group of the group `μ_n` of `n`-th roots of unity via
  Mathlib's `IsPrimitiveRoot.autToPow` (injective on cyclotomic extensions,
  `IsPrimitiveRoot.autToPow_injective`), together with `IsGalois.card_aut_eq_finrank` and
  `ZMod.card_units_eq_totient`.

* `totient_prime_pow_le_finrank_mul_base`: `φ(p^N) ≤ [k : ℚ] · [k(ζ_{p^N}) : k]`.  The lower
  bound comes from the *compositum* `ℚ(ζ_p, ζ_{p^N}) = ℚ(ζ_{p^N}) ⊆ k(ζ_{p^N})`: Mathlib's
  `IsPrimitiveRoot.lcm_totient_le_finrank` (applied to the primitive `p`-th root `ζ^{p^{N-1}}` and
  to `ζ`) gives `φ(p^N) ≤ [k(ζ_{p^N}) : ℚ]`, and `Module.finrank_mul_finrank` turns this into
  `[k : ℚ] · [k(ζ_{p^N}) : k]`.

* `dvd_of_dvd_totient_prime_pow`: the elementary arithmetic that, given `d ∣ φ(p^N)`,
  `φ(p^N) ≤ n₀ · d` and `n₀ < p^{N-1}`, forces `p ∣ d`. -/

/-- **`[k(ζ) : k]` divides `n.totient`.**  For a number field `k` with algebraic closure `Ω` and a
primitive `n`-th root of unity `ζ ∈ Ω`, the degree over `k` of the cyclotomic level `k(ζ)` divides
`n.totient`.  Indeed `Gal(k(ζ)/k)` embeds into `(ℤ/nℤ)ˣ` by `IsPrimitiveRoot.autToPow`, and both
groups have order `[k(ζ):k]` and `n.totient` respectively. -/
theorem finrank_adjoin_primitiveRoot_dvd_totient (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] {n : ℕ} [NeZero n] (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ n) :
    Module.finrank k ↥(IntermediateField.adjoin k ({ζ} : Set Ω)) ∣ n.totient := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (RingHom.injective (algebraMap k Ω))
  haveI : Algebra.IsIntegral k Ω := Algebra.IsAlgebraic.isIntegral
  let E := IntermediateField.adjoin k ({ζ} : Set Ω)
  haveI hcyc : IsCyclotomicExtension {n} k ↥E :=
    hζ.intermediateField_adjoin_isCyclotomicExtension k
  haveI : IsGalois k ↥E := IsCyclotomicExtension.isGalois {n} k ↥E
  haveI : FiniteDimensional k ↥E := IsCyclotomicExtension.finiteDimensional {n} k ↥E
  -- transport `ζ` to the cyclotomic level `↥E` itself
  let z : ↥E := ⟨ζ, IntermediateField.mem_adjoin_simple_self k ζ⟩
  have hz : IsPrimitiveRoot z n := by
    apply IsPrimitiveRoot.of_map_of_injective
      (f := (IntermediateField.val (S := E) : ↥E →ₐ[k] Ω)) (ζ := z)
    · simpa [z, E] using hζ
    · exact Subtype.val_injective
  -- the Galois group of `k(ζ)/k` embeds into `(ℤ/nℤ)ˣ`
  have hinj : Function.Injective ⇑(IsPrimitiveRoot.autToPow k hz) := hz.autToPow_injective k
  have h1 : Nat.card ↥(MonoidHom.range (IsPrimitiveRoot.autToPow k hz)) =
      Nat.card (E ≃ₐ[k] E) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_coeSort_range hinj]
  have h2 : Nat.card ↥(MonoidHom.range (IsPrimitiveRoot.autToPow k hz)) ∣ Nat.card ((ZMod n)ˣ) :=
    (MonoidHom.range (IsPrimitiveRoot.autToPow k hz)).card_subgroup_dvd_card
  have h3 : Nat.card ((ZMod n)ˣ) = n.totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have h4 : Nat.card (E ≃ₐ[k] E) = Module.finrank k ↥E := IsGalois.card_aut_eq_finrank k ↥E
  rw [h1, h4, h3] at h2
  exact h2

/-- **`φ(p^N) ≤ [k : ℚ] · [k(ζ_{p^N}) : k]`.**  For a prime `p`, `1 ≤ N`, a number field `k` with
algebraic closure `Ω` and a primitive `p^N`-th root of unity `ζ ∈ Ω`, the Euler function of `p^N`
is at most `[k : ℚ]` times the degree of `k(ζ_{p^N})` over `k`. -/
theorem totient_prime_pow_le_finrank_mul_base (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] {N : ℕ} (hN : 1 ≤ N) (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ (p ^ N)) :
    (p ^ N).totient ≤ Module.finrank ℚ k *
      Module.finrank k ↥(IntermediateField.adjoin k ({ζ} : Set Ω)) := by
  haveI hp : p.Prime := Fact.out
  haveI : CharZero Ω := charZero_of_injective_algebraMap (RingHom.injective (algebraMap k Ω))
  haveI hst : IsScalarTower ℚ k Ω :=
    IsScalarTower.of_algebraMap_eq fun x => (RingHom.map_rat_algebraMap (algebraMap k Ω) x).symm
  haveI : Algebra.IsIntegral k Ω := Algebra.IsAlgebraic.isIntegral
  let E := IntermediateField.adjoin k ({ζ} : Set Ω)
  haveI hne : NeZero (p ^ N) := ⟨pow_ne_zero N hp.ne_zero⟩
  haveI hcyc : IsCyclotomicExtension {p ^ N} k ↥E :=
    hζ.intermediateField_adjoin_isCyclotomicExtension k
  haveI hfinE : FiniteDimensional k ↥E := IsCyclotomicExtension.finiteDimensional {p ^ N} k ↥E
  haveI : CharZero ↥E := inferInstance
  haveI : FiniteDimensional ℚ ↥E := inferInstance
  -- the primitive `p`-th root of unity `ζ ^ p ^ (N-1)` lies in `k(ζ_{p^N})`
  let z : ↥E := ⟨ζ, IntermediateField.mem_adjoin_simple_self k ζ⟩
  have hz : IsPrimitiveRoot z (p ^ N) := by
    apply IsPrimitiveRoot.of_map_of_injective
      (f := (IntermediateField.val (S := E) : ↥E →ₐ[k] Ω)) (ζ := z)
    · simpa [z, E] using hζ
    · exact Subtype.val_injective
  have hzp : IsPrimitiveRoot (z ^ p ^ (N - 1)) p := by
    have hd : p ^ (N - 1) ∣ p ^ N := pow_dvd_pow p (Nat.sub_le N 1)
    have := hz.pow_of_dvd (pow_ne_zero (N - 1) hp.ne_zero) hd
    rwa [Nat.pow_div (Nat.sub_le N 1) hp.pos, Nat.sub_sub_self hN, pow_one] at this
  -- `ℚ(ζ_p, ζ_{p^N}) = ℚ(ζ_{p^N}) ⊆ k(ζ_{p^N})` has degree at least `φ(p^N)` over `ℚ`
  have hlow : (p ^ N).totient ≤ Module.finrank ℚ ↥E := by
    have h := IsPrimitiveRoot.lcm_totient_le_finrank (K := ℚ) (L := ↥E) hzp hz
      (Polynomial.cyclotomic.irreducible_rat
        (Nat.lcm_pos (Nat.pos_of_ne_zero hp.ne_zero) (pow_pos hp.pos N)))
    rwa [Nat.lcm_eq_right (dvd_pow_self p (by omega))] at h
  -- and the degree of `k(ζ_{p^N})` over `ℚ` is `[k : ℚ] · [k(ζ_{p^N}) : k]`
  have htow : Module.finrank ℚ k * Module.finrank k ↥E = Module.finrank ℚ ↥E :=
    Module.finrank_mul_finrank ℚ k ↥E
  exact hlow.trans (le_of_eq htow.symm)

/-- **Elementary arithmetic.**  If `d ∣ φ(p^N)`, `φ(p^N) ≤ n₀ · d` and `n₀ < p^{N-1}` for a prime
`p` and `1 ≤ N`, then `p ∣ d`.  Indeed `φ(p^N) = p^{N-1}(p-1)`, so if `p ∤ d` then `d ∣ p - 1` and
`p^{N-1}(p-1) = φ(p^N) ≤ n₀ d ≤ n₀ (p-1) < p^{N-1}(p-1)`, a contradiction. -/
theorem dvd_of_dvd_totient_prime_pow {p N n₀ d : ℕ} (hp : p.Prime) (hN : 1 ≤ N)
    (hlt : n₀ < p ^ (N - 1)) (hdvd : d ∣ (p ^ N).totient)
    (hle : (p ^ N).totient ≤ n₀ * d) : p ∣ d := by
  have hp2 : 2 ≤ p := hp.two_le
  rw [Nat.totient_prime_pow hp (by omega)] at hdvd hle
  by_contra hcon
  have hcop : d.Coprime (p ^ (N - 1)) :=
    ((hp.coprime_iff_not_dvd.mpr hcon).symm).pow_right (N - 1)
  have hd1 : d ∣ p - 1 := hcop.dvd_of_dvd_mul_left hdvd
  have hle1 : d ≤ p - 1 := Nat.le_of_dvd (by omega) hd1
  have hle3 : p ^ (N - 1) * (p - 1) ≤ n₀ * (p - 1) :=
    le_trans hle (Nat.mul_le_mul_left n₀ hle1)
  have := Nat.le_of_mul_le_mul_right hle3 (by omega : 0 < p - 1)
  omega

/-- **A Galois level of degree divisible by `p`.**  For a number field `k`, an algebraic closure
`Ω` and a finite Galois intermediate field `K ⊆ Ω`, there is a finite Galois intermediate field
`L` with `K ≤ L` and `p ∣ [L:k]` (so that, by `Work.SSGRoute.pt_char_pTorsion`, the `p`-torsion of
`H²(Gal(L/k), C_L)` is `𝔽_p`).

Guidance.  Take `L = K ⊔ k(ζ_{p^N}) ⊆ Ω`: `k(ζ_{p^N})/k` is Galois and `Gal(k(ζ_{p^N})/k) ↪ (ℤ/p^N)^×`
by restriction, while `[k(ζ_{p^N}):k]` is unbounded in `N` (it is at least `φ(p^N)/[k:ℚ]`) and is
bounded by `p-1` whenever `p ∤ [k(ζ_{p^N}):k]`; so some `N` has `p ∣ [k(ζ_{p^N}):k]`.  A compositum
of Galois extensions of `k` is Galois over `k`, and
`[K ⊔ k(ζ_{p^N}) : k] = [K ⊔ k(ζ_{p^N}) : k(ζ_{p^N})] · [k(ζ_{p^N}) : k]` is then divisible by `p`.
See also `Submission/Work/SSGRoute/exists_normal_sup_rootsOfUnity.lean` for the same compositum
`L ⊔ ℚ(ζ_{p^{i+1}})` trick over `ℚ`, and `adjoin_primitiveRoot_isGalois_coprime.lean`.
Mathlib has `IsCyclotomicExtension.finrank` / `IsPrimitiveRoot.finrank`, the compositum API
(`IntermediateField.sup`) and `IsCyclotomicExtension.isGalois`; `ζ_{p^N} ∈ Ω` because `Ω` is an
algebraic closure of `k`. -/
theorem exists_galois_level_p_dvd (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] :
    ∃ L : IntermediateField k Ω, K ≤ L ∧ FiniteDimensional k L ∧ IsGalois k L ∧
      p ∣ Module.finrank k L := by
  haveI hp : p.Prime := Fact.out
  haveI : CharZero Ω := charZero_of_injective_algebraMap (RingHom.injective (algebraMap k Ω))
  haveI : Algebra.IsIntegral k Ω := Algebra.IsAlgebraic.isIntegral
  haveI : IsAlgClosed Ω := (inferInstance : IsAlgClosure k Ω).isAlgClosed
  haveI : IsSepClosed Ω := inferInstance
  -- the degree `n₀ = [k : ℚ]` is positive
  let n₀ := Module.finrank ℚ k
  have hn₀ : 0 < n₀ := Module.finrank_pos
  -- choose `N = n₀ + 1`, so that `p ^ (N - 1) > n₀`
  let N : ℕ := n₀ + 1
  have hN : 1 ≤ N := by simp [N]
  have hlt : n₀ < p ^ (N - 1) := by
    have h1 : N - 1 = n₀ := by simp [N]
    rw [h1]
    calc n₀ < 2 ^ n₀ := Nat.lt_two_pow_self
      _ ≤ p ^ n₀ := Nat.pow_le_pow_left hp.two_le n₀
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N hp.ne_zero⟩
  -- a primitive `p ^ N`-th root of unity in `Ω`
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (p ^ N)
  -- the cyclotomic level `k(ζ_{p^N})`
  let E := IntermediateField.adjoin k ({ζ} : Set Ω)
  haveI hcyc : IsCyclotomicExtension {p ^ N} k ↥E :=
    hζ.intermediateField_adjoin_isCyclotomicExtension k
  haveI : IsGalois k ↥E := IsCyclotomicExtension.isGalois {p ^ N} k ↥E
  haveI : FiniteDimensional k ↥E := IsCyclotomicExtension.finiteDimensional {p ^ N} k ↥E
  -- `p` divides the degree `[k(ζ_{p^N}) : k]`
  have hdvd : Module.finrank k ↥E ∣ (p ^ N).totient :=
    finrank_adjoin_primitiveRoot_dvd_totient k Ω ζ hζ
  have hle : (p ^ N).totient ≤ n₀ * Module.finrank k ↥E :=
    totient_prime_pow_le_finrank_mul_base p k Ω hN ζ hζ
  have hpdvd : p ∣ Module.finrank k ↥E := dvd_of_dvd_totient_prime_pow hp hN hlt hdvd hle
  -- the compositum `L = K ⊔ k(ζ_{p^N})` is finite and Galois over `k`, and contains `K`
  refine ⟨K ⊔ E, le_sup_left, inferInstance, ?_, ?_⟩
  · exact isGalois_iff.mpr
      ⟨Algebra.isSeparable_tower_bot_of_isSeparable k _ Ω, inferInstance⟩
  · exact dvd_trans hpdvd (IntermediateField.finrank_dvd_of_le_right le_sup_right)

end Work.SSGRoute
