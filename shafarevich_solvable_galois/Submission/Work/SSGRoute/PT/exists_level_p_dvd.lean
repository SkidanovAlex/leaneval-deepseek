import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.exists_galois_level_p_dvd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A Galois level of degree divisible by `p`

For a number field `k`, a finite Galois `K/k` and an algebraically closed field `Ω ⊇ K` there is a
finite Galois level `K ≤ L ≤ Ω` with `p ∣ [L : k]`.  Such a level is the *anchor* of a coherent
family of invariants on the `p`-torsion of the class formation `H²`: at a level whose degree is
divisible by `p` the `p`-torsion of `H²(Gal(L/k), C_L)` is cyclic of order `p`
(`Work.SSGRoute.pt_char_pTorsion`), and the transition maps (inflation) are injective, so the choice
of an isomorphism at one such level propagates coherently to all levels.

The construction is cyclotomic: `L = K · k(ζ_{p^N})` with `N = [k : ℚ] + 1`.  We avoid the
hypothesis `IsAlgClosure k Ω` of `Work.SSGRoute.exists_galois_level_p_dvd` (which is *not* satisfied
by a general algebraically closed `Ω ⊇ k`) by proving the two cyclotomic degree estimates for the
level `k(ζ)` directly: a primitive `n`-th root of unity is *integral* (hence algebraic) over any
base, so `k(ζ)` is a cyclotomic extension without any integrality hypothesis on `Ω`.

The main results:

* `Work.SSGRoute.PT.isAlgebraic_of_isPrimitiveRoot` — a primitive root of unity is algebraic over
  the base.
* `Work.SSGRoute.PT.adjoin_isCyclotomicExtension` — `k(ζ)` is a cyclotomic extension over `k`
  (the Mathlib lemma needs integrality of the *ambient* field, which we supply for the element).
* `Work.SSGRoute.PT.finrank_adjoin_dvd_totient` — `[k(ζ) : k] ∣ n.totient`.
* `Work.SSGRoute.PT.totient_prime_pow_le_finrank_mul_base` — `φ(p^N) ≤ [k : ℚ] · [k(ζ_{p^N}) : k]`.
* `Work.SSGRoute.PT.exists_level_p_dvd` — the anchor level.
-/

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace Work.SSGRoute.PT

open scoped IntermediateField

section Cyclotomic

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]

/-- **A primitive root of unity is algebraic over the base.**  It is a root of the monic polynomial
`X ^ n - 1`. -/
theorem isAlgebraic_of_isPrimitiveRoot {n : ℕ} [NeZero n] {ζ : Ω} (hζ : IsPrimitiveRoot ζ n) :
    IsAlgebraic k ζ := by
  refine IsIntegral.isAlgebraic ⟨Polynomial.X ^ n - Polynomial.C (1 : k),
    Polynomial.monic_X_pow_sub_C 1 (NeZero.ne n), ?_⟩
  simp [Polynomial.eval₂_X, Polynomial.eval₂_C, hζ.pow_eq_one]

/-- **`k(ζ)` is a cyclotomic extension of `k`.**  Mathlib's
`IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension` requires the ambient field to be
integral over the base; here we only need integrality of the root of unity `ζ`, which is automatic
(`isAlgebraic_of_isPrimitiveRoot`). -/
theorem adjoin_isCyclotomicExtension {n : ℕ} [NeZero n] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ n) (halg : IsAlgebraic k ζ) :
    IsCyclotomicExtension {n} k ↥(IntermediateField.adjoin k ({ζ} : Set Ω)) := by
  change IsCyclotomicExtension {n} k (IntermediateField.adjoin k ({ζ} : Set Ω)).toSubalgebra
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]
  exact hζ.adjoin_isCyclotomicExtension k

/-- **`[k(ζ) : k]` divides `n.totient`.**  `Gal(k(ζ)/k)` embeds into `(ℤ/nℤ)ˣ` via the action on
`ζ` (`IsPrimitiveRoot.autToPow_injective`), and both groups have order `[k(ζ):k]` and `n.totient`. -/
theorem finrank_adjoin_dvd_totient {n : ℕ} [NeZero n] {ζ : Ω} (hζ : IsPrimitiveRoot ζ n) :
    Module.finrank k ↥(IntermediateField.adjoin k ({ζ} : Set Ω)) ∣ n.totient := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (RingHom.injective (algebraMap k Ω))
  let E := IntermediateField.adjoin k ({ζ} : Set Ω)
  haveI hcyc : IsCyclotomicExtension {n} k ↥E :=
    adjoin_isCyclotomicExtension hζ (isAlgebraic_of_isPrimitiveRoot hζ)
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

/-- **`φ(p^N) ≤ [k : ℚ] · [k(ζ_{p^N}) : k]`.**  The lower bound comes from the compositum
`ℚ(ζ_p, ζ_{p^N}) = ℚ(ζ_{p^N}) ⊆ k(ζ_{p^N})`: `IsPrimitiveRoot.lcm_totient_le_finrank` applied to
the primitive `p`-th root `ζ^{p^{N-1}}` and to `ζ` gives `φ(p^N) ≤ [k(ζ_{p^N}) : ℚ]`, and
`Module.finrank_mul_finrank` turns this into `[k : ℚ] · [k(ζ_{p^N}) : k]`. -/
theorem totient_prime_pow_le_finrank_mul_base (p : ℕ) [Fact p.Prime] {N : ℕ} (hN : 1 ≤ N)
    {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ N)) :
    (p ^ N).totient ≤ Module.finrank ℚ k *
      Module.finrank k ↥(IntermediateField.adjoin k ({ζ} : Set Ω)) := by
  haveI hp : p.Prime := Fact.out
  haveI : CharZero Ω := charZero_of_injective_algebraMap (RingHom.injective (algebraMap k Ω))
  haveI hst : IsScalarTower ℚ k Ω :=
    IsScalarTower.of_algebraMap_eq fun x => (RingHom.map_rat_algebraMap (algebraMap k Ω) x).symm
  let E := IntermediateField.adjoin k ({ζ} : Set Ω)
  haveI hne : NeZero (p ^ N) := ⟨pow_ne_zero N hp.ne_zero⟩
  haveI hcyc : IsCyclotomicExtension {p ^ N} k ↥E :=
    adjoin_isCyclotomicExtension hζ (isAlgebraic_of_isPrimitiveRoot hζ)
  haveI hfinE : FiniteDimensional k ↥E := IsCyclotomicExtension.finiteDimensional {p ^ N} k ↥E
  haveI : CharZero ↥E := inferInstance
  haveI : FiniteDimensional ℚ ↥E := inferInstance
  -- the primitive `p`-th root of unity `ζ ^ p ^ (N - 1)` lies in `k(ζ_{p^N})`
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

end Cyclotomic

/-- **A Galois level of degree divisible by `p`.**  For a number field `k`, a finite Galois
extension `K/k` and an algebraically closed `Ω ⊇ K`, there is a finite Galois intermediate field
`K ≤ L ≤ Ω` whose degree over `k` is divisible by `p`. -/
theorem exists_level_p_dvd (p : ℕ) [Fact p.Prime] (k K Ω : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
    [IsGalois k K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω] :
    ∃ L : IntermediateField K Ω, NumberField L ∧ FiniteDimensional k L ∧ IsGalois k L ∧
      p ∣ Module.finrank k L := by
  haveI hp : p.Prime := Fact.out
  haveI : CharZero Ω := charZero_of_injective_algebraMap (RingHom.injective (algebraMap k Ω))
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
  haveI hne : NeZero (p ^ N) := ⟨pow_ne_zero N hp.ne_zero⟩
  -- a primitive `p ^ N`-th root of unity in `Ω`
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (p ^ N)
  -- the level `E = k(ζ_{p^N})` has `p`-divisible degree over `k`
  let E : IntermediateField k Ω := IntermediateField.adjoin k ({ζ} : Set Ω)
  haveI hcycE : IsCyclotomicExtension {p ^ N} k ↥E :=
    adjoin_isCyclotomicExtension hζ (isAlgebraic_of_isPrimitiveRoot hζ)
  haveI hgalE : IsGalois k ↥E := IsCyclotomicExtension.isGalois {p ^ N} k ↥E
  haveI hfinE : FiniteDimensional k ↥E := IsCyclotomicExtension.finiteDimensional {p ^ N} k ↥E
  have hdvdE : Module.finrank k ↥E ∣ (p ^ N).totient := finrank_adjoin_dvd_totient hζ
  have hleE : (p ^ N).totient ≤ n₀ * Module.finrank k ↥E :=
    totient_prime_pow_le_finrank_mul_base p hN hζ
  have hpdvdE : p ∣ Module.finrank k ↥E := dvd_of_dvd_totient_prime_pow hp hN hlt hdvdE hleE
  -- the compositum `K · k(ζ_{p^N})` inside `Ω`
  let Kf : IntermediateField k Ω := (IsScalarTower.toAlgHom k K Ω).fieldRange
  haveI hfdKf : FiniteDimensional k Kf :=
    LinearEquiv.finiteDimensional
      (AlgHom.equivFieldRange (IsScalarTower.toAlgHom k K Ω)).toLinearEquiv
  haveI hgalKf : IsGalois k Kf :=
    IsGalois.of_algEquiv (AlgHom.equivFieldRange (IsScalarTower.toAlgHom k K Ω))
  let Lk : IntermediateField k Ω := Kf ⊔ E
  haveI hfdLk : FiniteDimensional k Lk := IntermediateField.finiteDimensional_sup Kf E
  haveI hgalLk : IsGalois k Lk := inferInstance
  haveI hnfLk : NumberField ↥Lk := NumberField.of_module_finite k ↥Lk
  have hpdvdLk : p ∣ Module.finrank k ↥Lk :=
    dvd_trans hpdvdE
      (IntermediateField.finrank_dvd_of_le_right (le_sup_right : E ≤ Kf ⊔ E))
  -- the same field, carved out over `K`
  let L : IntermediateField K Ω :=
    Lk.toSubfield.toIntermediateField (fun x => by
      have hx : algebraMap K Ω x ∈ Kf := by
        have h1 : algebraMap K Ω x
            = (((IsScalarTower.toAlgHom k K Ω).equivFieldRange x : ↥Kf) : Ω) := by
          rw [AlgHom.equivFieldRange_apply_coe, IsScalarTower.toAlgHom_apply]
        rw [h1]
        exact ((IsScalarTower.toAlgHom k K Ω).equivFieldRange x).2
      exact (show Kf ≤ Lk from le_sup_left) hx)
  have hLrestrict : L.restrictScalars k = Lk := by
    ext x; exact Iff.rfl
  have eL : ↥Lk ≃ₐ[k] ↥L := (IntermediateField.equivOfEq hLrestrict).symm
  haveI hfdL : FiniteDimensional k ↥L := LinearEquiv.finiteDimensional eL.toLinearEquiv
  haveI hgalL : IsGalois k ↥L := IsGalois.of_algEquiv eL
  haveI hnfL : NumberField ↥L := NumberField.of_module_finite k ↥L
  refine ⟨L, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [← LinearEquiv.finrank_eq eL.toLinearEquiv]
  exact hpdvdLk

end Work.SSGRoute.PT
