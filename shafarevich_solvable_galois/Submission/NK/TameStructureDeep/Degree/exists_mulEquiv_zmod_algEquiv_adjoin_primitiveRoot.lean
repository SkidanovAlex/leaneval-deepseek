/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Gal(κ⟮ζ⟯/κ) ≅ ℤ/d` **with its action** on a primitive `(q ^ d - 1)`-th root of unity

For a number field `K`, a finite place `𝔭`, `κ = K_𝔭` the `𝔭`-adic completion, `q = residueCard K 𝔭`
the residue cardinality, `d ≠ 0`, and `ζ` a primitive `(q ^ d - 1)`-th root of unity in a separable
closure `K'` of `κ`, the extension `κ⟮ζ⟯/κ` is cyclic of order `d`, and the isomorphism
`ℤ/d ≅ Gal(κ⟮ζ⟯/κ)` can be **normalised by the action on `ζ`**:

  `T a (ζ) = ζ ^ (q ^ a)`.

This is the "cyclotomic character" form of `Gal(κ(μ_{q^d-1})/κ) ≅ ℤ/d`: the chosen generator
`σ` (acting as `ζ ↦ ζ ^ q`) is the Frobenius, and `a ↦ σ ^ a` transports `ℤ/d` to the Galois
group.  The result is the exponent-precise strengthening of
`NK.TameStructureDeep.Degree.galoisGroup_adjoin_primitiveRoot_mulEquiv`, which only produces a
non-canonical isomorphism.

The proof splits into two parts, exactly along the natural boundary:

* `exists_mulEquiv_zmod_gal_adjoin_of_frobenius` — pure group theory: given *some*
  `σ : Gal(κ⟮ζ⟯/κ)` with `σ ζ = ζ ^ q`, the cardinality `d` of the Galois group, and
  `1 < q`, the map `a ↦ σ ^ a` is a group isomorphism onto `Gal(κ⟮ζ⟯/κ)` and has the required
  action.  (Injectivity is where `ζ`'s being a primitive `(q ^ d - 1)`-th root enters: if
  `σ ^ a` acts trivially then `q ^ a ≡ 1 (mod q ^ d - 1)`, forcing `a = 0`.)
* the arithmetic inputs, all of which are already in the chapter:
  `NK.TameStructureDeep.Degree.exists_algEquiv_adjoin_primitiveRoot_pow` for the Frobenius `σ`,
  `NK.TameStructureDeep.Degree.finrank_adjoin_eq_orderOf` for the degree, and the elementary
  `orderOf_residueCard_zmod_pow_sub_one` for `ord_{q^d-1}(q) = d`.
-/
import Mathlib
import Submission.NK.TameStructureDeep.Degree.exists_algEquiv_adjoin_primitiveRoot_pow
import Submission.NK.TameStructureDeep.Degree.Equality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical NumberField
open IsDedekindDomain

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

namespace NK.TameStructureDeep.Degree

/-! ## Elementary arithmetic of the level `q ^ d - 1` -/

/-- If `q ≥ 2` and `k < d`, then `q ^ d - 1 ∣ q ^ k - 1` forces `k = 0`: the two consecutive
values `q ^ k - 1 < q ^ d - 1` are strictly increasing in `k`.  This is the elementary fact that
makes `ord_{q ^ d - 1}(q) = d`. -/
theorem pow_eq_one_of_dvd_pow_sub_one {q d k : ℕ} (hq : 1 < q) (hk : k < d)
    (h : q ^ d - 1 ∣ q ^ k - 1) : k = 0 := by
  have hlt : q ^ k - 1 < q ^ d - 1 := by
    have hlt' : q ^ k < q ^ d := Nat.pow_lt_pow_right hq hk
    have hpos : 1 ≤ q ^ k := Nat.one_le_pow k q hq.le
    omega
  have hzero : q ^ k - 1 = 0 := Nat.eq_zero_of_dvd_of_lt h hlt
  by_contra hk0
  have : 1 < q ^ k := Nat.one_lt_pow hk0 hq
  omega

/-- **`ord_{q ^ d - 1}(q) = d`** for the residue cardinality `q = residueCard K 𝔭` of a number
field at a finite prime: the order of `q` in `(ℤ / (q ^ d - 1))ˣ` is `d`.

This is the value of the degree `[κ⟮ζ_{q ^ d - 1}⟯ : κ]` (`finrank_adjoin_eq_orderOf`) and hence the
order of the Galois group `Gal(κ⟮ζ⟯/κ)` used below. -/
theorem orderOf_residueCard_zmod_pow_sub_one {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (d : ℕ)
    (hd : d ≠ 0) :
    orderOf ((NK.LocalStructure.residueCard K 𝔭 : ℕ) :
      ZMod (NK.LocalStructure.residueCard K 𝔭 ^ d - 1)) = d := by
  have hq : 1 < NK.LocalStructure.residueCard K 𝔭 := by
    have h2 : 2 ≤ NK.LocalStructure.residueCard K 𝔭 :=
      NK.LocalReciprocity.two_le_residueCard K 𝔭
    omega
  rw [orderOf_eq_iff (Nat.pos_of_ne_zero hd)]
  constructor
  · have h : 1 ≤ NK.LocalStructure.residueCard K 𝔭 ^ d :=
      Nat.one_le_pow d _ (le_of_lt hq)
    rw [← Nat.cast_pow, ← Nat.sub_add_cancel h]
    rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add]
  · intro m hm hm0 hcontra
    have hcast : ((NK.LocalStructure.residueCard K 𝔭 ^ m : ℕ) :
        ZMod (NK.LocalStructure.residueCard K 𝔭 ^ d - 1)) =
        ((1 : ℕ) : ZMod (NK.LocalStructure.residueCard K 𝔭 ^ d - 1)) := by
      rw [Nat.cast_pow, Nat.cast_one]; exact hcontra
    have hmod : NK.LocalStructure.residueCard K 𝔭 ^ m ≡ 1
        [MOD (NK.LocalStructure.residueCard K 𝔭 ^ d - 1)] :=
      (ZMod.natCast_eq_natCast_iff (NK.LocalStructure.residueCard K 𝔭 ^ m) 1
        (NK.LocalStructure.residueCard K 𝔭 ^ d - 1)).mp hcast
    have hk := pow_eq_one_of_dvd_pow_sub_one hq hm hmod.symm.dvd'
    omega

/-! ## The group-theoretic half -/

/-- **The Frobenius generates `Gal(κ⟮ζ⟯/κ)` and its action on `ζ` is the `q`-power map.**

Given a field extension `E/F`, an element `ζ ∈ E` that is a primitive `(q ^ d - 1)`-th root of
unity, a `σ ∈ Gal(F⟮ζ⟯/F)` acting on `ζ` by `ζ ↦ ζ ^ q`, and the cardinality input
`#Gal(F⟮ζ⟯/F) = d`, the map `a ↦ σ ^ a` is a group isomorphism `ℤ/d ≅ Gal(F⟮ζ⟯/F)` satisfying
`T a ζ = ζ ^ (q ^ a)`.

The hypothesis `1 < q` is what makes `q ^ k - 1` strictly increasing, and hence `σ` have order
exactly `d` in its action on `ζ`. -/
theorem exists_mulEquiv_zmod_gal_adjoin_of_frobenius {F E : Type*} [Field F] [Field E]
    [Algebra F E] {q d : ℕ} (hq : 1 < q) (hd : d ≠ 0) {ζ : E}
    (hζ : IsPrimitiveRoot ζ (q ^ d - 1))
    [FiniteDimensional F ↥(IntermediateField.adjoin F ({ζ} : Set E))]
    (hσ : ∃ σ : Gal(IntermediateField.adjoin F ({ζ} : Set E) / F),
        σ ⟨ζ, IntermediateField.mem_adjoin_simple_self F ζ⟩ =
          ⟨ζ, IntermediateField.mem_adjoin_simple_self F ζ⟩ ^ q)
    (hcard : Nat.card (Gal(IntermediateField.adjoin F ({ζ} : Set E) / F)) = d) :
    ∃ T : Multiplicative (ZMod d) ≃*
        Gal(IntermediateField.adjoin F ({ζ} : Set E) / F),
      ∀ a : Multiplicative (ZMod d),
        T a ⟨ζ, IntermediateField.mem_adjoin_simple_self F ζ⟩ =
          ⟨ζ, IntermediateField.mem_adjoin_simple_self F ζ⟩ ^
            (q ^ (Multiplicative.toAdd a).val) := by
  classical
  haveI : NeZero d := ⟨hd⟩
  have hn0 : q ^ d - 1 ≠ 0 := by
    have := Nat.one_lt_pow hd hq
    omega
  obtain ⟨σ, hσ⟩ := hσ
  let E' := IntermediateField.adjoin F ({ζ} : Set E)
  let z : ↥E' := ⟨ζ, IntermediateField.mem_adjoin_simple_self F ζ⟩
  have hσz : σ z = z ^ q := hσ
  -- The iterated action of `σ` on `z` is `z ↦ z ^ (q ^ k)`.
  have hzpow : ∀ k : ℕ, (σ ^ k) z = z ^ q ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : (σ ^ (k + 1)) z = (σ ^ k) (σ z) := rfl
      rw [h1, hσz, map_pow, ih, ← pow_mul, ← pow_succ]
  have hζz : IsPrimitiveRoot z (q ^ d - 1) :=
    (IsPrimitiveRoot.coe_submonoidClass_iff (ζ := z)).mp hζ
  -- `σ` has order dividing `d`, because `σ ^ d` fixes the generator `z`.
  have hσd : σ ^ d = 1 := by
    have hzd : (σ ^ d) z = z := by
      rw [hzpow d]
      have hqd : q ^ d = (q ^ d - 1) + 1 :=
        (Nat.sub_add_cancel (Nat.one_le_pow d q hq.le)).symm
      rw [hqd, pow_succ, hζz.pow_eq_one, one_mul]
    apply AlgEquiv.coe_toAlgHom_injective
    apply IntermediateField.adjoin_algHom_ext F (s := ({ζ} : Set E))
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    simpa using hzd
  -- The candidate group homomorphism `a ↦ σ ^ a`.
  let f : Multiplicative (ZMod d) →* Gal(↥E' / F) :=
    MonoidHom.mk' (fun a => σ ^ (Multiplicative.toAdd a).val) (by
      intro a b
      show σ ^ (Multiplicative.toAdd (a * b)).val =
        σ ^ (Multiplicative.toAdd a).val * σ ^ (Multiplicative.toAdd b).val
      rw [show Multiplicative.toAdd (a * b) =
          Multiplicative.toAdd a + Multiplicative.toAdd b from rfl,
        ZMod.val_add, ← pow_eq_pow_mod _ hσd, pow_add])
  -- The kernel of `f` is trivial.
  have hkem : ∀ a : Multiplicative (ZMod d), f a = 1 → a = 1 := by
    intro a ha
    have ha2 : σ ^ (Multiplicative.toAdd a).val = 1 := ha
    have haz : (σ ^ (Multiplicative.toAdd a).val) z = z := by rw [ha2]; rfl
    have hk : z ^ (q ^ (Multiplicative.toAdd a).val) = z := by
      rw [← hzpow]; exact haz
    have hm1 : 1 ≤ q ^ (Multiplicative.toAdd a).val := Nat.one_le_pow _ _ hq.le
    have h1 : z ^ (q ^ (Multiplicative.toAdd a).val - 1) * z = 1 * z := by
      rw [one_mul, ← pow_succ, Nat.sub_add_cancel hm1]
      exact hk
    have h2 : z ^ (q ^ (Multiplicative.toAdd a).val - 1) = 1 :=
      mul_right_cancel₀ (hζz.ne_zero hn0) h1
    have hdiv : q ^ d - 1 ∣ q ^ (Multiplicative.toAdd a).val - 1 :=
      (hζz.pow_eq_one_iff_dvd _).mp h2
    have hlt : (Multiplicative.toAdd a).val < d := ZMod.val_lt _
    have hv : (Multiplicative.toAdd a).val = 0 :=
      pow_eq_one_of_dvd_pow_sub_one hq hlt hdiv
    have : Multiplicative.toAdd a = 0 := (ZMod.val_eq_zero _).mp hv
    exact Multiplicative.toAdd.injective (by rw [this]; rfl)
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : f (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hkem (a * b⁻¹) h1)
  -- Injectivity plus the cardinality input make `f` bijective.
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    have e1 : Fintype.card (Multiplicative (ZMod d)) = d := by
      rw [Fintype.card_congr Multiplicative.toAdd, ZMod.card]
    have e2 : Fintype.card (Gal(↥E' / F)) = d := by
      rw [← Nat.card_eq_fintype_card]; exact hcard
    rw [e1, e2]
  refine ⟨MulEquiv.ofBijective f hbij, ?_⟩
  intro a
  show f a z = z ^ (q ^ (Multiplicative.toAdd a).val)
  exact hzpow _

/-! ## The theorem -/

theorem exists_mulEquiv_zmod_algEquiv_adjoin_primitiveRoot {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {d : ℕ} (hd : d ≠ 0) {ζ : K'}
    (hζ : IsPrimitiveRoot ζ (NK.LocalStructure.residueCard K 𝔭 ^ d - 1)) :
    ∃ T : Multiplicative (ZMod d) ≃*
        Gal(↥(IntermediateField.adjoin (𝔭.adicCompletion K) ({ζ} : Set K')) /
          𝔭.adicCompletion K),
      ∀ a : Multiplicative (ZMod d),
        T a ⟨ζ, IntermediateField.mem_adjoin_simple_self (𝔭.adicCompletion K) ζ⟩ =
          ⟨ζ, IntermediateField.mem_adjoin_simple_self (𝔭.adicCompletion K) ζ⟩ ^
            (NK.LocalStructure.residueCard K 𝔭 ^ (Multiplicative.toAdd a).val) := by
  classical
  have hq : 1 < NK.LocalStructure.residueCard K 𝔭 := by
    have h2 : 2 ≤ NK.LocalStructure.residueCard K 𝔭 :=
      NK.LocalReciprocity.two_le_residueCard K 𝔭
    omega
  have hn0 : NK.LocalStructure.residueCard K 𝔭 ^ d - 1 ≠ 0 := by
    have := Nat.one_lt_pow hd hq
    omega
  haveI hne : NeZero (NK.LocalStructure.residueCard K 𝔭 ^ d - 1) := ⟨hn0⟩
  -- The level order `q ^ d - 1` is prime to the residue characteristic.
  have hn : ¬ ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) ∣
      NK.LocalStructure.residueCard K 𝔭 ^ d - 1 := by
    have hp := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
    have hpc := NK.Mine.charP_ringChar_residueField_adicCompletion 𝔭
    obtain ⟨f, _hf, hqf⟩ :=
      NK.LocalStructure.Tame.residueCard_eq_pow_of_charP 𝔭 hp hpc
    rw [hqf, ← pow_mul]
    have hfd : f * d ≠ 0 := Nat.mul_ne_zero (by omega) hd
    have hpdvd : ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) ∣
        ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) ^ (f * d) :=
      dvd_pow_self _ hfd
    have hpos : 1 ≤ ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) ^ (f * d) :=
      Nat.one_le_pow _ _ hp.pos
    intro hdiv
    have h1 : ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) ∣
        ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) ^ (f * d) -
          (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) ^ (f * d) - 1) :=
      Nat.dvd_sub hpdvd hdiv
    rw [Nat.sub_sub_self hpos] at h1
    exact hp.not_dvd_one h1
  -- `κ⟮ζ⟯` is a finite Galois cyclotomic extension of `κ`.
  haveI hint : Algebra.IsIntegral (𝔭.adicCompletion K) K' := inferInstance
  haveI hfd : FiniteDimensional (𝔭.adicCompletion K)
      ↥(IntermediateField.adjoin (𝔭.adicCompletion K) ({ζ} : Set K')) :=
    IntermediateField.adjoin.finiteDimensional (hint.isIntegral ζ)
  haveI hcyc : IsCyclotomicExtension
      ({NK.LocalStructure.residueCard K 𝔭 ^ d - 1} : Set ℕ) (𝔭.adicCompletion K)
      ↥(IntermediateField.adjoin (𝔭.adicCompletion K) ({ζ} : Set K')) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension (𝔭.adicCompletion K)
  haveI hgal : IsGalois (𝔭.adicCompletion K)
      ↥(IntermediateField.adjoin (𝔭.adicCompletion K) ({ζ} : Set K')) :=
    IsCyclotomicExtension.isGalois
      ({NK.LocalStructure.residueCard K 𝔭 ^ d - 1} : Set ℕ) (𝔭.adicCompletion K)
      ↥(IntermediateField.adjoin (𝔭.adicCompletion K) ({ζ} : Set K'))
  -- The Galois group has `d` elements.
  have hcard : Nat.card (Gal(↥(IntermediateField.adjoin (𝔭.adicCompletion K)
      ({ζ} : Set K')) / 𝔭.adicCompletion K)) = d := by
    rw [IsGalois.card_aut_eq_finrank (𝔭.adicCompletion K)
        ↥(IntermediateField.adjoin (𝔭.adicCompletion K) ({ζ} : Set K')),
      finrank_adjoin_eq_orderOf 𝔭 hn0 hn hζ]
    exact orderOf_residueCard_zmod_pow_sub_one 𝔭 d hd
  -- The Frobenius acting on `ζ` by `ζ ↦ ζ ^ q`.
  exact exists_mulEquiv_zmod_gal_adjoin_of_frobenius hq hd hζ
    (exists_algEquiv_adjoin_primitiveRoot_pow 𝔭 hn hζ) hcard

end NK.TameStructureDeep.Degree
