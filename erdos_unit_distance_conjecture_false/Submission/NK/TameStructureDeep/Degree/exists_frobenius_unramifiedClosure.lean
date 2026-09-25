/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Frobenius of the maximal unramified extension `κ^ur = κ(μ_{p'})`

For a number field `K`, a finite place `𝔭`, `κ = K_𝔭` its `𝔭`-adic completion, `p` the residue
characteristic, `q = residueCard K 𝔭` the residue field cardinality and `K'` a separable closure
of `κ`, the maximal unramified extension `L = unramifiedClosure p = κ(μ_{p'}) ⊆ K'` carries a
**Frobenius element**: an automorphism `F` of `L/κ` acting on the prime-to-`p` roots of unity by

  `ζ ↦ ζ ^ q`.

This is the classical normalisation of the Frobenius of the unramified extension `κ^ur/κ`
(NSW (7.5.6)); it is the "action on the prime-to-`p` roots of unity" half of
`NK.LocalAnabelian.IsFrobeniusFor`, made unconditional for the unramified quotient.

The proof is a compactness argument in the profinite group `Gal(K'/κ)`: for each `n` prime to `p`
the set `frobSet n` of elements acting on the primitive `n`-th roots of unity by the `q`-th power
map is nonempty (this is the finite-level Frobenius,
`NK.TameStructureDeep.Degree.exists_algEquiv_adjoin_primitiveRoot_pow`, transported to `K'`
along the surjection `Gal(K'/κ) → Gal(κ⟮ζ_n⟯/κ)`) and closed (the condition depends only on the
restriction to the finite Galois field `κ⟮ζ_n⟯`), and the family is directed downwards by
divisibility (`μ_n ⊆ μ_{nm}`).  The finite intersection property in the compact group
`Gal(K'/κ)` produces a single element `F' ∈ Gal(K'/κ)` acting by `ζ ↦ ζ ^ q` on the roots of unity
of *every* order prime to `p`; restricting `F'` along the normal intermediate field `L` gives the
required `F`.
-/
import Mathlib
import Submission.NK.TameStructureDeep.Degree.exists_algEquiv_adjoin_primitiveRoot_pow
import Submission.NK.LocalAnabelian.ResidueField.isGalois_unramifiedClosure
import Submission.NK.Mine.ResidueCharAutomatic
import Submission.NK.LocalStructure.Tame.residueCard_eq_pow_of_charP

set_option synthInstance.maxHeartbeats 200000

open scoped Classical
open IntermediateField

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

namespace NK.TameStructureDeep.Degree

/-- **The `n`-th Frobenius condition** on `κ`-automorphisms of `K'`, `κ = K_𝔭` the `𝔭`-adic
completion of the number field `K`: the elements acting on the primitive `n`-th roots of unity by
the `q`-th power map, `q = residueCard K 𝔭` being the cardinality of the residue field of `κ`. -/
private def frobSet {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] (n : ℕ) :
    Set (K' ≃ₐ[𝔭.adicCompletion K] K') :=
  {σ | ∀ ζ : K', IsPrimitiveRoot ζ n → σ ζ = ζ ^ NK.LocalStructure.residueCard K 𝔭}

/-- **Uniqueness of the action on a generating root of unity.**  Two `κ`-automorphisms of `K'`
agreeing on a primitive `n`-th root of unity `ζ` agree on the whole cyclotomic field `κ⟮ζ⟯`: that
field is generated over `κ` by `ζ`. -/
private lemma eq_on_adjoin_of_eq {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] {n : ℕ} {ζ : K'} (hζ : IsPrimitiveRoot ζ n)
    {σ τ : Gal(K'/𝔭.adicCompletion K)} (h : σ ζ = τ ζ) {x : K'}
    (hx : x ∈ IntermediateField.adjoin (𝔭.adicCompletion K) ({ζ} : Set K')) : σ x = τ x :=
  IntermediateField.adjoin_induction (F := 𝔭.adicCompletion K) (s := ({ζ} : Set K'))
    (p := fun y _ => σ y = τ y)
    (fun y hy => by rw [Set.mem_singleton_iff] at hy; rw [hy]; exact h)
    (fun y => by simp)
    (fun y z _ _ ih1 ih2 => by rw [map_add, map_add, ih1, ih2])
    (fun y _ ih => by rw [map_inv₀, map_inv₀, ih])
    (fun y z _ _ ih1 ih2 => by rw [map_mul, map_mul, ih1, ih2]) hx

/-- `n ≠ 0` remains nonzero in the separable closure `K'` of the `𝔭`-adic completion: that
completion has characteristic `0`, being an extension of the number field `K`. -/
private lemma natCast_ne_zero {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] {n : ℕ} (hn : n ≠ 0) : (n : K') ≠ 0 := by
  intro h
  have h2 : ((n : ℕ) : 𝔭.adicCompletion K) = 0 := by
    apply RingHom.injective (algebraMap (𝔭.adicCompletion K) K')
    rw [map_natCast, h, map_zero]
  have h4 : ((n : ℕ) : K) = 0 := by
    apply RingHom.injective (algebraMap K (𝔭.adicCompletion K))
    rw [map_natCast, h2, map_zero]
  have h4' : ((n : ℕ) : K) = ((0 : ℕ) : K) := by simpa using h4
  exact hn (Nat.cast_injective h4')

/-- Primitive `n`-th roots of unity exist in `K'` for every `n ≠ 0`: `K'` is separably closed
and of characteristic `0`. -/
private lemma exists_isPrimitiveRoot_of_ne_zero {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {n : ℕ} (hn : n ≠ 0) : ∃ ζ : K', IsPrimitiveRoot ζ n := by
  haveI : NeZero n := ⟨hn⟩
  haveI : NeZero (n : K') := ⟨natCast_ne_zero (K' := K') 𝔭 hn⟩
  haveI : IsSepClosed K' := IsSepClosure.sep_closed (𝔭.adicCompletion K)
  exact NK.LocalAnabelian.exists_isPrimitiveRoot_of_isSepClosed

/-- **The Frobenius exists at every finite level.**  For `n` prime to the residue characteristic
`p` there is a `κ`-automorphism of `K'` acting on the primitive `n`-th roots of unity by
`ζ ↦ ζ ^ q`.

The input is the finite-level statement
`NK.TameStructureDeep.Degree.exists_algEquiv_adjoin_primitiveRoot_pow`, which produces the
Frobenius on `κ⟮ζ_n⟯`; it is extended to `K'` along the surjection `Gal(K'/κ) → Gal(κ⟮ζ_n⟯/κ)`,
and every primitive `n`-th root of unity in `K'` is a power of `ζ_n`. -/
private theorem frobSet_nonempty {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] {n : ℕ}
    (hn : ¬ ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) ∣ n) :
    (frobSet 𝔭 (K' := K') n).Nonempty := by
  classical
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero _)
  haveI : NeZero n := ⟨hn0⟩
  obtain ⟨ζ₀, hζ₀⟩ := exists_isPrimitiveRoot_of_ne_zero 𝔭 (K' := K') hn0
  let E : IntermediateField (𝔭.adicCompletion K) K' :=
    IntermediateField.adjoin (𝔭.adicCompletion K) ({ζ₀} : Set K')
  have hmem : ζ₀ ∈ E := IntermediateField.mem_adjoin_simple_self (𝔭.adicCompletion K) ζ₀
  obtain ⟨σE, hσE⟩ := exists_algEquiv_adjoin_primitiveRoot_pow (K := K) 𝔭 hn hζ₀
  haveI hgalE : IsGalois (𝔭.adicCompletion K) ↥E :=
    NK.LocalAnabelian.ResidueField.isGalois_adjoin_primitiveRoot
      (κ := 𝔭.adicCompletion K) (K' := K') hn0 hζ₀
  haveI hnormE : Normal (𝔭.adicCompletion K) ↥E := IsGalois.to_normal
  obtain ⟨σ₀, hσ₀⟩ := AlgEquiv.restrictNormalHom_surjective (F := 𝔭.adicCompletion K)
    (K₁ := ↥E) (E := K') σE
  refine ⟨σ₀, ?_⟩
  have hσ₀ζ : σ₀ ζ₀ = ζ₀ ^ NK.LocalStructure.residueCard K 𝔭 := by
    have h1 : ((AlgEquiv.restrictNormalHom (F := 𝔭.adicCompletion K) (K₁ := K') E) σ₀)
        ⟨ζ₀, hmem⟩ = (⟨ζ₀, hmem⟩ : ↥E) ^ NK.LocalStructure.residueCard K 𝔭 := by
      rw [hσ₀]; exact hσE
    have h2 := congrArg (fun x : ↥E => (x : K')) h1
    rw [AlgEquiv.restrictNormalHom_apply, SubmonoidClass.coe_pow] at h2
    exact h2
  intro ζ hζ
  obtain ⟨i, -, hi⟩ := hζ₀.eq_pow_of_pow_eq_one hζ.pow_eq_one
  calc σ₀ ζ = σ₀ (ζ₀ ^ i) := by rw [hi]
    _ = (σ₀ ζ₀) ^ i := map_pow σ₀ ζ₀ i
    _ = (ζ₀ ^ NK.LocalStructure.residueCard K 𝔭) ^ i := by rw [hσ₀ζ]
    _ = (ζ₀ ^ i) ^ NK.LocalStructure.residueCard K 𝔭 := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = ζ ^ NK.LocalStructure.residueCard K 𝔭 := by rw [hi]

/-- **The Frobenius condition is closed.**  For `n` prime to `p`, the set of `κ`-automorphisms of
`K'` acting on the primitive `n`-th roots of unity by `ζ ↦ ζ ^ q` is closed in the Krull topology:
it is the preimage of a single element under the (continuous) restriction map to the finite Galois
field `κ⟮ζ_n⟯`. -/
private theorem frobSet_closed {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] {n : ℕ}
    (hn : ¬ ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) ∣ n) :
    IsClosed (frobSet 𝔭 (K' := K') n) := by
  classical
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero _)
  haveI : NeZero n := ⟨hn0⟩
  obtain ⟨ζ₀, hζ₀⟩ := exists_isPrimitiveRoot_of_ne_zero 𝔭 (K' := K') hn0
  let E : IntermediateField (𝔭.adicCompletion K) K' :=
    IntermediateField.adjoin (𝔭.adicCompletion K) ({ζ₀} : Set K')
  have hmem : ζ₀ ∈ E := IntermediateField.mem_adjoin_simple_self (𝔭.adicCompletion K) ζ₀
  haveI hgalE : IsGalois (𝔭.adicCompletion K) ↥E :=
    NK.LocalAnabelian.ResidueField.isGalois_adjoin_primitiveRoot
      (κ := 𝔭.adicCompletion K) (K' := K') hn0 hζ₀
  haveI hnormE : Normal (𝔭.adicCompletion K) ↥E := IsGalois.to_normal
  obtain ⟨σ₀, hσ₀⟩ := frobSet_nonempty 𝔭 (K' := K') hn
  let τ : ↥E ≃ₐ[𝔭.adicCompletion K] ↥E :=
    (AlgEquiv.restrictNormalHom (F := 𝔭.adicCompletion K) (K₁ := K') E) σ₀
  have heq : frobSet 𝔭 (K' := K') n =
      (AlgEquiv.restrictNormalHom (F := 𝔭.adicCompletion K) (K₁ := K') E) ⁻¹' ({τ} :
        Set (↥E ≃ₐ[𝔭.adicCompletion K] ↥E)) := by
    ext σ
    simp only [Set.mem_preimage, Set.mem_singleton_iff, frobSet, Set.mem_ofPred_eq]
    constructor
    · intro hσ
      have h1 : ∀ x : ↥E,
          ((AlgEquiv.restrictNormalHom (F := 𝔭.adicCompletion K) (K₁ := K') E) σ) x =
            ((AlgEquiv.restrictNormalHom (F := 𝔭.adicCompletion K) (K₁ := K') E) σ₀) x := by
        intro x
        apply Subtype.ext
        rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]
        exact eq_on_adjoin_of_eq 𝔭 (K' := K') hζ₀ (by rw [hσ ζ₀ hζ₀, hσ₀ ζ₀ hζ₀]) x.2
      exact AlgEquiv.ext h1
    · intro hσ
      have hagree : ∀ y : K', y ∈ E → σ y = σ₀ y := by
        intro y hy
        have h2 : ((AlgEquiv.restrictNormalHom (F := 𝔭.adicCompletion K) (K₁ := K') E) σ)
            ⟨y, hy⟩ = ((AlgEquiv.restrictNormalHom (F := 𝔭.adicCompletion K) (K₁ := K') E) σ₀)
            ⟨y, hy⟩ := by rw [hσ]
        have h3 := congrArg (fun x : ↥E => (x : K')) h2
        rwa [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply] at h3
      intro ζ hζ
      obtain ⟨i, -, hi⟩ := hζ₀.eq_pow_of_pow_eq_one hζ.pow_eq_one
      calc σ ζ = σ (ζ₀ ^ i) := by rw [hi]
        _ = (σ ζ₀) ^ i := map_pow σ ζ₀ i
        _ = (σ₀ ζ₀) ^ i := by rw [hagree ζ₀ hmem]
        _ = σ₀ (ζ₀ ^ i) := (map_pow σ₀ ζ₀ i).symm
        _ = σ₀ ζ := by rw [hi]
        _ = ζ ^ NK.LocalStructure.residueCard K 𝔭 := hσ₀ ζ hζ
  rw [heq]
  exact IsClosed.preimage (InfiniteGalois.restrictNormalHom_continuous E) isClosed_singleton

/-- **The Frobenius condition is monotone in the level.**  If the order `n` divides `m` then
acting by `ζ ↦ ζ ^ q` on the primitive `m`-th roots of unity implies the same for the primitive
`n`-th ones: every `n`-th root of unity is a power of a primitive `m`-th one. -/
private theorem frobSet_anti {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] {n m : ℕ}
    (hm : ¬ ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) ∣ m) (hdiv : n ∣ m) :
    frobSet 𝔭 (K' := K') m ⊆ frobSet 𝔭 (K' := K') n := by
  classical
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  haveI : NeZero m := ⟨hm0⟩
  obtain ⟨ξ, hξ⟩ := exists_isPrimitiveRoot_of_ne_zero 𝔭 (K' := K') hm0
  intro σ hσ ζ hζ
  have hζm : ζ ^ m = 1 := by
    obtain ⟨t, rfl⟩ := hdiv
    rw [pow_mul, hζ.pow_eq_one, one_pow]
  obtain ⟨i, -, hi⟩ := hξ.eq_pow_of_pow_eq_one hζm
  calc σ ζ = σ (ξ ^ i) := by rw [hi]
    _ = (σ ξ) ^ i := map_pow σ ξ i
    _ = (ξ ^ NK.LocalStructure.residueCard K 𝔭) ^ i := by rw [hσ ξ hξ]
    _ = (ξ ^ i) ^ NK.LocalStructure.residueCard K 𝔭 := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = ζ ^ NK.LocalStructure.residueCard K 𝔭 := by rw [hi]

/-- **Existence of the Frobenius on the maximal unramified extension.**  For a number field `K`, a
finite place `𝔭` with `𝔭`-adic completion `κ`, residue characteristic `p` and residue field
cardinality `q = residueCard K 𝔭`, the maximal unramified extension `κ^ur = κ(μ_{p'})` inside a
separable closure `K'` of `κ` carries an automorphism `F` over `κ` acting on the roots of unity of
order prime to `p` by the `q`-th power map: the (arithmetic) Frobenius of `κ^ur/κ`. -/
theorem exists_frobenius_unramifiedClosure {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] :
    ∃ F : Gal(↥(NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))))
      / 𝔭.adicCompletion K),
      ∀ (n : ℕ), ¬ ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) ∣ n →
        ∀ ζ : ↥(NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
            (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)))),
          IsPrimitiveRoot ζ n → F ζ = ζ ^ NK.LocalStructure.residueCard K 𝔭 := by
  classical
  let κ := 𝔭.adicCompletion K
  let p := ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))
  let L : IntermediateField κ K' := NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p
  have hpprime : p.Prime := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  haveI hgalL : IsGalois κ ↥L :=
    NK.LocalAnabelian.ResidueField.isGalois_unramifiedClosure (κ := κ) (K' := K') p
  haveI hnormL : Normal κ ↥L := IsGalois.to_normal
  -- ## The directed family of closed sets of finite-level Frobenius conditions
  let I := {n : ℕ // ¬ p ∣ n}
  let t : I → Set (K' ≃ₐ[κ] K') := fun n => frobSet 𝔭 (K' := K') (↑n)
  have h1 : ¬ p ∣ 1 := by rw [Nat.dvd_one]; exact hpprime.ne_one
  haveI : Nonempty I := ⟨⟨1, h1⟩⟩
  have hdir : Directed (· ⊇ ·) t := by
    rintro ⟨n, hn⟩ ⟨m, hm⟩
    have hnm : ¬ p ∣ n * m := fun hd => (hpprime.dvd_mul.mp hd).elim hn hm
    exact ⟨⟨n * m, hnm⟩,
      frobSet_anti 𝔭 (K' := K') (n := n) (m := n * m) hnm ⟨m, rfl⟩,
      frobSet_anti 𝔭 (K' := K') (n := m) (m := n * m) hnm ⟨n, mul_comm n m⟩⟩
  have hne : ∀ i : I, (t i).Nonempty := fun i => frobSet_nonempty 𝔭 (K' := K') i.2
  have hclosed : ∀ i : I, IsClosed (t i) := fun i => frobSet_closed 𝔭 (K' := K') i.2
  have hcomp : ∀ i : I, IsCompact (t i) := fun i => (hclosed i).isCompact
  obtain ⟨F', hF'⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    t hdir hne hcomp hclosed
  refine ⟨AlgEquiv.restrictNormalHom (F := κ) (K₁ := K') L F', ?_⟩
  intro n hn ζ hζ
  have hζK : IsPrimitiveRoot (ζ : K') n := IsPrimitiveRoot.coe_submonoidClass_iff.mpr hζ
  have hmem : F' ∈ t ⟨n, hn⟩ := Set.mem_iInter.mp hF' ⟨n, hn⟩
  have h1 : F' (ζ : K') = (ζ : K') ^ NK.LocalStructure.residueCard K 𝔭 :=
    hmem (ζ : K') hζK
  apply Subtype.ext
  rw [AlgEquiv.restrictNormalHom_apply (F := κ) (K₁ := K') L F' ζ, SubmonoidClass.coe_pow]
  exact h1

end NK.TameStructureDeep.Degree
