/-
Work of the Neukirch–Uchida team.

# Setup for `NK.LocalKW.exists_zpow_mul_pow_eq_unram`

The lemma `NK.LocalKW.exists_zpow_mul_pow_eq_unram` states that in the maximal unramified
extension `ℚ_p^ur` of `ℚ_[p]`, every nonzero element is an `n`-th power times a power of `p`
(`n` coprime to `p`).  The mathematical content is `ℚ_p^{ur×}/(ℚ_p^{ur×})^n = ⟨p⟩`, which is
proved here by reducing to the *abstract* local field `A = ℚ_𝔭` (the `𝔭`-adic completion of `ℚ`
for `𝔭 = (p)`), for which the workspace already contains the general statement
`NK.TameStructureDeep.Tame.pow_class_unramifiedClosure_pow`.

This file fixes the comparison between the two models of `ℚ_p`:

* `ratPrime p` — the prime `(p)` of `ℤ` as a height-one prime of `𝓞 ℚ`;
* `ratPadicEquiv p` — the `ℚ`-algebra isomorphism `ℚ_[p] ≃+* (ratPrime p).adicCompletion ℚ`;
* `instAlgebraRatCompletionOmega` — the resulting `A`-algebra structure on `Ω = ℚ_p`-separably
  closed;
* `ratUniformizer p` — the element of `𝒪_A = (ratPrime p).adicCompletionIntegers ℚ` corresponding
  to `p`; its image in `Ω` is `p` itself.

The transfer lemmas `coe_adjoin_eq_of_range_algebraMap_eq`, `coe_iSup_eq_of_coe_eq` and
`mem_unramifiedClosure_iff_of_range_eq` compare the intermediate fields
`A⟮ζ⟯` and `ℚ_[p]⟮ζ⟯` (and their suprema) inside `Ω`, using only the equality of the ranges of
the two algebra maps.
-/
import Mathlib
import Submission.NK.Chebotarev.LocalKW.Defs
import Submission.NK.TameStructureDeep.Tame.Defs
import Submission.NK.LocalStructure.Defs
import Submission.NK.Mine.ResidueCharAutomatic
import Submission.NK.LocalStructure.Tame.residueCard_eq_pow_of_charP
import Submission.Commons.NumberTheory.NumberField.residueCard_adicCompletion_eq_absNorm
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_residueClass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open IsDedekindDomain

namespace NK.LocalKW

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- The prime `(p)` of `ℤ`, as a height-one prime ideal of the ring of integers of `ℚ`. -/
abbrev ratPrime : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨p, Fact.out⟩

lemma primesEquiv_ratPrime : Rat.HeightOneSpectrum.primesEquiv (ratPrime p) = ⟨p, Fact.out⟩ :=
  Equiv.apply_symm_apply _ _

/-- The canonical `ℚ`-algebra isomorphism between `ℚ_[p]` and the `(p)`-adic completion of `ℚ`. -/
noncomputable def ratPadicEquiv : ℚ_[p] ≃+* (ratPrime p).adicCompletion ℚ :=
  (Padic.adicCompletionEquiv (NumberField.RingOfIntegers ℚ) ⟨p, Fact.out⟩).toRingEquiv

/-- The `(p)`-adic completion of `ℚ`, acting on `Ω` through `ratPadicEquiv`.  This is the
`Algebra` structure for which `Ω` is a separable closure of the abstract local field `A`. -/
noncomputable instance instAlgebraRatCompletionOmega :
    Algebra ((ratPrime p).adicCompletion ℚ) (NK.Chebotarev.LocalKW.Omega p) :=
  ((algebraMap ℚ_[p] (NK.Chebotarev.LocalKW.Omega p)).comp
    (ratPadicEquiv p).symm.toRingHom).toAlgebra

lemma algebraMap_ratCompletion_apply (x : (ratPrime p).adicCompletion ℚ) :
    algebraMap ((ratPrime p).adicCompletion ℚ) (NK.Chebotarev.LocalKW.Omega p) x =
      algebraMap ℚ_[p] (NK.Chebotarev.LocalKW.Omega p) ((ratPadicEquiv p).symm x) := rfl

lemma range_algebraMap_ratCompletion :
    Set.range (algebraMap ((ratPrime p).adicCompletion ℚ) (NK.Chebotarev.LocalKW.Omega p)) =
      Set.range (algebraMap ℚ_[p] (NK.Chebotarev.LocalKW.Omega p)) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(ratPadicEquiv p).symm a, (algebraMap_ratCompletion_apply p a).symm⟩
  · rintro ⟨y, rfl⟩
    exact ⟨ratPadicEquiv p y,
      by rw [algebraMap_ratCompletion_apply, RingEquiv.symm_apply_apply]⟩

section Transfer

variable {κ κ' K' : Type*} [Field κ] [Field κ'] [Field K'] [Algebra κ K'] [Algebra κ' K']

/-- Two base fields with the same image in `K'` generate the same intermediate field on the same
set of generators. -/
theorem coe_adjoin_eq_of_range_algebraMap_eq
    (h : Set.range (algebraMap κ K') = Set.range (algebraMap κ' K')) (S : Set K') :
    ((IntermediateField.adjoin κ S : IntermediateField κ K') : Set K') =
      ((IntermediateField.adjoin κ' S : IntermediateField κ' K') : Set K') := by
  change ((IntermediateField.adjoin κ S).toSubfield : Set K') =
    ((IntermediateField.adjoin κ' S).toSubfield : Set K')
  rw [IntermediateField.adjoin_toSubfield, IntermediateField.adjoin_toSubfield, h]

/-- Suprema of two families of intermediate fields with pairwise equal carriers, over base fields
with the same image in `K'`, have equal carriers. -/
theorem coe_iSup_eq_of_coe_eq {ι : Type*}
    (hR : Set.range (algebraMap κ K') = Set.range (algebraMap κ' K'))
    (F : ι → IntermediateField κ K') (G : ι → IntermediateField κ' K')
    (h : ∀ i, (F i : Set K') = (G i : Set K')) :
    ((⨆ i, F i : IntermediateField κ K') : Set K') =
      ((⨆ i, G i : IntermediateField κ' K') : Set K') := by
  have hcoe : SetLike.coe '' Set.range F = SetLike.coe '' Set.range G := by
    ext s
    constructor
    · rintro ⟨i, hi, hci⟩
      obtain ⟨j, rfl⟩ := hi
      exact ⟨G j, ⟨j, rfl⟩, (h j).symm.trans hci⟩
    · rintro ⟨i, hi, hci⟩
      obtain ⟨j, rfl⟩ := hi
      exact ⟨F j, ⟨j, rfl⟩, (h j).trans hci⟩
  rw [show (⨆ i, F i : IntermediateField κ K') = sSup (Set.range F) from rfl,
      show (⨆ i, G i : IntermediateField κ' K') = sSup (Set.range G) from rfl,
      IntermediateField.sSup_def, IntermediateField.sSup_def, hcoe]
  change ((IntermediateField.adjoin κ (⋃₀ (SetLike.coe '' Set.range G))).toSubfield : Set K') =
    ((IntermediateField.adjoin κ' (⋃₀ (SetLike.coe '' Set.range G))).toSubfield : Set K')
  rw [IntermediateField.adjoin_toSubfield, IntermediateField.adjoin_toSubfield, hR]

/-- **Transfer of membership in the maximal unramified extension along a comparison of the base
fields**: two models of the `p`-adic field with the same image in `K'` have the same maximal
unramified extension inside `K'`. -/
theorem mem_unramifiedClosure_iff_of_range_eq
    (hR : Set.range (algebraMap κ K') = Set.range (algebraMap κ' K')) (q : ℕ) (x : K') :
    x ∈ NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') q ↔
      x ∈ NK.LocalAnabelian.unramifiedClosure (κ := κ') (K' := K') q := by
  have h1 : NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') q =
      ⨆ i : (Σ n : {n : ℕ // ¬ q ∣ n}, {ζ : K' // IsPrimitiveRoot ζ n}),
        IntermediateField.adjoin κ ({i.2.1} : Set K') := by
    rw [NK.LocalAnabelian.unramifiedClosure]; simp only [iSup_subtype', iSup_sigma']
  have h2 : NK.LocalAnabelian.unramifiedClosure (κ := κ') (K' := K') q =
      ⨆ i : (Σ n : {n : ℕ // ¬ q ∣ n}, {ζ : K' // IsPrimitiveRoot ζ n}),
        IntermediateField.adjoin κ' ({i.2.1} : Set K') := by
    rw [NK.LocalAnabelian.unramifiedClosure]; simp only [iSup_subtype', iSup_sigma']
  rw [h1, h2]
  have key := coe_iSup_eq_of_coe_eq (κ := κ) (κ' := κ') (K' := K') hR
    (fun i : (Σ n : {n : ℕ // ¬ q ∣ n}, {ζ : K' // IsPrimitiveRoot ζ n}) =>
      IntermediateField.adjoin κ ({i.2.1} : Set K'))
    (fun i : (Σ n : {n : ℕ // ¬ q ∣ n}, {ζ : K' // IsPrimitiveRoot ζ n}) =>
      IntermediateField.adjoin κ' ({i.2.1} : Set K'))
    (fun i => coe_adjoin_eq_of_range_algebraMap_eq hR _)
  exact Set.ext_iff.mp key x

end Transfer

/-- **The maximal unramified extension of `ℚ_[p]` agrees with that of the abstract completion of
`ℚ` at `(p)`**, inside the separable closure `Ω = ℚ̄_p^{sep}`. -/
lemma mem_unram_iff (x : NK.Chebotarev.LocalKW.Omega p) :
    x ∈ NK.LocalAnabelian.unramifiedClosure (κ := (ratPrime p).adicCompletion ℚ)
        (K' := NK.Chebotarev.LocalKW.Omega p) p ↔
      x ∈ NK.Chebotarev.LocalKW.unram p :=
  mem_unramifiedClosure_iff_of_range_eq (range_algebraMap_ratCompletion p) p x

/-- The element `p` of `𝒪_A`, transported to the completion of `ℚ` at `(p)`. -/
noncomputable def ratUniformizer : (ratPrime p).adicCompletionIntegers ℚ :=
  PadicInt.adicCompletionIntegersEquiv (NumberField.RingOfIntegers ℚ) ⟨p, Fact.out⟩ (p : ℤ_[p])

lemma ratUniformizer_coe :
    ((ratUniformizer p : (ratPrime p).adicCompletionIntegers ℚ) : (ratPrime p).adicCompletion ℚ)
      = ratPadicEquiv p (p : ℚ_[p]) :=
  PadicInt.coe_adicCompletionIntegersEquiv_apply (NumberField.RingOfIntegers ℚ)
    (⟨p, Fact.out⟩ : Nat.Primes) (p : ℤ_[p])

lemma ratPadicEquiv_symm_ratUniformizer :
    (ratPadicEquiv p).symm (ratUniformizer p : (ratPrime p).adicCompletion ℚ) = (p : ℚ_[p]) :=
  (ratPadicEquiv p).symm_apply_eq.mpr (ratUniformizer_coe p)

/-- The image of `ratUniformizer p` in `Ω` is the element `p` of `ℚ_[p]`. -/
lemma ratUniformizer_image :
    algebraMap ((ratPrime p).adicCompletion ℚ) (NK.Chebotarev.LocalKW.Omega p)
        (ratUniformizer p : (ratPrime p).adicCompletion ℚ)
      = algebraMap ℚ_[p] (NK.Chebotarev.LocalKW.Omega p) (p : ℚ_[p]) := by
  show algebraMap ℚ_[p] (NK.Chebotarev.LocalKW.Omega p)
      ((ratPadicEquiv p).symm (ratUniformizer p : (ratPrime p).adicCompletion ℚ))
    = algebraMap ℚ_[p] (NK.Chebotarev.LocalKW.Omega p) (p : ℚ_[p])
  rw [ratPadicEquiv_symm_ratUniformizer]

/-- **`Ω` is a separable closure of the abstract local field `A = ℚ_𝔭`**: base change of
separability along the ring isomorphism `ℚ_[p] ≃+* A`, together with the fact that `Ω` is
separably closed. -/
theorem isSepClosure_ratCompletion_omega :
    IsSepClosure ((ratPrime p).adicCompletion ℚ) (NK.Chebotarev.LocalKW.Omega p) := by
  refine ⟨inferInstance, ?_⟩
  have hcomp : RingHom.comp (algebraMap ((ratPrime p).adicCompletion ℚ)
        (NK.Chebotarev.LocalKW.Omega p)) (ratPadicEquiv p).toRingHom =
      RingHom.comp (RingEquiv.refl (NK.Chebotarev.LocalKW.Omega p) :
          (NK.Chebotarev.LocalKW.Omega p) →+* (NK.Chebotarev.LocalKW.Omega p))
        (algebraMap ℚ_[p] (NK.Chebotarev.LocalKW.Omega p)) := by
    rw [show algebraMap ((ratPrime p).adicCompletion ℚ) (NK.Chebotarev.LocalKW.Omega p) =
        ((algebraMap ℚ_[p] (NK.Chebotarev.LocalKW.Omega p)).comp
          (ratPadicEquiv p).symm.toRingHom) from rfl]
    ext x
    simp [RingHom.comp_apply, RingEquiv.symm_apply_apply]
  exact (Algebra.IsSeparable.iff_of_equiv_equiv (ratPadicEquiv p)
    (RingEquiv.refl (NK.Chebotarev.LocalKW.Omega p)) hcomp).mp inferInstance

/-- **The residue characteristic of the completion of `ℚ` at `(p)` is `p`.**  The residue field
of `𝒪_A` has `p` elements
(`Commons.NumberTheory.NumberField.residueCard_adicCompletion_eq_absNorm` together with
`Commons.NumberTheory.NumberField.Set.absNorm_eq_primesEquiv`), and it is a finite field of
characteristic `resCharAt (ratPrime p)` (`NK.Mine.charP_ringChar_residueField_adicCompletion`),
so `NK.LocalStructure.Tame.residueCard_eq_pow_of_charP` forces the two primes to agree. -/
theorem resCharAt_ratPrime : NK.TameStructureDeep.Tame.resCharAt (ratPrime p) = p := by
  have hcard : NK.LocalStructure.residueCard ℚ (ratPrime p) = p := by
    show Nat.card (IsLocalRing.ResidueField ((ratPrime p).adicCompletionIntegers ℚ)) = p
    rw [Commons.NumberTheory.NumberField.residueCard_adicCompletion_eq_absNorm (ratPrime p),
        Commons.NumberTheory.NumberField.Set.absNorm_eq_primesEquiv (ratPrime p),
        primesEquiv_ratPrime p]
  obtain ⟨f, hf, hpow⟩ := NK.LocalStructure.Tame.residueCard_eq_pow_of_charP (ratPrime p)
    (NK.Mine.prime_ringChar_residueField_adicCompletion (ratPrime p))
    (NK.Mine.charP_ringChar_residueField_adicCompletion (ratPrime p))
  have hr : (NK.TameStructureDeep.Tame.resCharAt (ratPrime p)).Prime :=
    NK.Mine.prime_ringChar_residueField_adicCompletion (ratPrime p)
  have hdvd0 : NK.TameStructureDeep.Tame.resCharAt (ratPrime p) ∣
      NK.LocalStructure.residueCard ℚ (ratPrime p) := by
    rw [hpow]
    exact dvd_pow_self _ hf.ne'
  have hdvd : NK.TameStructureDeep.Tame.resCharAt (ratPrime p) ∣ p := by
    rwa [hcard] at hdvd0
  exact (Nat.prime_dvd_prime_iff_eq hr (Fact.out : Nat.Prime p)).mp hdvd

/-- **`p` is a uniformiser of `𝒪_A = (ratPrime p).adicCompletionIntegers ℚ`**: the maximal ideal
is generated by the transport of `(p : ℤ_[p])` under the `ℤ`-algebra isomorphism
`PadicInt.adicCompletionIntegersEquiv`, transported from `PadicInt.maximalIdeal_eq_span_p`. -/
theorem isUniformizerAt_ratUniformizer :
    NK.TameStructureDeep.Tame.IsUniformizerAt (ratPrime p) (ratUniformizer p) := by
  have hspan : Ideal.span {ratUniformizer p} =
      (IsLocalRing.maximalIdeal ℤ_[p]).map
        (PadicInt.adicCompletionIntegersEquiv (NumberField.RingOfIntegers ℚ) ⟨p, Fact.out⟩) := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span]
    simp only [Set.image_singleton]
    rfl
  show IsLocalRing.maximalIdeal ((ratPrime p).adicCompletionIntegers ℚ) = Ideal.span {ratUniformizer p}
  rw [hspan]
  exact (IsLocalRing.eq_maximalIdeal (inferInstance :
    Ideal.IsMaximal ((IsLocalRing.maximalIdeal ℤ_[p]).map
      (PadicInt.adicCompletionIntegersEquiv (NumberField.RingOfIntegers ℚ) ⟨p, Fact.out⟩)))).symm

end

end NK.LocalKW
