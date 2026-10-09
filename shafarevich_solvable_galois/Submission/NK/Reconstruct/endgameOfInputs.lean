import Submission.NeukirchUchida.Endgame
import Submission.NK.Reconstruct.exists_sigma_of_levelPrimeIdentification
import Submission.NK.Reconstruct.chebotarevInput_of_artinReciprocity
import Submission.NK.ReconstructField.Targets
import Submission.NK.ReconstructField.LevelCandidate
import Submission.NK.ReconstructField.weakNeukirchUchida
import Submission.NK.Reconstruct.isWeakUchida_two_of_uchidaModuleData_and_perlis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The reconstruction of `σ`: the endgame in terms of classical inputs

This module states the σ-producing step of Neukirch–Uchida (CoNF XII §12.2) in terms of the
*classical inputs* of the several areas of the workspace, and proves it inside `NK.Reconstruct`.

The route is the one of `exists_sigma_of_levelPrimeIdentification.lean`:

1. the local correspondence **(a)** `NK.Reconstruct.LocalCorrespondence ϕ` of CoNF (12.1.9)
   (σ-free: a bijection of the place systems, Galois-equivariant, compatible with the decomposition
   groups, preserving the residue characteristic and the local degree);
2. the *base-level* prime identification **(i)**: a base-field isomorphism `τ₀ : K₁ ≃+* K₂` with
   `primeTransport τ₀ = a.primeMap` — the base-level form of Neukirch's Lemma 5.2, i.e.
   `NK.ReconstructField.WeakNeukirchUchida a`, which is the *weak* half of Neukirch–Uchida in the
   form in which the sibling area `Submission/Work/ReconstructField/` uses it;
3. the *weak Neukirch–Uchida theorem* **(W)**, in the two level-wise presentations
   `NK.ReconstructField.LevelIsoInput ϕ hϕ` and (via
   `NK.ReconstructField.levelIsoInput_of_isWeakUchida`) Uchida's theorem
   `NK.UchidaKummer.IsWeakUchida`; the concrete classical inputs discharging these are
   `NK.UchidaKummer.IsUchidaModuleData 2` and `NK.UchidaKummer.PerlisGassmannInput`
   (`NK.Reconstruct.isWeakUchida_two_of_uchidaModuleData_and_perlis`);
4. one **Čebotarev/density input (c)** `NK.Reconstruct.ChebotarevInput K₁ K₁'`, discharged from
   Artin reciprocity by `NK.Reconstruct.chebotarevInput_of_artinReciprocity`.

The Kummer input `ℓ.Prime`, `μ_ℓ ⊆ K₁` of the differentiation lemma is *eliminated* here by taking
`ℓ = 2` (every number field has characteristic `0`, hence contains the primitive second root of
unity `-1`).

**The Frobenius correspondence (b) is not an input**: it is a consequence of the level prime
identification, and it is *proved* on this route
(`NK.ReconstructField.exists_sigma_of_placeMap_and_frobenius_of_levelPrimeIdentification`).
Likewise nothing here presupposes a field isomorphism `σ : K₂' ≃+* K₁'` or the realization of the
place correspondence — the hypothesis `(d)` of
`NK.Reconstruct.exists_sigma_of_localCorrespondence_sigmaFree`, which is *equivalent* to the
conclusion (`NK.Reconstruct.exists_conjugates_iff_exists_realizesPlaceMap`), is **not** used.

Finally `NK.Reconstruct.existsUnique_neukirchUchidaOfInputs` is the *full* statement of CoNF XII
Theorem 12.2.1 (`∃! σ`, with the predicate in exactly the form of the challenge statement), obtained
by adding the *proved* uniqueness half.
-/

set_option linter.unusedVariables false

open scoped Pointwise

namespace NK.Reconstruct

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-! ## 2. The core theorem with the classical inputs -/

/-- **The σ-producing step of Neukirch–Uchida from the classical inputs.**

From the σ-free local correspondence (a), the base-level prime identification (i)
(`NK.ReconstructField.WeakNeukirchUchida a`, Neukirch's Lemma 5.2 in its base form), the
level-wise weak Neukirch–Uchida theorem (W) (`NK.ReconstructField.LevelIsoInput ϕ hϕ`) and the
Čebotarev input (c), there is a field isomorphism `σ : K₂' ≃+* K₁'` inducing `ϕ`.

No hypothesis here presupposes `σ`, the realization of the place correspondence, the Frobenius
correspondence (b), or the rigidity of the place system: the Frobenius correspondence is derived,
the Kummer input of the differentiation lemma is met by `ℓ = 2`. -/
theorem exists_sigma_of_weakNeukirchUchida_and_levelIso (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : LocalCorrespondence ϕ)
    (hbase : NK.ReconstructField.WeakNeukirchUchida a)
    (hlev : NK.ReconstructField.LevelIsoInput ϕ hϕ)
    (hc : ChebotarevInput K₁ K₁') :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨τ₀, hbase'⟩ := hbase
  exact exists_sigma_of_localCorrespondence_of_levelIso ϕ hϕ a τ₀
    (fun 𝔭 => (hbase' 𝔭).symm) hlev Nat.prime_two (isWeakUchida_two_exists_isPrimitiveRoot K₁) hc

/-- **The σ-producing step of Neukirch–Uchida, with Uchida's weak theorem as a single input.**

Same statement as `NK.Reconstruct.exists_sigma_of_weakNeukirchUchida_and_levelIso`, with the
level-wise input `LevelIsoInput` replaced by the weak Neukirch–Uchida theorem
`NK.UchidaKummer.IsWeakUchida 2` (two number fields with isomorphic absolute Galois groups are
isomorphic) — the weak half of Theorem 12.2.1, proved by a route disjoint from the reconstruction.
The statement is given for fields in `Type` because `NK.UchidaKummer.IsWeakUchida` is stated there
(`NK.ReconstructField.levelIsoInput_of_isWeakUchida`). -/
theorem exists_sigma_of_weakNeukirchUchida_and_isWeakUchida {k₁ k₂ k₁' k₂' : Type}
    [Field k₁] [Field k₂] [Field k₁'] [Field k₂'] [NumberField k₁] [NumberField k₂]
    [Algebra k₁ k₁'] [Algebra k₂ k₂'] [IsSepClosure k₁ k₁'] [IsSepClosure k₂ k₂']
    (ϕ : Gal(k₁'/k₁) ≃* Gal(k₂'/k₂)) (hϕ : IsHomeomorph ϕ) (a : LocalCorrespondence ϕ)
    (hbase : NK.ReconstructField.WeakNeukirchUchida a)
    (hW : NK.UchidaKummer.IsWeakUchida 2) (hc : ChebotarevInput k₁ k₁') :
    ∃ σ : k₂' ≃+* k₁', Submission.NeukirchUchida.Conjugates σ ϕ :=
  exists_sigma_of_weakNeukirchUchida_and_levelIso ϕ hϕ a hbase
    (NK.ReconstructField.levelIsoInput_of_isWeakUchida hW ϕ hϕ) hc

/-! ## 3. The full statement of CoNF XII Theorem 12.2.1, from the classical inputs -/

/-- **Neukirch–Uchida (CoNF XII Theorem 12.2.1), from the classical inputs.**

This is the *whole* theorem — unique existence of the inducing field isomorphism, with the predicate
written out exactly as in the challenge statement
(`(algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range`, which is
`Submission.NeukirchUchida.MapsBase`, and `ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)`, which is the
conjugacy) — conditional on

* **(a)** the local correspondence `NK.Reconstruct.LocalCorrespondence ϕ` of CoNF (12.1.9)
  (sibling area `Submission/Work/BrauerHasse/` together with `Submission/Work/LocalInputs/`),
* **(i)** the base-level prime identification `NK.ReconstructField.WeakNeukirchUchida a`
  (Neukirch's Lemma 5.2; the weak half of the theorem),
* **(W)** the weak Neukirch–Uchida theorem `NK.ReconstructField.LevelIsoInput ϕ hϕ`
  (Uchida; sibling area `Submission/Work/UchidaKummer/`),
* **(c)** the Čebotarev density input `NK.Reconstruct.ChebotarevInput K₁ K₁'`
  (sibling area `Submission/Work/Chebotarev/`).

The uniqueness half is the *proved* theorem `Submission.NeukirchUchida.unique_sigma_of_centralizer_trivial`
(CoNF (12.1.6), triviality of the centre of an absolute Galois group); it is not an input. -/
theorem existsUnique_neukirchUchidaOfInputs (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : LocalCorrespondence ϕ)
    (hbase : NK.ReconstructField.WeakNeukirchUchida a)
    (hlev : NK.ReconstructField.LevelIsoInput ϕ hϕ)
    (hc : ChebotarevInput K₁ K₁') :
    ∃! σ : K₂' ≃+* K₁',
      (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  obtain ⟨τ₀, hbase'⟩ := hbase
  obtain ⟨σ, hσ, huniq⟩ :=
    existsUnique_sigma_of_localCorrespondence_of_levelIso ϕ hϕ a τ₀
      (fun 𝔭 => (hbase' 𝔭).symm) hlev Nat.prime_two (isWeakUchida_two_exists_isPrimitiveRoot K₁) hc
  exact ⟨σ, hσ, fun y hy => huniq y hy⟩

/-- **Neukirch–Uchida from the group-theoretic form of (12.1.9).**

Discharges the local correspondence (a) of `NK.Reconstruct.existsUnique_neukirchUchidaOfInputs`
from

* `h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ` — the "if" direction of
  CoNF (12.1.9) (the deliverable of `Submission/Work/BrauerHasse/`), and
* the two arithmetic conditions on corresponding primes: preservation of the residue
  characteristic and of the local degree `[κ : ℚ_p]` (the deliverable of
  `Submission/Work/LocalInputs/`),

using the construction `Submission.NeukirchUchida.localCorrespondenceOf` of
`Submission/NeukirchUchida/Endgame.lean`. -/
theorem existsUnique_neukirchUchidaOfPreservesDecompositionGroups (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ)
    (residueChar : ∀ (A : FinitePlaceOf K₁ K₁') (ℓ : ℕ),
      CharP (NumberField.RingOfIntegers K₁ ⧸
          (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal) ℓ →
        CharP (NumberField.RingOfIntegers K₂ ⧸
          (Submission.NeukirchUchida.primeOf (Submission.NeukirchUchida.placeMap ϕ h A).1
            (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal) ℓ)
    (localDegree : ∀ A : FinitePlaceOf K₁ K₁',
      (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.inertiaDeg ℤ *
          (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.ramificationIdx ℤ =
        (Submission.NeukirchUchida.primeOf (Submission.NeukirchUchida.placeMap ϕ h A).1
          (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal.inertiaDeg ℤ *
          (Submission.NeukirchUchida.primeOf (Submission.NeukirchUchida.placeMap ϕ h A).1
            (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal.ramificationIdx ℤ)
    (τ₀ : K₁ ≃+* K₂)
    (hbase : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal K₁,
      primeTransport τ₀ 𝔭 = primeEquivOf ϕ h 𝔭)
    (hlev : NK.ReconstructField.LevelIsoInput ϕ hϕ)
    (hc : ChebotarevInput K₁ K₁') :
    ∃! σ : K₂' ≃+* K₁',
      (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) :=
  existsUnique_neukirchUchidaOfInputs ϕ hϕ
    (Submission.NeukirchUchida.localCorrespondenceOf ϕ h residueChar localDegree)
    ⟨τ₀, hbase⟩ hlev hc

/-! ## 4. Discharging Čebotarev from Artin reciprocity -/

/-- **Neukirch–Uchida from Artin reciprocity and the weak half.**

Same as `NK.Reconstruct.existsUnique_neukirchUchidaOfInputs`, with the Čebotarev input (c)
*discharged*: it is derived from the Artin reciprocity package
`NK.Chebotarev.ArtinReciprocityInput` at every finite Galois level by
`NK.Reconstruct.chebotarevInput_of_artinReciprocity` (the Dirichlet density of a Frobenius class;
sibling area `Submission/Work/Chebotarev/`, whose inputs live in `Submission/Work/GlobalCFT/`). -/
theorem existsUnique_neukirchUchidaOfArtinReciprocity (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : LocalCorrespondence ϕ)
    (hbase : NK.ReconstructField.WeakNeukirchUchida a)
    (hlev : NK.ReconstructField.LevelIsoInput ϕ hϕ)
    (hA : ∀ (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L]
      [NumberField ↥L] [IsGalois K₁ ↥L], NK.Chebotarev.ArtinReciprocityInput K₁ ↥L) :
    ∃! σ : K₂' ≃+* K₁',
      (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) :=
  existsUnique_neukirchUchidaOfInputs ϕ hϕ a hbase hlev
    (chebotarevInput_of_artinReciprocity hA)

/-! ## 5. The concrete classical inputs at `ℓ = 2` -/

/-- **Neukirch–Uchida (CoNF XII Theorem 12.2.1) from the concrete classical inputs.**

This is `NK.Reconstruct.existsUnique_neukirchUchidaOfInputs` with

* **(a)** the local correspondence constructed from the group-theoretic form
  `Submission.NeukirchUchida.PreservesDecompositionGroups ϕ` (the "if" half of CoNF (12.1.9)) and
  the two arithmetic conditions (residue characteristic and local degree);
* **(W)** the level-wise weak Neukirch–Uchida input replaced by Uchida's theorem
  `NK.UchidaKummer.IsWeakUchida 2` (in turn a consequence of
  `NK.UchidaKummer.IsUchidaModuleData 2` and `NK.UchidaKummer.PerlisGassmannInput`, see
  `NK.Reconstruct.isWeakUchida_two_of_uchidaModuleData_and_perlis`).

The Kummer input of the differentiation lemma is met by `ℓ = 2`. -/
theorem existsUnique_neukirchUchidaOfClassicalInputs {k₁ k₂ k₁' k₂' : Type}
    [Field k₁] [Field k₂] [Field k₁'] [Field k₂'] [NumberField k₁] [NumberField k₂]
    [Algebra k₁ k₁'] [Algebra k₂ k₂'] [IsSepClosure k₁ k₁'] [IsSepClosure k₂ k₂']
    (ϕ : Gal(k₁'/k₁) ≃* Gal(k₂'/k₂)) (hϕ : IsHomeomorph ϕ) (a : LocalCorrespondence ϕ)
    (hbase : NK.ReconstructField.WeakNeukirchUchida a)
    (hW : NK.UchidaKummer.IsWeakUchida 2) (hc : ChebotarevInput k₁ k₁') :
    ∃! σ : k₂' ≃+* k₁',
      (algebraMap k₂ k₂').range.map σ.toRingHom = (algebraMap k₁ k₁').range ∧
        ∀ g : Gal(k₁'/k₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) :=
  existsUnique_neukirchUchidaOfInputs ϕ hϕ a hbase
    (NK.ReconstructField.levelIsoInput_of_isWeakUchida hW ϕ hϕ) hc

/-! ## 6. The strongest form: only (a), (W) and the Čebotarev input

The base-level prime identification `WeakNeukirchUchida a` (item **(i)** above) is **not** an
independent input: by `NK.ReconstructField.exists_primeTransport_eq_primeMap`
(`Submission/Work/ReconstructField/weakNeukirchUchida.lean`) it is a *consequence* of the local
correspondence (a), the level-wise weak Neukirch–Uchida input (W) and the Kummer input of the
differentiation lemma; and the Kummer input is met by `ℓ = 2`
(`NK.Reconstruct.isWeakUchida_two_exists_isPrimitiveRoot`). The theorems below are the resulting
forms: their
hypotheses are exactly

* **(a)** `NK.Reconstruct.LocalCorrespondence ϕ` (CoNF (12.1.9)),
* **(W)** `NK.ReconstructField.LevelIsoInput ϕ hϕ` (Uchida's weak theorem at levels), and
* **(c)** `NK.Reconstruct.ChebotarevInput K₁ K₁'` (Čebotarev density),

with the Frobenius correspondence **(b)** and the base-level identification **(i)** *proved*. -/

/-- **The σ-producing step of Neukirch–Uchida from (a), (W) and Čebotarev.**

The Frobenius correspondence (b) and the base-level prime identification (i) are both derived;

 the Kummer input of the differentiation lemma is met by `ℓ = 2`, since a number field has
characteristic `0`, hence contains `-1`, a primitive second root of unity. -/
theorem exists_sigma_of_localCorrespondence_of_levelIsoInput
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) (a : LocalCorrespondence ϕ)
    (hlev : NK.ReconstructField.LevelIsoInput ϕ hϕ) (hc : ChebotarevInput K₁ K₁') :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨σ, hσ, hfrob⟩ :=
    NK.ReconstructField.exists_sigma_of_placeMap_and_frobenius_of_levelIsoInput ϕ hϕ a hlev
      Nat.prime_two (isWeakUchida_two_exists_isPrimitiveRoot K₁)
  exact exists_sigma_of_frobeniusCorrespondence ϕ σ hσ hfrob hc

/-- **Neukirch–Uchida (CoNF XII Theorem 12.2.1) from (a), (W) and Čebotarev.**

The full `∃!` statement, in exactly the predicate of the challenge, from the three inputs
(a) `LocalCorrespondence ϕ`, (W) `LevelIsoInput ϕ hϕ` and (c) `ChebotarevInput K₁ K₁'` — with the
Frobenius correspondence, the base-level prime identification and the uniqueness half all *proved*.

This is the deliverable's core theorem in its strongest available form: every hypothesis is a
classical statement strictly weaker than the conclusion, and each has an independent proof route in
the workspace:

* (a) — CoNF (12.1.9), "if" direction (`Submission/Work/BrauerHasse/` with
  `Submission/Work/LocalInputs/`);
* (W) — Uchida's weak theorem, nu2d §6 (`Submission/Work/UchidaKummer/`), and in particular
  `NK.ReconstructField.levelIsoInput_of_isWeakUchida` from `NK.UchidaKummer.IsWeakUchida`;
* (c) — Čebotarev's density theorem (`Submission/Work/Chebotarev/`, resting on Artin reciprocity). -/
theorem existsUnique_neukirchUchidaOfLocalCorrespondence (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : LocalCorrespondence ϕ)
    (hlev : NK.ReconstructField.LevelIsoInput ϕ hϕ) (hc : ChebotarevInput K₁ K₁') :
    ∃! σ : K₂' ≃+* K₁',
      (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  obtain ⟨τ₀, hbase⟩ := NK.ReconstructField.exists_primeTransport_eq_primeMap ϕ hϕ a hlev
    Nat.prime_two (isWeakUchida_two_exists_isPrimitiveRoot K₁)
  obtain ⟨σ, hσ, huniq⟩ :=
    existsUnique_sigma_of_localCorrespondence_of_levelIso ϕ hϕ a τ₀
      (fun 𝔭 => (hbase 𝔭).symm) hlev Nat.prime_two (isWeakUchida_two_exists_isPrimitiveRoot K₁) hc
  exact ⟨σ, hσ, fun y hy => huniq y hy⟩

/-- **The base-level prime identification is a theorem** (labelled (i) in the module docstring).

The input `NK.ReconstructField.WeakNeukirchUchida a` of
`NK.Reconstruct.exists_sigma_of_weakNeukirchUchida_and_levelIso` is not independent: it follows
from (a) and (W), the Kummer input being met by `ℓ = 2`. -/
theorem weakNeukirchUchida_of_levelIso (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : LocalCorrespondence ϕ) (hlev : NK.ReconstructField.LevelIsoInput ϕ hϕ) :
    NK.ReconstructField.WeakNeukirchUchida a :=
  NK.ReconstructField.exists_primeTransport_eq_primeMap ϕ hϕ a hlev Nat.prime_two
    (isWeakUchida_two_exists_isPrimitiveRoot K₁)

/-- **Neukirch–Uchida from Uchida's weak theorem as a single input.**

`NK.Reconstruct.existsUnique_neukirchUchidaOfLocalCorrespondence` with the level-wise input (W)
replaced by Uchida's weak theorem `NK.UchidaKummer.IsWeakUchida 2` (two number fields with
isomorphic absolute Galois groups are isomorphic).  The fields live in `Type` because
`NK.UchidaKummer.IsWeakUchida` is stated there. -/
theorem existsUnique_neukirchUchidaOfLocalCorrespondenceAndIsWeakUchida {k₁ k₂ k₁' k₂' : Type}
    [Field k₁] [Field k₂] [Field k₁'] [Field k₂'] [NumberField k₁] [NumberField k₂]
    [Algebra k₁ k₁'] [Algebra k₂ k₂'] [IsSepClosure k₁ k₁'] [IsSepClosure k₂ k₂']
    (ϕ : Gal(k₁'/k₁) ≃* Gal(k₂'/k₂)) (hϕ : IsHomeomorph ϕ) (a : LocalCorrespondence ϕ)
    (hW : NK.UchidaKummer.IsWeakUchida 2) (hc : ChebotarevInput k₁ k₁') :
    ∃! σ : k₂' ≃+* k₁',
      (algebraMap k₂ k₂').range.map σ.toRingHom = (algebraMap k₁ k₁').range ∧
        ∀ g : Gal(k₁'/k₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) :=
  existsUnique_neukirchUchidaOfLocalCorrespondence ϕ hϕ a
    (NK.ReconstructField.levelIsoInput_of_isWeakUchida hW ϕ hϕ) hc

/-- **Neukirch–Uchida from the group-theoretic form of (12.1.9), Uchida's weak theorem and
Čebotarev.**

This is `NK.Reconstruct.existsUnique_neukirchUchidaOfLocalCorrespondence` with the local
correspondence (a) *constructed* from

* `Submission.NeukirchUchida.PreservesDecompositionGroups ϕ` — the "if" direction of CoNF (12.1.9),
  and
* the preservation of the residue characteristic and of the local degree `[κ : ℚ_p]`,

via `Submission.NeukirchUchida.localCorrespondenceOf`. -/
theorem existsUnique_neukirchUchidaOfPreservesDecompositionGroupsAndLevelIso
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ)
    (residueChar : ∀ (A : FinitePlaceOf K₁ K₁') (ℓ : ℕ),
      CharP (NumberField.RingOfIntegers K₁ ⧸
          (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal) ℓ →
        CharP (NumberField.RingOfIntegers K₂ ⧸
          (Submission.NeukirchUchida.primeOf (Submission.NeukirchUchida.placeMap ϕ h A).1
            (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal) ℓ)
    (localDegree : ∀ A : FinitePlaceOf K₁ K₁',
      (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.inertiaDeg ℤ *
          (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.ramificationIdx ℤ =
        (Submission.NeukirchUchida.primeOf (Submission.NeukirchUchida.placeMap ϕ h A).1
          (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal.inertiaDeg ℤ *
          (Submission.NeukirchUchida.primeOf (Submission.NeukirchUchida.placeMap ϕ h A).1
            (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal.ramificationIdx ℤ)
    (hlev : NK.ReconstructField.LevelIsoInput ϕ hϕ) (hc : ChebotarevInput K₁ K₁') :
    ∃! σ : K₂' ≃+* K₁',
      (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) :=
  existsUnique_neukirchUchidaOfLocalCorrespondence ϕ hϕ
    (Submission.NeukirchUchida.localCorrespondenceOf ϕ h residueChar localDegree) hlev hc

/-! ## 7. The challenge target from the sibling areas' named inputs -/

/-- **Neukirch–Uchida from Uchida's module data and Perlis/Gassmann.**

`NK.Reconstruct.existsUnique_neukirchUchidaOfLocalCorrespondenceAndIsWeakUchida` with the weak
Neukirch–Uchida theorem supplied from Uchida's module data
(`NK.UchidaKummer.IsUchidaModuleData 2`) and Perlis/Gassmann
(`NK.UchidaKummer.PerlisGassmannInput`) by
`NK.Reconstruct.isWeakUchida_two_of_uchidaModuleData_and_perlis`. -/
theorem existsUnique_neukirchUchidaOfLocalCorrespondenceAndUchidaData {k₁ k₂ k₁' k₂' : Type}
    [Field k₁] [Field k₂] [Field k₁'] [Field k₂'] [NumberField k₁] [NumberField k₂]
    [Algebra k₁ k₁'] [Algebra k₂ k₂'] [IsSepClosure k₁ k₁'] [IsSepClosure k₂ k₂']
    (ϕ : Gal(k₁'/k₁) ≃* Gal(k₂'/k₂)) (hϕ : IsHomeomorph ϕ) (a : LocalCorrespondence ϕ)
    (hU : NK.UchidaKummer.IsUchidaModuleData 2)
    (hP : NK.UchidaKummer.PerlisGassmannInput) (hc : ChebotarevInput k₁ k₁') :
    ∃! σ : k₂' ≃+* k₁',
      (algebraMap k₂ k₂').range.map σ.toRingHom = (algebraMap k₁ k₁').range ∧
        ∀ g : Gal(k₁'/k₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) :=
  existsUnique_neukirchUchidaOfLocalCorrespondenceAndIsWeakUchida ϕ hϕ a
    (isWeakUchida_two_of_uchidaModuleData_and_perlis hU hP) hc

/-- **The Neukirch–Uchida theorem (CoNF XII Theorem 12.2.1) from the sibling areas' named
inputs.**

This is the *complete* reduction of the challenge target carried out inside `NK.Reconstruct`: the
statement is the challenge statement verbatim (unique existence of the inducing field isomorphism),
and the hypotheses are exactly the named classical inputs of the sibling areas:

1. `Submission.NeukirchUchida.PreservesDecompositionGroups ϕ` — the "if" direction of CoNF
   (12.1.9), the deliverable of `Submission/Work/BrauerHasse/`;
2. preservation of the residue characteristic and of the local degree `[κ : ℚ_p]` — the deliverable
   of `Submission/Work/LocalInputs/`;
3. `NK.UchidaKummer.IsUchidaModuleData 2` and `NK.UchidaKummer.PerlisGassmannInput` — the
   named inputs of `Submission/Work/UchidaKummer/` for Uchida's weak theorem (nu2d §6), which
   provides the level-wise weak Neukirch–Uchida input (W);
4. `NK.Chebotarev.ArtinReciprocityInput` at every finite Galois level — Artin reciprocity, the
   input of `Submission/Work/Chebotarev/` (whose own inputs live in `Submission/Work/GlobalCFT/`).

Nothing else is used: the place correspondence (a), the base-level prime identification (i), the
Frobenius correspondence (b), the Čebotarev density input (c), the Kummer input of the
differentiation lemma, and the uniqueness half are all *proved* in this area (or in the areas this
one imports). -/
theorem existsUnique_neukirchUchidaOfSiblingInputs {k₁ k₂ k₁' k₂' : Type}
    [Field k₁] [Field k₂] [Field k₁'] [Field k₂'] [NumberField k₁] [NumberField k₂]
    [Algebra k₁ k₁'] [Algebra k₂ k₂'] [IsSepClosure k₁ k₁'] [IsSepClosure k₂ k₂']
    (ϕ : Gal(k₁'/k₁) ≃* Gal(k₂'/k₂)) (hϕ : IsHomeomorph ϕ)
    (h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ)
    (residueChar : ∀ (A : FinitePlaceOf k₁ k₁') (ℓ : ℕ),
      CharP (NumberField.RingOfIntegers k₁ ⧸
          (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal) ℓ →
        CharP (NumberField.RingOfIntegers k₂ ⧸
          (Submission.NeukirchUchida.primeOf (Submission.NeukirchUchida.placeMap ϕ h A).1
            (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal) ℓ)
    (localDegree : ∀ A : FinitePlaceOf k₁ k₁',
      (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.inertiaDeg ℤ *
          (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.ramificationIdx ℤ =
        (Submission.NeukirchUchida.primeOf (Submission.NeukirchUchida.placeMap ϕ h A).1
          (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal.inertiaDeg ℤ *
          (Submission.NeukirchUchida.primeOf (Submission.NeukirchUchida.placeMap ϕ h A).1
            (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal.ramificationIdx ℤ)
    (hU : NK.UchidaKummer.IsUchidaModuleData 2)
    (hP : NK.UchidaKummer.PerlisGassmannInput)
    (hA : ∀ (L : IntermediateField k₁ k₁') [FiniteDimensional k₁ L] [Normal k₁ L]
      [NumberField ↥L] [IsGalois k₁ ↥L], NK.Chebotarev.ArtinReciprocityInput k₁ ↥L) :
    ∃! σ : k₂' ≃+* k₁',
      (algebraMap k₂ k₂').range.map σ.toRingHom = (algebraMap k₁ k₁').range ∧
        ∀ g : Gal(k₁'/k₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) :=
  existsUnique_neukirchUchidaOfLocalCorrespondenceAndUchidaData ϕ hϕ
    (Submission.NeukirchUchida.localCorrespondenceOf ϕ h residueChar localDegree) hU hP
    (chebotarevInput_of_artinReciprocity hA)

end NK.Reconstruct
