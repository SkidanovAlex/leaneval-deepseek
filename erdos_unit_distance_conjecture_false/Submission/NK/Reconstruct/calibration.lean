import Submission.NK.Reconstruct.endgameOfInputs
import Submission.NK.Reconstruct.levelIsoInput_of_conjugates

/-!
# The exact strength of the level-wise input (W)

`NK.Reconstruct.existsUnique_neukirchUchidaOfLocalCorrespondence` derives Neukirch–Uchida from
three inputs: the local correspondence **(a)** of CoNF (12.1.9), the level-wise weak
Neukirch–Uchida input **(W)** `NK.ReconstructField.LevelIsoInput ϕ hϕ`, and the Čebotarev input
**(c)**.

This module calibrates (W) exactly:

* **(W) is necessary for the conclusion**: if `σ : K₂' ≃+* K₁'` realizes `ϕ`
  (`Conjugates σ ϕ`), then every finite level `L ⊆ K₁'` is isomorphic to its image
  `levelMap ϕ L` — the isomorphism being the restriction of `σ`
  (`NK.Reconstruct.levelIsoInput_of_conjugates`).  Hence (W) is not an extra assumption beyond the
  statement of the theorem.
* **Conversely**, given (a) and (c), (W) *does* yield the conclusion
  (`NK.Reconstruct.exists_sigma_of_localCorrespondence_of_levelIsoInput`).

Consequently, **in the presence of (a) and (c) the input (W) is equivalent to the conclusion**;
this is stated as `NK.Reconstruct.exists_conjugates_iff_levelIsoInput`.  This is the honest
calibration of the reconstruction: the theorem cannot be derived from a hypothesis that does not,
together with the true statements (a) and (c), already determine the answer.  What the reduction
*does* deliver is that (W) is

* **σ-free** (it mentions no field isomorphism of the separable closures, only isomorphisms of
  finite levels, with no compatibility between them), and
* a **consequence of Uchida's weak theorem**
  (`NK.ReconstructField.levelIsoInput_of_isWeakUchida`, from
  `NK.UchidaKummer.IsWeakUchida`), a theorem of §6 of Uchida's paper whose proof is disjoint from
  the strong form of Neukirch–Uchida, and which in turn is derived from
  `NK.UchidaKummer.IsUchidaModuleData 2` and `NK.UchidaKummer.PerlisGassmannInput`
  (`NK.Reconstruct.isWeakUchida_two_of_uchidaModuleData_and_perlis`).

So the content of this area is the *derivation* of `σ` from (W): the pinning of the level
isomorphisms by the prime correspondence (Neukirch's Lemma `α identifies with σ on primes`), the
base-field identification (Neukirch's Lemma 5.2), the Frobenius correspondence and the Čebotarev
endgame.
-/

set_option linter.unusedVariables false

namespace NK.Reconstruct

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The conclusion implies the level-wise input (W).** -/
theorem levelIsoInput_of_exists_conjugates (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (h : ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ) :
    NK.ReconstructField.LevelIsoInput ϕ hϕ :=
  let ⟨σ, hσ⟩ := h
  levelIsoInput_of_conjugates hϕ σ hσ

/-- **The exact strength of the level-wise input (W)**: given the local correspondence (a) and the
Čebotarev input (c), the existence of a realizing field isomorphism and the level-wise weak
Neukirch–Uchida input (W) are *equivalent*.

The forward implication is the necessary direction (the restriction of `σ` to a level), the backward
one is the σ-producing step of this area
(`NK.Reconstruct.exists_sigma_of_localCorrespondence_of_levelIsoInput`).  Note that the
equivalence uses (c), a *true* theorem (Čebotarev); without it (W) alone does not produce `σ`. -/
theorem exists_conjugates_iff_levelIsoInput (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : LocalCorrespondence ϕ) (hc : ChebotarevInput K₁ K₁') :
    (∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ) ↔
      NK.ReconstructField.LevelIsoInput ϕ hϕ :=
  ⟨levelIsoInput_of_exists_conjugates ϕ hϕ,
    fun hlev => exists_sigma_of_localCorrespondence_of_levelIsoInput ϕ hϕ a hlev hc⟩

end NK.Reconstruct
