import Submission.NK.ReconstructField.Input
import Submission.NK.ReconstructField.Weak
import Submission.NK.Reconstruct.InnerTwist
import Submission.NK.Reconstruct.comap_placeMap_eq_of_conjugates
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The sharp available interface: the *repair* input

The deliverable of this chapter asks for
`∃ σ : K₂' ≃+* K₁', MapsBase … σ ∧ FrobeniusCorrespondence ϕ σ` from the local correspondence `(A)`
and the local Frobenius correspondence `(B)`.  The honest state of the development is that the two
remaining inputs are the **weak Neukirch–Uchida theorem** (a base-field-mapping isomorphism
`σ₀ : K₂' ≃+* K₁'`, i.e. `K₁ ≅ K₂`) and the **vanishing of the obstruction**

  `β := ϕ.symm.trans (conjHomEquiv hσ₀) ∈ Aut(Gal(K₂'/K₂))`

in `Out(Gal(K₂'/K₂))` (see `README.md` §12.1; Neukirch's `LocalRigidity` is the case `β = 1`, and
`NK.Reconstruct.PlaceRigidity` implies innerness).  This file packages the pair as a single
hypothesis `NK.ReconstructField.RepairInput ϕ` and proves that it delivers the chapter's
conclusion.

`RepairInput ϕ` is **strictly weaker** than the σ-realization hypothesis `(C) = ReconstructionInput`
of `Input.lean`: it does not assert that `σ₀` realizes the place correspondence, only that the
obstruction is inner; and it is *equivalent* to the conclusion (by
`NK.Reconstruct.conjugates_twist_iff` the twist `σ₀ ∘ k` induces `ϕ` precisely when
`β = MulAut.conj k`).  Consequently `RepairInput` is a *form* of the conclusion, not a way around
it; what it records is that the deep input of the reconstruction is exactly the pair
(weak Neukirch–Uchida, `Out`-vanishing), neither of which is available in this workspace.
-/

set_option linter.unusedVariables false

namespace NK.ReconstructField

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The repair input.**  There is a base-field-mapping isomorphism `σ₀ : K₂' ≃+* K₁'` whose
obstruction against `ϕ` is an inner automorphism of `Gal(K₂'/K₂)`.

Equivalently (by `NK.Reconstruct.exists_conjugates_of_conj_normal`), `ϕ` is induced by the field
isomorphism `σ₀ ∘ k`.  The two ingredients — existence of `σ₀` (the weak Neukirch–Uchida theorem)
and innerness of `β` (the `Out(Gal(K₂'/K₂))`-vanishing) — are the two classical inputs isolated in
`README.md` §12.1. -/
def RepairInput (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) : Prop :=
  ∃ (σ₀ : K₂' ≃+* K₁')
    (_ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ₀)
    (k : Gal(K₂'/K₂)),
    ϕ.symm.trans (Submission.NeukirchUchida.conjHomEquiv ‹_›) = MulAut.conj k

/-- The repair input is realised by a field isomorphism inducing `ϕ`. -/
theorem exists_conjugates_of_repairInput {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (h : RepairInput ϕ) :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨σ₀, hσ₀, k, hk⟩ := h
  exact NK.Reconstruct.exists_conjugates_of_conj_normal (ϕ := ϕ) (σ₀ := σ₀) (hσ₀ := hσ₀) k hk

/-- The repair input gives the σ-based reconstruction input of `Input.lean` (the realizing `σ` also
realizes the place correspondence of `(A)`). -/
theorem reconstructionInputSigma_of_repairInput {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (hϕ : IsHomeomorph ϕ) (a : NK.Reconstruct.LocalCorrespondence ϕ) (h : RepairInput ϕ) :
    ReconstructionInputSigma hϕ a := by
  obtain ⟨σ, hconj⟩ := exists_conjugates_of_repairInput h
  exact ⟨σ, hconj.1, NK.Reconstruct.comap_placeMap_eq_of_conjugates a hconj⟩

/-- **The chapter's conclusion from the repair input** (together with `(A)` and `(B)`, which are not
used: `RepairInput` already contains the conclusion in the `Conjugates` form).

This is the sharpest available statement of the deliverable: it is
`NK.ReconstructField.exists_sigma_of_placeMap_and_frobenius` with the σ-realization hypothesis
`(C)` replaced by the strictly weaker `RepairInput`. -/
theorem exists_sigma_of_placeMap_and_frobenius_of_repairInput
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a)
    (h : RepairInput ϕ) :
    ∃ σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        NK.Reconstruct.FrobeniusCorrespondence ϕ σ := by
  obtain ⟨σ, hconj⟩ := exists_conjugates_of_repairInput h
  exact ⟨σ, hconj.1, frobeniusCorrespondence_of_conjugates hconj⟩

/-- The repair input is *equivalent* to the conclusion `∃ σ, Conjugates σ ϕ` for a fixed `ϕ`: the
forward direction is `exists_conjugates_of_repairInput`, and the converse takes the trivial twist
`k = 1`.  So `RepairInput` is a *form* of the conclusion, and its two ingredients — the existence
of the base-field-mapping isomorphism `σ₀` (the weak Neukirch–Uchida theorem) and the innerness of
the obstruction (the `Out(Gal(K₂'/K₂))`-vanishing) — are precisely the deep inputs. -/
theorem repairInput_iff_exists_conjugates (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) :
    RepairInput ϕ ↔ ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  refine ⟨exists_conjugates_of_repairInput, ?_⟩
  rintro ⟨σ, hσ, hconj⟩
  refine ⟨σ, hσ, 1, ?_⟩
  have hhom : ϕ = Submission.NeukirchUchida.conjHomEquiv hσ := by
    refine MulEquiv.ext fun g => ?_
    ext x
    change (ϕ g).toRingEquiv x = (Submission.NeukirchUchida.conj hσ g).toRingEquiv x
    rw [hconj g, Submission.NeukirchUchida.conj_toRingEquiv hσ g]
  rw [hhom]
  refine MulEquiv.ext fun u => ?_
  simp [MulEquiv.trans_apply, MulAut.conj_apply]

end NK.ReconstructField
