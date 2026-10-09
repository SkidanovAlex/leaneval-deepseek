import Submission.NK.Reconstruct.endgameOfInputs
import Submission.NK.Reconstruct.levelIsoInput_of_conjugates
import Submission.NK.ReconstructField.Weak
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# What the reconstruction still takes as input, calibrated exactly

This module pins down, with *proved* statements, exactly what
`NK.Reconstruct.existsUnique_neukirchUchidaOfLocalCorrespondence` still consumes beyond the
correspondence data of (a) + (b) + (c):

* `NK.Reconstruct.levelIsoInput_iff_weakNULevels` — the level-wise weak Neukirch–Uchida input (W)
  `NK.ReconstructField.LevelIsoInput ϕ hϕ` is *exactly* the weak Neukirch–Uchida theorem applied
  to the level pairs `(↥L, ↥(levelMap ϕ L))` of the two towers: for each finite level `L ⊆ K₁'` the
  Galois groups `Gal(K₁'/L)` and `Gal(K₂'/levelMap ϕ L)` are isomorphic (`levelGalEquiv`), and (W)
  asks that the fields themselves be isomorphic.
  Hmm, hmm: (W) does not mention any isomorphism between them, so this is the *weak* theorem in the
  form in which Uchida's theorem supplies it
  (`NK.ReconstructField.levelIsoInput_of_isWeakUchida`, from
  `NK.UchidaKummer.IsWeakUchida`).

* `NK.Reconstruct.nonempty_ringEquiv_of_exists_mapsBase` — a `MapsBase` isomorphism
  `σ : K₂' ≃+* K₁'` exists **iff** `K₁ ≅ K₂`
  (`NK.ReconstructField.weakNeukirchUchidaIso_iff_exists_mapsBase`), so the reconstruction's
  *conclusion* contains the weak half of Neukirch–Uchida
  (`NK.Reconstruct.nonempty_ringEquiv_of_exists_conjugates`).

* `NK.Reconstruct.exists_sigma_iff_levelIsoInput_of_frobenius_correspondence` — **the calibration
  of the deliverable's request**: the implication

  `(a) → (b) → (c) → ∃ σ, Conjugates σ ϕ`

  is *equivalent* to the implication

  `(a) → (b) → (c) → (W)`.

  That is: producing `σ` from the σ-free local correspondence (a), the Frobenius correspondence (b)
  and Čebotarev (c) is exactly the same thing as deriving the existence of the level isomorphisms
  from that data.  Both directions are proved: the direction `←` is the σ-producing step of this
  area, the direction `→` is the fact that a realizing `σ` restricts to isomorphisms of the levels
  (`NK.Reconstruct.levelIsoInput_of_conjugates`).

  Nothing in this area derives (W) from (a) + (b) + (c), and it cannot be derived from them without
  a further deep theorem: (W) is the *weak* half of Neukirch–Uchida at the pairs
  `(↥L, ↥(levelMap ϕ L))` — i.e. an instance, at the level pairs, of the same theorem that is being
  proved — and it is *supplied* in the workspace by Uchida's theorem
  (`NK.UchidaKummer.IsWeakUchida`, from `NK.UchidaKummer.IsUchidaModuleData 2` and
  `NK.UchidaKummer.PerlisGassmannInput`, by
  `NK.Reconstruct.isWeakUchida_two_of_uchidaModuleData_and_perlis`).  Every route to `σ` needs the
  weak half, because a `MapsBase` isomorphism `σ` exists only when `K₁ ≅ K₂`
  (`NK.Reconstruct.nonempty_ringEquiv_of_exists_mapsBase`).
-/

set_option linter.unusedVariables false

namespace NK.Reconstruct

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **(W) is the weak Neukirch–Uchida theorem at the level pairs.**

`LevelIsoInput ϕ hϕ` is the assertion that, for every finite level `L ⊆ K₁'`, the fields `↥L` and
`↥(levelMap ϕ L)` are isomorphic.  Their absolute Galois groups `Gal(K₁'/L)` and
`Gal(K₂'/levelMap ϕ L)` are isomorphic (`NK.ReconstructField.levelGalEquiv`), so this is exactly
the weak Neukirch–Uchida statement for the pairs of the two towers. -/
theorem levelIsoInput_iff_weakNULevels (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) :
    NK.ReconstructField.LevelIsoInput ϕ hϕ ↔
      ∀ (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L],
        Nonempty (Gal(K₁'/↥L) ≃* Gal(K₂'/↥(NK.Reconstruct.levelMap ϕ L))) →
          Nonempty (↥L ≃+* ↥(NK.Reconstruct.levelMap ϕ L)) := by
  constructor
  · intro h L _ _; exact h L
  · intro h L _; exact h L ⟨NK.ReconstructField.levelGalEquiv ϕ hϕ L⟩

/-- **The reconstruction's conclusion contains the weak half of Neukirch–Uchida**: a `MapsBase`
isomorphism `σ : K₂' ≃+* K₁'` exists only if the number fields `K₁`, `K₂` are isomorphic
(`NK.ReconstructField.weakNeukirchUchidaIso_iff_exists_mapsBase` proves the converse). -/
theorem nonempty_ringEquiv_of_exists_mapsBase
    (h : ∃ σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) :
    Nonempty (K₁ ≃+* K₂) :=
  (NK.ReconstructField.weakNeukirchUchidaIso_iff_exists_mapsBase (K₁ := K₁) (K₂ := K₂)
    (K₁' := K₁') (K₂' := K₂')).mpr h

/-- The same for the conclusion `∃ σ, Conjugates σ ϕ`. -/
theorem nonempty_ringEquiv_of_exists_conjugates (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (h : ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ) :
    Nonempty (K₁ ≃+* K₂) :=
  nonempty_ringEquiv_of_exists_mapsBase ⟨h.choose, h.choose_spec.1⟩

/-- **The calibration of the deliverable's request.**

The implication "the σ-free local correspondence (a) *and* the Frobenius correspondence (b) *and*
Čebotarev (c) yield `∃ σ, Conjugates σ ϕ`" is *equivalent* to the implication "… yield the
level-wise weak Neukirch–Uchida input (W)".

* `←`: the σ-producing step of this area
  (`NK.Reconstruct.exists_sigma_of_localCorrespondence_of_levelIsoInput`);
* `→`: a realizing `σ` restricts to isomorphisms of the levels
  (`NK.Reconstruct.levelIsoInput_of_conjugates`).

So the deliverable's requested theorem is precisely the derivation of (W) from (a) + (b) + (c); and
(W) is exactly the *weak* half of Neukirch–Uchida at the level pairs
(`NK.Reconstruct.levelIsoInput_iff_weakNULevels`), which the workspace obtains from Uchida's
theorem (`NK.UchidaKummer.IsWeakUchida`, from `IsUchidaModuleData 2` and `PerlisGassmannInput`). -/
theorem exists_sigma_iff_levelIsoInput_of_frobenius_correspondence
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) (a : LocalCorrespondence ϕ) :
    ((b : FrobeniusCorrespondencePlace ϕ hϕ a) → (c : ChebotarevInput K₁ K₁') →
        ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ) ↔
      ((b : FrobeniusCorrespondencePlace ϕ hϕ a) → (c : ChebotarevInput K₁ K₁') →
        NK.ReconstructField.LevelIsoInput ϕ hϕ) := by
  constructor
  · intro h b c
    obtain ⟨σ, hσ⟩ := h b c
    exact levelIsoInput_of_conjugates hϕ σ hσ
  · intro h b c
    exact exists_sigma_of_localCorrespondence_of_levelIsoInput ϕ hϕ a (h b c) c

end NK.Reconstruct
