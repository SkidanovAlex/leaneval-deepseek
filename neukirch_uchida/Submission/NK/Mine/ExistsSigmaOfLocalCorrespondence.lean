import Submission.NK.Mine.exists_sigma_of_frobeniusCorrespondence
import Submission.NK.ReconstructField.weakNeukirchUchida

/-!
# The existence half of Neukirch–Uchida from the place correspondence alone

`Submission/Work/ReconstructField/weakNeukirchUchida.lean` proves (this session) the final theorem
of the CoNF §12.2 reconstruction:

```lean
NK.ReconstructField.exists_sigma_of_placeMap_and_frobenius_of_levelIsoInput
    (ϕ) (hϕ : IsHomeomorph ϕ) (a : LocalCorrespondence ϕ)
    (hlev : LevelIsoInput ϕ hϕ) (hℓ : ℓ.Prime) (hμ : ∃ ζ : K₁, IsPrimitiveRoot ζ ℓ) :
    ∃ σ : K₂' ≃+* K₁', MapsBase … σ ∧ FrobeniusCorrespondence ϕ σ
```

Its hypotheses are σ-free: (A) the place correspondence, the *level-wise* weak Neukirch–Uchida input,
a prime `ℓ` and `μ_ℓ ⊆ K₁`.  Taking `ℓ = 2` makes `hμ` automatic (`-1` is a primitive square root
of unity in every field of characteristic `≠ 2`), so the reconstruction needs **only (A) and the
level-wise weak input** — in particular it does *not* need the local Frobenius correspondence (B),
and it does not need the Jarden–Ritter rigidity `PlaceRigidity`.

Composing with `NK.Mine.exists_sigma_of_frobeniusCorrespondence` (the detection lemma, which turns
`MapsBase σ` plus the Frobenius correspondence into `Conjugates σ ϕ`) gives the existence half
`∃ σ, Conjugates σ ϕ` from (A) and `LevelIsoInput` alone.  This is the form in which the endgame
consumes the reconstruction: the remaining obligation is only the place correspondence (A).
-/

namespace NK.Mine

open IntermediateField

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- `-1` is a primitive square root of unity in a number field. -/
theorem isPrimitiveRoot_neg_one_of_numberField (K : Type*) [Field K] [NumberField K] :
    ∃ ζ : K, IsPrimitiveRoot ζ 2 :=
  ⟨-1, IsPrimitiveRoot.neg_one 0 (by norm_num)⟩

/-- **The existence half of Neukirch–Uchida (CoNF XII Thm 12.2.1) from the place correspondence
and the level-wise weak Neukirch–Uchida input.**

The local Frobenius correspondence (input (B) of `Submission/NeukirchUchida/Endgame.lean`) and the
Jarden–Ritter place rigidity are *not* needed: the reconstruction of
`Submission/Work/ReconstructField/` produces the `MapsBase` isomorphism together with its Frobenius
correspondence, and `NK.Mine.exists_sigma_of_frobeniusCorrespondence` converts that into
`Conjugates σ ϕ`. -/
theorem exists_sigma_of_localCorrespondence
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hlev : NK.ReconstructField.LevelIsoInput ϕ hϕ) :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨σ, hσ, b⟩ :=
    NK.ReconstructField.exists_sigma_of_placeMap_and_frobenius_of_levelIsoInput ϕ hϕ a hlev
      Nat.prime_two (isPrimitiveRoot_neg_one_of_numberField K₁)
  exact exists_sigma_of_frobeniusCorrespondence ϕ σ hσ b

end NK.Mine
