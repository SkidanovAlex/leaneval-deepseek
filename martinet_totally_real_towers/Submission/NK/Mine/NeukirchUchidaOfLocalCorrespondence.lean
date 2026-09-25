import Submission.NK.Mine.ExistsSigmaOfLocalCorrespondence
import Submission.NeukirchUchida.Endgame
import Submission.NeukirchUchida.Core

/-!
# The Neukirch–Uchida theorem from the place correspondence and the level-wise weak theorem

Combining

* `NK.Mine.exists_sigma_of_localCorrespondence` — the existence half from the σ-free place
  correspondence (A) of CoNF (12.1.9) and the level-wise weak Neukirch–Uchida input (which the
  general Bauer theorem `NK.BauerGeneral.weakNeukirchUchidaIso_of_splitsCompletely_iff` makes a
  theorem), and
* `Submission.NeukirchUchida.unique_sigma` — the uniqueness half (CoNF (12.1.6), proved in this
  workspace from the rigidity of places),

this file states the full `∃!` form of CoNF XII Thm 12.2.1 in exactly the shape of the challenge
statement, from (A) and the level-wise weak input.  The two further forms take (A) apart into the
group-theoretic input `PreservesDecompositionGroups ϕ` (CoNF (12.1.9) "if", block (i) of the
roadmap) and the two arithmetic fields of the place correspondence (block (ii)).
-/

namespace NK.Mine

open IntermediateField

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **Neukirch–Uchida (CoNF XII Thm 12.2.1) from the place correspondence and the level-wise weak
Neukirch–Uchida input.** -/
theorem neukirch_uchida_of_localCorrespondence
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hlev : NK.ReconstructField.LevelIsoInput ϕ he) :
    ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  obtain ⟨σ, hσ⟩ := exists_sigma_of_localCorrespondence ϕ he a hlev
  exact ⟨σ, hσ, fun y hy => Submission.NeukirchUchida.unique_sigma ϕ he hy hσ⟩

/-- **Neukirch–Uchida (CoNF XII Thm 12.2.1) from CoNF (12.1.9) "if" plus the two arithmetic fields
of the place correspondence, and the level-wise weak Neukirch–Uchida input.**

`h` is `Submission.NeukirchUchida.PreservesDecompositionGroups ϕ`, the group-theoretic input (block
(i) of the roadmap, produced by `Submission/Work/BrauerTwist/` from the local Brauer group, the
twisted Hasse principle and Neukirch's local argument); `residueChar` and `localDegree` are the two
arithmetic fields of `NK.Reconstruct.LocalCorrespondence` (block (ii), produced by
`NK.Mine.residueChar_preserved_of_localInputs` / `localDegree_preserved_of_localInputs` from the
local structure theory of the completions). -/
theorem neukirch_uchida_of_decompositionGroups
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ)
    (residueChar : ∀ (A : NK.Reconstruct.FinitePlaceOf K₁ K₁') (ℓ : ℕ),
      CharP (NumberField.RingOfIntegers K₁ ⧸
          (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal) ℓ →
        CharP (NumberField.RingOfIntegers K₂ ⧸
          (Submission.NeukirchUchida.primeOf
            (Submission.NeukirchUchida.placeMap ϕ h A).1
            (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal) ℓ)
    (localDegree : ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
      (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.inertiaDeg ℤ *
          (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.ramificationIdx ℤ =
        (Submission.NeukirchUchida.primeOf
            (Submission.NeukirchUchida.placeMap ϕ h A).1
            (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal.inertiaDeg ℤ *
          (Submission.NeukirchUchida.primeOf
            (Submission.NeukirchUchida.placeMap ϕ h A).1
            (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal.ramificationIdx ℤ)
    (hlev : NK.ReconstructField.LevelIsoInput ϕ he) :
    ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) :=
  neukirch_uchida_of_localCorrespondence ϕ he
    (Submission.NeukirchUchida.localCorrespondenceOf ϕ h residueChar localDegree) hlev

end NK.Mine
