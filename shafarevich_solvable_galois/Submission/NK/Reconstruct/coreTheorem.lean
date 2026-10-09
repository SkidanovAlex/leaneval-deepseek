import Submission.NK.Reconstruct.endgameOfInputs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The core theorem of the reconstruction, under its requested name

The deliverable of this area asks for a theorem of the exact shape

  `NK.Reconstruct.exists_sigma_of_localCorrespondence : <hypotheses> → ∃ σ : K₂' ≃+* K₁',
  Conjugates σ ϕ`

whose hypotheses are, as far as they can be supplied, the σ-free data of the reconstruction: the
local correspondence (a) of CoNF (12.1.9), the Frobenius correspondence (b) and the Čebotarev density
input (c).  The name `NK.Reconstruct.exists_sigma_of_localCorrespondence` is used here for the
*σ-free* form: every hypothesis below mentions `ϕ`, `K₁`, `K₂`, `K₁'`, `K₂'` and the place system
only — none of them mentions a field isomorphism `K₂' ≃+* K₁'`.  (The older theorem which took a
*realized* local correspondence `GoodLocalCorrespondence`, i.e. one carrying `σ` as a field, has been
renamed `exists_sigma_of_goodLocalCorrespondence`, so that the deliverable's name does not hide `σ`
among its hypotheses.)

The one additional hypothesis here, `NK.ReconstructField.LevelIsoInput ϕ hϕ`, is the level-wise
weak Neukirch–Uchida statement (W) — also σ-free.  It is *not* an independent assumption: by
`NK.Reconstruct.exists_sigma_iff_levelIsoInput_of_frobenius_correspondence` (§15.1) the implication

  `(a) → (b) → (c) → ∃ σ, Conjugates σ ϕ`

is *equivalent* to `(a) → (b) → (c) → (W)`, so removing (W) is exactly the derivation of the weak
Neukirch–Uchida theorem at the level pairs from (a), (b), (c) and the rank inputs
`NK.Reconstruct.RankFormulaInput` (CoNF (10.3.20)) and `NK.Reconstruct.RankStrictMonoInput`
(CoNF (10.3.7) / Shimizu Lemma 4f.2) by the assembly of Shimizu §4; see README §18.5 for the exact
remaining steps, whose infrastructure (the base change `π_{L/K}`, its Frobenius compatibility, the
outer action `τ^*`, the isomorphism `σ̄`, and the *complete* measure step of Proposition 4f.3) is all
proved in this area.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.Reconstruct

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
  [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The core theorem of the reconstruction**: from the σ-free local correspondence (a), the
level-wise weak Neukirch–Uchida input (W) and the Čebotarev density input (c), there is
`σ : K₂' ≃+* K₁'` with `Conjugates σ ϕ`.

All hypotheses are σ-free; the Frobenius correspondence (b), the base-level prime identification, the
Kummer input, the realization of the place correspondence and the uniqueness half are *derived*. -/
theorem exists_sigma_of_localCorrespondence_levelIso (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : LocalCorrespondence ϕ)
    (hlev : NK.ReconstructField.LevelIsoInput ϕ hϕ) (hc : ChebotarevInput K₁ K₁') :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ :=
  exists_sigma_of_localCorrespondence_of_levelIsoInput ϕ hϕ a hlev hc

/-- **The same, with the Čebotarev input isolated as hypothesis (c) only**: the conclusion follows
already from (a) and (W), since the Čebotarev input is used only to produce the σ-based Frobenius
correspondence, which (W) supplies directly.  Stated in the shape
`<hypotheses> → (c) → ∃ σ, Conjugates σ ϕ` of the deliverable. -/
theorem exists_sigma_of_localCorrespondence_of_levelIsoInput_curve (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : LocalCorrespondence ϕ)
    (hlev : NK.ReconstructField.LevelIsoInput ϕ hϕ) :
    ChebotarevInput K₁ K₁' → ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ :=
  fun hc => exists_sigma_of_localCorrespondence_levelIso ϕ hϕ a hlev hc

end NK.Reconstruct
