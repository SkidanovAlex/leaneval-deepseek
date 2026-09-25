import Mathlib
import Submission.NK.NUV2.Wall
import Submission.NK.NUV2.neukirch_uchida_of_chaptersV2
import Submission.NK.NUV2.ShrinkTransport

/-! Guidance from the project lead (the requester):

## Context (orchestrator, 2026-09-23)
The old wall `NK.EndgameRepair.ClassicalChaptersRepaired` is UNSATISFIABLE — do not use it or any of its fields'
catalogues as targets: `IndecomposedDeep.DeepInputs.indexOne` fails (quartic K with 2 = 𝔭₁𝔭₂³, K_{𝔭₂} ≅ ℚ₂(∛2):
G_{ℚ₂(∛2)} ≤ D_A is self-normalising, ≅ a local Galois group, of index 3), and `TowerRankCore.finiteIndex_isClosed`
is false without `FiniteDimensional κ M`. Also avoid `LocalStructure.LocalNUExistence` (G_M ≅ G_κ ⇒ M ≅ κ is false,
Yamagata/Jarden–Ritter), `UchidaKummer.IsWeakUchida`, `CyclicPrimeReduction`.
The new wall is `NK.NUV2.ChaptersV2` (`Submission/Work/NUV2/Wall.lean`, do NOT edit): the four inputs of the proved
`NK.EndgameRepair.exists_sigma_of_correctedResiduals`. Library inputs being proved elsewhere in this workspace and
allowed as hypotheses where the statement has them: `NK.GlobalCFTdeep.FundamentalClassElement` (global
fundamental class ⇒ class-formation axioms, reciprocity C_K/N C_L ≅ Gal(L/K)ᵃᵇ via
`artinReciprocity_of_cohomologicalFieldAxiom`, Tate's theorem, Albert–Brauer–Hasse–Noether) and
`NK.LocalArtin.KernelCondition` at every completion (⇒ `NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion`).
Design rules: state every local isomorphism as a CONTINUOUS isomorphism (ϕ is a homeomorphism; this removes
Nikolov–Segal entirely); for Brauer arguments use an ODD prime p (Br(ℝ)[p] = 0). Instantiate every new sub-statement
at K = ℚ and at the quartic above as a satisfiability check before relying on it. Delegate; one lemma per step.
## This lemma
Same as the proved `NK.NUV2.neukirch_uchida_of_chaptersV2` (read its file), but the four inputs are given at
`Type 0` only. Transport the challenge's fields (any universes) to `Type 0` models via `Shrink` (or explicit
`Equiv`s to countable types): a number field is countable, and a separable closure of a countable field is
countable (algebraic over a countable field). Build ring isomorphisms K ≃+* Shrink K with transported
`Field`/`NumberField`/`Algebra`/`IsSepClosure` structures, transport ϕ (continuous), apply the inputs, and pull σ
back; uniqueness is the proved `Submission.NeukirchUchida.unique_sigma`.

## Realization (this file + `Submission/Work/NUV2/ShrinkTransport.lean`)

The transport is exactly the pattern of `Submission/Work/UniverseUnify/Assembly.lean` (which lifts the four
fields to a *common bigger* universe along `ULift`), with `ULift` replaced by `Shrink.{0}` — the *universe-zero
model* of a small type:

* a number field is countable (`Finsupp.Countable.of_moduleFinite`), and a separable closure of a countable
  field is countable (Mathlib's `Algebraic.countable`, since the extension is algebraic);
* `Shrink` carries the field, number-field, algebra and finite-dimension structures
  (`NK.GlobalCFTdeep.HasseIndex.shrink_numberField`, `shrinkAlgebra`, `shrink_hc`), and this file adds the
  transported `IsSepClosed`/`IsSepClosure` (`NK.NUV2.ShrinkModels.instIsSepClosureShrink`);
* `NK.GlobalCFTdeep.HasseIndex.shrink_mapsBase` gives the `MapsBase` computation, so that conjugation by
  `Shrink.ringEquiv` identifies `Gal(Shrink K' / Shrink K)` with `Gal(K'/K)` — a *homeomorphism* of the Krull
  topologies by `NK.NeukirchUchida.isHomeomorph_conjHomEquiv`;
* `NK.NUV2.ShrinkModels.transportGalEquiv` carries `ϕ` to the models, `…isHomeomorph_transportGalEquiv` keeps
  `IsHomeomorph`, and `existsUnique_shrink` (proved from `NK.UniverseUnify.mapsBase_conj` and the pure
  `RingEquiv` identity `NK.UniverseUnify.ulift_conj_identity_down`) transports the `∃!` statement back.

Applying the four `Type 0` inputs at the models and `NK.EndgameRepair.exists_sigma_of_correctedResiduals`
there (uniqueness by `Submission.NeukirchUchida.unique_sigma`) gives the challenge at the original universes.

Note on universes: `NK.NUV2.Capstone0` has four universe parameters, one for each of the four
fields of the conclusion, and applying this theorem at four *independent* universe levels requires
the universe instantiation to be given explicitly, e.g.
`NK.NUV2.neukirch_uchida_of_chaptersV2_0.{u₁, u₂, u₃, u₄} hLC hFrob hRes hCheb ϕ he`
(at `Type 0` fields the application infers the universes on its own).  The same caveat applies to
the universe-lifted form `NK.NUV2.neukirch_uchida_of_chaptersV2`. -/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.NUV2

open Submission.NeukirchUchida

/-- **The Neukirch–Uchida capstone from the four `Type 0` inputs of the second wall.**

This is `NK.NUV2.Capstone0`: the four inputs `LCAll0`, `FrobAll0`, `ResAll0`, `ChebAll0` are
stated for fields in `Type 0`, and the conclusion is the challenge with four independent universe
parameters.  The proof transports every field to its universe-zero `Shrink` model, applies the
inputs and `NK.EndgameRepair.exists_sigma_of_correctedResiduals` there, and descends the `∃!`
along the conjugation bijection `NK.NUV2.ShrinkModels.shrinkRingEquivEquiv`. -/
theorem neukirch_uchida_of_chaptersV2_0 : NK.NUV2.Capstone0 := by
  intro hLC hFrob hRes hCheb
  intro K₁ K₂ K₁' K₂' _ _ _ _ _ _ _ _ _ _ ϕ he
  -- ## Smallness of the four fields: number fields are countable, and so are their separable closures
  haveI hc₁ : Countable K₁ := ShrinkModels.countable_of_numberField K₁
  haveI hc₂ : Countable K₂ := ShrinkModels.countable_of_numberField K₂
  haveI hc₁' : Countable K₁' := ShrinkModels.countable_of_isSepClosure K₁ K₁'
  haveI hc₂' : Countable K₂' := ShrinkModels.countable_of_isSepClosure K₂ K₂'
  haveI hs₁ : Small.{0} K₁ := Countable.toSmall K₁
  haveI hs₂ : Small.{0} K₂ := Countable.toSmall K₂
  haveI hs₁' : Small.{0} K₁' := Countable.toSmall K₁'
  haveI hs₂' : Small.{0} K₂' := Countable.toSmall K₂'
  -- ## the transported isomorphism of absolute Galois groups of the `Shrink` models
  have he₀ : IsHomeomorph (ShrinkModels.transportGalEquiv ϕ) :=
    ShrinkModels.isHomeomorph_transportGalEquiv ϕ he
  -- ## the four inputs, instantiated at the models
  obtain ⟨a⟩ := hLC (Shrink.{0} K₁) (Shrink.{0} K₂) (Shrink.{0} K₁') (Shrink.{0} K₂')
    (ShrinkModels.transportGalEquiv ϕ) he₀
  have b : NK.Reconstruct.FrobeniusCorrespondencePlace (ShrinkModels.transportGalEquiv ϕ) he₀ a :=
    hFrob (Shrink.{0} K₁) (Shrink.{0} K₂) (Shrink.{0} K₁') (Shrink.{0} K₂')
      (ShrinkModels.transportGalEquiv ϕ) he₀ a
  have hres : NK.RankTheoryDeep.CorrectedResidualsDerived (Shrink.{0} K₁) (Shrink.{0} K₁') 2 :=
    hRes (Shrink.{0} K₁) (Shrink.{0} K₁')
  have hcheb : NK.ReconstructEndgame.ChebotarevInputDerived (Shrink.{0} K₁) (Shrink.{0} K₁') :=
    hCheb (Shrink.{0} K₁) (Shrink.{0} K₁')
  -- ## the σ-producing step at the models
  obtain ⟨σ₀, hσ₀⟩ :=
    NK.EndgameRepair.exists_sigma_of_correctedResiduals
      (K₁ := Shrink.{0} K₁) (K₁' := Shrink.{0} K₁') (K₂ := Shrink.{0} K₂) (K₂' := Shrink.{0} K₂')
      (ShrinkModels.transportGalEquiv ϕ) he₀ a b 2 hres hcheb
  -- ## descend the `∃!` to the original universes
  exact ShrinkModels.existsUnique_shrink_mp ϕ
    ⟨σ₀, hσ₀,
      fun y hy => Submission.NeukirchUchida.unique_sigma (ShrinkModels.transportGalEquiv ϕ) he₀ hy hσ₀⟩

end NK.NUV2
