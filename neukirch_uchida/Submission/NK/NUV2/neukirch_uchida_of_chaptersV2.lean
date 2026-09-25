import Mathlib
import Submission.NK.NUV2.Wall
import Submission.NK.UniverseUnify.Assembly

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
Pure transport: copy the pattern (the ∀-universe Props LCAll etc. are instantiated at max u₁ u₂ u₃ u₄ on the ULift copies) of `NK.UniverseUnify.neukirch_uchida_of_repairedChapters_lifted`
(`Submission/Work/UniverseUnify/Assembly.lean`: `transportGalEquiv`, `isHomeomorph_transportGalEquiv`,
`existsUnique_ulift_mp`) with `NK.EndgameRepair.exists_sigma_of_correctedResiduals` + the proved uniqueness
(`Submission.NeukirchUchida.unique_sigma` / Core.lean) in place of the old wall.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.NUV2

open Submission.NeukirchUchida

universe u₁ u₂ u₃ u₄

/-- **The Neukirch–Uchida capstone from the four inputs of the second wall.**

The four hypotheses are the `∀`-universe propositions `LCAll`, `FrobAll`, `ResAll`, `ChebAll` of
`Submission/Work/NUV2/Wall.lean`, stated at the single universe `max u₁ u₂ u₃ u₄`; the conclusion is
the `∃!` of the challenge at four independent universes `u₁ u₂ u₃ u₄`.

The proof is the transport pattern of `NK.UniverseUnify.neukirch_uchida_of_repairedChapters_lifted`:

* lift the four fields to the common universe `w := max u₁ u₂ u₃ u₄` by `ULift`, and transport `ϕ`
  to `NK.UniverseUnify.transportGalEquiv ϕ` (a homeomorphism by
  `NK.UniverseUnify.isHomeomorph_transportGalEquiv`);
* instantiate the four inputs at the lifted fields: the place correspondence `a` is the witness of
  the `Nonempty` of `LCAll`, the Frobenius correspondence `b` is `FrobAll`, and the rank and
  Čebotarev hypotheses are `ResAll` (at `ℓ = 2`) and `ChebAll`;
* apply the proved σ-producing step `NK.EndgameRepair.exists_sigma_of_correctedResiduals`
  (existence) and `Submission.NeukirchUchida.unique_sigma` (uniqueness) at the lifted fields,
  obtaining the `∃!` at the lifted types;
* descend along `NK.UniverseUnify.existsUnique_ulift_mp`. -/
private theorem neukirch_uchida_of_chaptersV2_aux : NK.NUV2.Capstone.{u₁, u₂, u₃, u₄} := by
  intro hLC hFrob hRes hCheb
  intro K₁ K₂ K₁' K₂' _ _ _ _ _ _ _ _ _ _ ϕ he
  -- ## the transported isomorphism at the common universe `w = max u₁ u₂ u₃ u₄`
  have he' : IsHomeomorph (NK.UniverseUnify.transportGalEquiv ϕ) :=
    NK.UniverseUnify.isHomeomorph_transportGalEquiv ϕ he
  -- ## the four inputs, instantiated at the lifted fields
  obtain ⟨a⟩ :=
    hLC (ULift.{max u₁ u₂ u₃ u₄, u₁} K₁) (ULift.{max u₁ u₂ u₃ u₄, u₂} K₂)
      (ULift.{max u₁ u₂ u₃ u₄, u₃} K₁') (ULift.{max u₁ u₂ u₃ u₄, u₄} K₂')
      (NK.UniverseUnify.transportGalEquiv ϕ) he'
  have b : NK.Reconstruct.FrobeniusCorrespondencePlace
      (NK.UniverseUnify.transportGalEquiv ϕ) he' a :=
    hFrob (ULift.{max u₁ u₂ u₃ u₄, u₁} K₁) (ULift.{max u₁ u₂ u₃ u₄, u₂} K₂)
      (ULift.{max u₁ u₂ u₃ u₄, u₃} K₁') (ULift.{max u₁ u₂ u₃ u₄, u₄} K₂')
      (NK.UniverseUnify.transportGalEquiv ϕ) he' a
  have hres : NK.RankTheoryDeep.CorrectedResidualsDerived
      (ULift.{max u₁ u₂ u₃ u₄, u₁} K₁) (ULift.{max u₁ u₂ u₃ u₄, u₃} K₁') 2 :=
    hRes (ULift.{max u₁ u₂ u₃ u₄, u₁} K₁) (ULift.{max u₁ u₂ u₃ u₄, u₃} K₁')
  have hcheb : NK.ReconstructEndgame.ChebotarevInputDerived
      (ULift.{max u₁ u₂ u₃ u₄, u₁} K₁) (ULift.{max u₁ u₂ u₃ u₄, u₃} K₁') :=
    hCheb (ULift.{max u₁ u₂ u₃ u₄, u₁} K₁) (ULift.{max u₁ u₂ u₃ u₄, u₃} K₁')
  -- ## the σ-producing step at the lifted fields
  obtain ⟨σ, hσ⟩ :=
    NK.EndgameRepair.exists_sigma_of_correctedResiduals
      (K₁ := ULift.{max u₁ u₂ u₃ u₄, u₁} K₁) (K₁' := ULift.{max u₁ u₂ u₃ u₄, u₃} K₁')
      (K₂ := ULift.{max u₁ u₂ u₃ u₄, u₂} K₂) (K₂' := ULift.{max u₁ u₂ u₃ u₄, u₄} K₂')
      (NK.UniverseUnify.transportGalEquiv ϕ) he' a b 2 hres hcheb
  -- ## descend the `∃!` to the original universes
  exact NK.UniverseUnify.existsUnique_ulift_mp ϕ
    ⟨σ, hσ, fun y hy =>
      Submission.NeukirchUchida.unique_sigma (NK.UniverseUnify.transportGalEquiv ϕ) he' hy hσ⟩

/-- **The Neukirch–Uchida capstone from the four inputs of the second wall.**

See the docstring of `neukirch_uchida_of_chaptersV2_aux`, which is this statement with its four
universe parameters named. -/
theorem neukirch_uchida_of_chaptersV2 : NK.NUV2.Capstone :=
  neukirch_uchida_of_chaptersV2_aux

end NK.NUV2
