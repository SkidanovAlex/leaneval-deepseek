import Mathlib
import Submission.Work.Serre.E3aDefs
import Submission.Work.StemsB.RelChainsR
import Submission.Work.StemsB.Fibrations

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `E3(a)`: the vocabulary of the cellular inductive step

The cellular proof of `Work.Serre.SerreE3a` runs over a tower
`Γ₀ ⊆ Γ₁ ⊆ ⋯ ⊆ Γ_M = Γ` of cell attachments and a Serre fibration `p : E → B`, and compares the
absolute rational homology of the "preimage stages" `X_k = (pullbackFst g_k p)⁻¹(Γ_k) ⊆ Γ_k ×_B E`
with that of the base stages `Γ_k`.

This file contains only the two definitions of that comparison:

* `Work.Serre.E3aStep.AbsGoodQ p r g` — the **invariant**: for the stage `Γ` with structure map
  `g : Γ → B`, the projection `pullbackFst g p : Γ ×_B E → Γ` is a rational homology isomorphism in
  degrees `< r` and an epimorphism in degree `r`;
* `Work.Serre.E3aStep.stepMapQ p incl g'` — the **step map** of an inclusion of stages
  `incl : Γ → Γ'` with structure maps `g`, `g'`: the induced map of relative chain complexes
  `C_*(Γ' ×_B E, X) → C_*(Γ', Γ)`, where `X = (pullbackFst g' p)⁻¹(Set.range incl)`.

Both are `sorry`-free (they are definitions), so that lemmas proved against them do not inherit
`sorryAx`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.E3aStep

noncomputable section

/-- **The invariant of the cellular induction.**  For a Serre fibration `p : E → B` and a stage
`g : Γ → B` of a cellular model of `B`, the projection `pullbackFst g p` of the pullback
`Γ ×_B E` onto `Γ` induces an isomorphism on rational homology in degrees `< r` and an epimorphism
in degree `r`.

The range `r` is a parameter: the induction of `Work.Serre.E3aStep.propagateAbsQ` keeps it fixed,
and it is chosen at the end to be the range in which the fibres of `p` are rationally acyclic. -/
def AbsGoodQ {B E : Type} [TopologicalSpace B] [TopologicalSpace E] (p : C(E, B)) (r : ℕ)
    {Γ : Type} [TopologicalSpace Γ] (g : C(Γ, B)) : Prop :=
  (∀ i : ℕ, i < r → IsIso (Work.Serre.ratHomologyMap (Work.StemsB.pullbackFst g p) i)) ∧
    Epi (Work.Serre.ratHomologyMap (Work.StemsB.pullbackFst g p) r)

/-- The restriction of `pullbackFst g' p` to the preimage of the range of `incl`, as a map onto
`Set.range incl`. -/
def stepRestrict {B E Γ Γ' : Type} [TopologicalSpace B] [TopologicalSpace E]
    [TopologicalSpace Γ] [TopologicalSpace Γ'] (p : C(E, B)) (incl : C(Γ, Γ')) (g' : C(Γ', B)) :
    TopCat.of {x : Work.StemsB.Pullback g' p |
        (Work.StemsB.pullbackFst g' p) x ∈ Set.range incl} ⟶
      TopCat.of (Set.range incl) :=
  TopCat.ofHom ⟨fun x => ⟨Work.StemsB.pullbackFst g' p x.1, x.2⟩, by fun_prop⟩

/-- **The step map of the cellular induction**: the map of relative rational chain complexes
`C_*(Γ' ×_B E, (pullbackFst g' p)⁻¹(Γ)) ⟶ C_*(Γ', Γ)` induced by the projection of the pullback,
for the inclusion of stages `incl : Γ → Γ'`. -/
def stepMapQ {B E Γ Γ' : Type} [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace Γ]
    [TopologicalSpace Γ'] (p : C(E, B)) (incl : C(Γ, Γ')) (g' : C(Γ', B)) :
    Work.StemsB.relChainsR ℚ (TopCat.of (Work.StemsB.Pullback g' p))
        ((Work.StemsB.pullbackFst g' p) ⁻¹' (Set.range incl)) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of Γ') (Set.range incl) :=
  Work.Serre.relChainsRMapOf (TopCat.of (Work.StemsB.Pullback g' p)) (TopCat.of Γ')
    ((Work.StemsB.pullbackFst g' p) ⁻¹' (Set.range incl)) (Set.range incl)
    (TopCat.ofHom (Work.StemsB.pullbackFst g' p)) (stepRestrict p incl g')
    (by ext x; rfl)

end

end Work.Serre.E3aStep
