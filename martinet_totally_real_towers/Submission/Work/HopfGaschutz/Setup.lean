import Submission.Work.ConCohomology.All
import Submission.Work.RelatorRank.CohomologyH2
import Submission.Work.ShafarevichKoch.freeGroup_twoCocycle_is_coboundary
import Submission.Work.HopfGaschutz.Defs

/-!
# `Work.HopfGaschutz.Setup` -- the extension `1 → K → FreeGroup α → Q → 1` and its transgression

This module fixes the vocabulary in which the *cohomological* half of the relation-rank dictionary
is proved: given a (surjective) generating family `gen : α → Q` of a topological group `Q`, the
presentation map `FreeGroup.lift gen : FreeGroup α →* Q` is a group extension with kernel
`presKernel gen`, and the transgression of a `1`-cocycle on the kernel is a `2`-cocycle on `Q`
(`isCocycle2_tgCochainOf`), hence a class in `H²(Q, 𝔽₂)` (`tgClass`).

Everything here is in the *continuous* cohomology of `ConCohomology`, with the free group
`FreeGroup α` carrying the **discrete** topology (so that every cochain on it is locally constant)
and the finite group `Q` carrying the **discrete** topology (so that a section of `lift gen` is
continuous).  See `README.md` §7 for why the discrete topology on the free factor is exactly the
classical `cd(F) = 1` input, and `Profinite.lean` for the profinite gap.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.HopfGaschutz

open Work.ConCohomology

/-- The **trivial** action of a group on `𝔽₂ = ℤ/2`, registered as a global instance of this
chapter so that every consumer can write `H²(Γ, 𝔽₂)` (`Work.RelatorRank.contH2 Γ`) without
repeating the `letI` of `Work.RelatorRank.CohomologyH2`. -/
instance instTrivialActionF2 (Γ : Type*) [Group Γ] : DistribMulAction Γ (ZMod 2) :=
  Work.RelatorRank.f2TrivialAction Γ

/-- With the trivial action, `𝔽₂` is a discrete `Γ`-module (every stabiliser is open, indeed all of
`Γ`). -/
instance instIsDiscreteGModuleF2 (Γ : Type*) [Group Γ] [TopologicalSpace Γ] :
    IsDiscreteGModule Γ (ZMod 2) :=
  Work.RelatorRank.f2Discrete Γ

variable {α : Type*}

/-- The kernel of the presentation map `FreeGroup α →* Q` induced by a generating family
`gen : α → Q`: the group of relations of the presentation. -/
def presKernel {Q : Type*} [Group Q] (gen : α → Q) : Subgroup (FreeGroup α) :=
  MonoidHom.ker (FreeGroup.lift gen)

@[simp] lemma mem_presKernel {Q : Type*} [Group Q] (gen : α → Q) {x : FreeGroup α} :
    x ∈ presKernel gen ↔ FreeGroup.lift gen x = 1 := Iff.rfl

instance presKernel_normal {Q : Type*} [Group Q] (gen : α → Q) : (presKernel gen).Normal :=
  MonoidHom.normal_ker (FreeGroup.lift gen)

section Pres

variable {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
variable [TopologicalSpace (FreeGroup α)] [DiscreteTopology (FreeGroup α)]
variable (gen : α → Q)

/-- The extension `1 → K → FreeGroup α → Q → 1` attached to a surjective `gen`. -/
@[reducible] noncomputable def presExt :
    GroupExt (FreeGroup α) Q (presKernel gen) where
  q := FreeGroup.lift gen
  i := (presKernel gen).subtype
  ker_eq := fun g => ⟨fun h => ⟨⟨g, h⟩, rfl⟩, by rintro ⟨n, rfl⟩; exact n.2⟩
  injective_i := fun _ _ h => Subtype.ext h

/-- A section of the presentation map `FreeGroup.lift gen`, for a *generating* family `gen`: the
choice of an element of `FreeGroup α` mapping to `y`, for each `y : Q`.

Note that the hypothesis is that `gen` *generates* `Q` (its range has closure `⊤`), not that `gen`
is surjective: on the finite quotients that matter for this chapter a generating family of five
elements is of course never surjective, whereas `FreeGroup.lift gen` is surjective as soon as `gen`
generates, by `FreeGroup.lift_surjective_iff_closure_range_eq_top`. -/
noncomputable def presSection (hgen : Subgroup.closure (Set.range gen) = ⊤) : Q → FreeGroup α :=
  fun y => ((FreeGroup.lift_surjective_iff_closure_range_eq_top).mpr hgen y).choose

lemma presSection_spec (hgen : Subgroup.closure (Set.range gen) = ⊤) (y : Q) :
    FreeGroup.lift gen (presSection gen hgen y) = y :=
  ((FreeGroup.lift_surjective_iff_closure_range_eq_top).mpr hgen y).choose_spec

/-- The raw transgression cochain of a `1`-cochain on the relation kernel. -/
noncomputable def tgCochainOf [DiscreteTopology Q]
    (hgen : Subgroup.closure (Set.range gen) = ⊤) (φ : Cochain1 ↥(presKernel gen) (ZMod 2)) :
    Cochain2 Q (ZMod 2) :=
  tgCochain (presExt gen) (presSection gen hgen) (presSection_spec gen hgen)
    continuous_of_discreteTopology continuous_of_discreteTopology φ

/-- The invariance of a `1`-cocycle on the relation kernel `K` under the conjugation action of the
free group `F = FreeGroup α` (the action of `F/K = Q` on `H¹(K,𝔽₂)`). -/
def IsConjInvariant (φ : Z1 ↥(presKernel gen) (ZMod 2)) : Prop :=
  ∀ (g : FreeGroup α) (n : ↥(presKernel gen)),
    (φ : ↥(presKernel gen) → ZMod 2) ((presExt gen).conj g n)
      = (φ : ↥(presKernel gen) → ZMod 2) n

/-- **The transgression of an invariant `1`-cocycle on `K` is a `2`-cocycle on `Q`.** -/
theorem isCocycle2_tgCochainOf [DiscreteTopology Q]
    (hgen : Subgroup.closure (Set.range gen) = ⊤) {φ : Z1 ↥(presKernel gen) (ZMod 2)}
    (hφ : IsConjInvariant gen φ) :
    IsCocycle2 ⇑(tgCochainOf gen hgen φ) := by
  have h := isCocycle2_tgFun (E := presExt gen) (hcompN := fun n m => rfl)
    (s := presSection gen hgen) (hs := presSection_spec gen hgen) (hcompQ := fun y m => rfl)
    (φ := (φ : ↥(presKernel gen) → ZMod 2)) (mem_Z1.mp φ.2) (fun g n => hφ g n)
  simpa [tgCochainOf, tgCochain_coe] using h

/-- The transgression of an invariant `1`-cocycle on `K`, as a class in `H²(Q,𝔽₂)`. -/
noncomputable def tgClass [DiscreteTopology Q]
    (hgen : Subgroup.closure (Set.range gen) = ⊤) (φ : Z1 ↥(presKernel gen) (ZMod 2))
    (hφ : IsConjInvariant gen φ) : Work.RelatorRank.contH2 Q :=
  H2.mk ⟨tgCochainOf gen hgen φ, mem_Z2.mpr (isCocycle2_tgCochainOf gen hgen hφ)⟩

lemma tgCochainOf_add [DiscreteTopology Q]
    (hgen : Subgroup.closure (Set.range gen) = ⊤) (φ ψ : Cochain1 ↥(presKernel gen) (ZMod 2)) :
    tgCochainOf gen hgen (φ + ψ) = tgCochainOf gen hgen φ + tgCochainOf gen hgen ψ := by
  ext p
  simp [tgCochainOf, Pi.add_apply]

end Pres

end Work.HopfGaschutz
