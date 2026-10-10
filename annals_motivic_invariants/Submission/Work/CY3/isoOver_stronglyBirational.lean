import Mathlib
import Submission.Work.CY3.Defs
import Submission.Work.LLink.cInv_eq_zero_of_isPseudoIso

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CY3

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {𝕜 : Type} [Field 𝕜] {X Y : Scheme.{0}} [Variety 𝕜 X] [Variety 𝕜 Y]

/-- An isomorphism `e : X ≅ Y` over `Spec 𝕜`, viewed as a partial isomorphism defined on all of
`X` and all of `Y` (`PartialIso.ofIso`), is a partial isomorphism over `Spec 𝕜`: the two
structure morphisms `X ↘ Spec 𝕜` and `Y ↘ Spec 𝕜` cancel against the trivialisations
`X.topIso`, `Y.topIso`. -/
lemma partialIsoOfIso_isOver (e : X ≅ Y) (he : e.hom.IsOver (Spec (.of 𝕜))) :
    (PartialIso.ofIso e).IsOver (X ↘ (Spec (.of 𝕜))) (Y ↘ (Spec (.of 𝕜))) := by
  unfold PartialIso.ofIso
  rw [PartialIso.IsOver]
  simp only [Iso.trans_hom, Iso.symm_hom, Scheme.topIso_hom, Category.assoc]
  rw [← Category.assoc (Y.topIso.inv) ((⊤ : Y.Opens).ι) (Y ↘ (Spec (.of 𝕜))),
    Scheme.toIso_inv_ι, Category.id_comp]
  have h := (Hom.isOver_iff (Spec (.of 𝕜)) (f := e.hom)).mp he
  rw [h]

/-- The partial isomorphism attached to an isomorphism `e : X ≅ Y` (`PartialIso.ofIso e`, with
source and target both `⊤`) is a pseudo-isomorphism: every point of coheight one lies in the
source and in the target, because both are everything. -/
lemma partialIsoOfIso_isPseudoIso (e : X ≅ Y) : (PartialIso.ofIso e).IsPseudoIso := by
  constructor <;> intro p hp <;> exact absurd hp (by simp [PartialIso.ofIso])

/-- **Isomorphisms over `𝕜` are strong birationalities.**  An isomorphism `e : X ≅ Y` compatible
with the structure morphisms to `Spec 𝕜` gives a birational map `X ⤏ Y` over `𝕜` all of whose
invariant coefficients vanish (`Work.CY3.StronglyBirational 𝕜 X Y`, i.e. the paper's `c(γ) = 0`).
Route: the partial isomorphism with source and target `⊤` built from `e` represents it, is a
pseudo-isomorphism (`PartialIso.IsPseudoIso`, vacuous for source `⊤`), and
`Work.LLink.cInv_eq_zero_of_isPseudoIso` gives the vanishing coefficients; `IsOver` comes from
`Work.Motivic.pseudoReg_isOver_toBirationalMap` / the `IsOver` API of `PartialMap`.) -/
theorem isoOver_stronglyBirational {𝕜 : Type} [Field 𝕜]
    {X Y : AlgebraicGeometry.Scheme.{0}} [MotivicInvariants.Variety 𝕜 X]
    [MotivicInvariants.Variety 𝕜 Y] (h : Work.CY3.IsoOver 𝕜 X Y) :
    Work.CY3.StronglyBirational 𝕜 X Y := by
  obtain ⟨e, he⟩ := h
  refine ⟨(PartialIso.ofIso e).toBirationalMap, ?_, ?_⟩
  · exact Work.Motivic.pseudoReg_isOver_toBirationalMap (PartialIso.ofIso e)
      (partialIsoOfIso_isOver e he)
  · intro W _ w
    exact Work.LLink.cInv_eq_zero_of_isPseudoIso 𝕜 w (PartialIso.ofIso e)
      (partialIsoOfIso_isPseudoIso e)

end Work.CY3
