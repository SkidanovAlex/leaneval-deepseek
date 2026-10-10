import Submission.Work.K3.BaseChangeBirational
import Submission.Work.K3.partialIso_baseChangeAlong
import Submission.Work.Motivic.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3.isIsoAt_baseChangeAlong` — isomorphism points base change

`Work.K3.Motivic.IsIsoAt ψ x` says that the birational map `ψ` is an isomorphism at `x`, i.e. that
some partial isomorphism representing `ψ` has `x` in its source.  This file proves the *easy*
direction of the base-change behaviour of isomorphism points, which is the half of the `exDiv`
analysis needed in the descent step of `thm:K3` (see `NOTES.md` §6(c), step 3):

> if `x` is an isomorphism point of `ψ`, then every point `p` of the base change of `X` over `x`
> is an isomorphism point of any base change `Ψ` of `ψ`.

The other half (`x ∈ exDiv ψ ⟹ x_𝕜 ∈ exDiv Ψ`, i.e. *non*-isomorphism points base change) is the
`⊇` direction discussed in `NOTES.md` and is reduced there to the base-change stability of
injectivity, not to a general descent theory of isomorphism points.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.K3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants

variable {S T X Y : Scheme.{0}} (f : T ⟶ S) [X.Over S] [Y.Over S] [Surjective f]
  [UniversallyOpen f] [IrreducibleSpace X] [IrreducibleSpace Y]
  [IrreducibleSpace (baseChangeAlong f X)] [IrreducibleSpace (baseChangeAlong f Y)]

/-- **Isomorphism points base change.**  Let `i` be a partial isomorphism representing the
birational map `ψ`, let `x ∈ i.source`, and let `p` be a point of `X ×_S T` above `x`.  Then `p` is
an isomorphism point of any base change `Ψ` of `ψ` (i.e. of any `Ψ` whose forward rational map is
the base change of the rational map of `ψ`). -/
theorem isIsoAt_baseChangeAlong {ψ : X.BirationalMap Y}
    (Ψ : (baseChangeAlong f X).BirationalMap (baseChangeAlong f Y))
    (hΨ : ∀ (g : X.PartialMap Y) [g.IsOver S], g.toRationalMap = ψ.hom →
      (PartialMap.baseChangeAlong f g).toRationalMap = Ψ.hom)
    (i : X.PartialIso Y) (hi : i.toRationalMap = ψ.hom) (hg : i.toPartialMap.IsOver S) {x : X}
    (hx : x ∈ i.source) (p : baseChangeAlong f X) (hp : baseChangeAlongProj f X p = x) :
    IsIsoAt Ψ p := by
  obtain ⟨h, hsrc, -, hrat⟩ := partialIso_baseChangeAlong f i hg
  have hmem : p ∈ h.source := by
    rw [hsrc, Hom.mem_preimage, hp]
    exact hx
  exact ⟨h, hmem, by rw [hrat, hΨ i.toPartialMap hi]⟩

end Work.K3

namespace Work.K3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants

/-- **An isomorphism point has an injective representative.**  If `ψ` is an isomorphism at `x`, then
some partial map `g` representing `ψ`, defined at `x`, is injective (indeed its underlying morphism
is the composite of an isomorphism of schemes with an open immersion).

This is the *contrapositive* form in which the non-isomorphism of the link at its exceptional
divisor is used in the descent (`NOTES.md` §6(c), step 3): if every representative of `ψ` defined at
`x` fails to be injective — e.g. because the geometric map `ψ_ℂ` is not injective near `x_ℂ`, a
statement stable under base change — then `x` is not an isomorphism point. -/
theorem IsIsoAt.exists_injective_representative {X Y : Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] {ψ : X.BirationalMap Y} {x : X} (h : IsIsoAt ψ x) :
    ∃ (g : X.PartialMap Y), x ∈ g.domain ∧ g.toRationalMap = ψ.hom ∧ Function.Injective g.hom := by
  obtain ⟨i, hx, hi⟩ := h
  refine ⟨i.toPartialMap, hx, hi, ?_⟩
  have hhom : i.toPartialMap.hom = i.iso.hom ≫ i.target.ι := PartialIso.toPartialMap_hom i
  rw [hhom]
  -- the underlying morphism is a composite of open immersions (an isomorphism of schemes is an
  -- open immersion), hence an open embedding, hence injective
  exact (i.iso.hom ≫ i.target.ι).isOpenEmbedding.injective

end Work.K3
