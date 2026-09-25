import Mathlib
import Submission.Work.ProPDeficiency.Basic

/-!
# Burnside's basis theorem: generating modulo the Frattini subgroup

**Namespace** `Work.ProPDeficiency`; module `Submission.Work.ProPDeficiency.FrattiniGenerators`.

The *Frattini non-generator property*: a subset `S` of a finite group generates `G` if and only if
its image generates `G ⧸ Φ(G)`.  Since `S` generates `G` modulo `Φ(G)` exactly when
`⟨S⟩ ⊔ Φ(G) = ⊤`, this is the statement

`IsGeneratingSet S ↔ Subgroup.closure (S : Set G) ⊔ frattini G = ⊤`

proved from Mathlib's `frattini_nongenerating`; in combination with
`dGens_eq_log_card_frattini` (the counting form of Burnside's basis theorem, module
`Submission.Work.ProPDeficiency.dGens_eq_log_card_frattini`) this is the `dGens = dim_{𝔽_p} G/Φ(G)`
identity of the chapter: the image of `S` generates the elementary abelian quotient iff `S`
generates.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ProPDeficiency

/-- **Frattini non-generator property.**  For a finite group `G` and a finset `S`, `S` generates `G`
iff `S` generates `G` modulo `Φ(G)`, i.e. iff `⟨S⟩ ⊔ Φ(G) = ⊤`.  The latter is exactly the
statement that the image of `S` generates `G ⧸ Φ(G)`. -/
theorem isGeneratingSet_iff_sup_frattini_eq_top {G : Type*} [Group G] [Finite G] (S : Finset G) :
    IsGeneratingSet S ↔ Subgroup.closure (S : Set G) ⊔ frattini G = ⊤ := by
  constructor
  · intro h
    rw [h, top_sup_eq]
  · intro h
    exact frattini_nongenerating h

/-- The "if" direction alone, in the form used when lifting generators of `G ⧸ Φ(G)` to `G`. -/
theorem isGeneratingSet_of_sup_frattini_eq_top {G : Type*} [Group G] [Finite G] (S : Finset G)
    (h : Subgroup.closure (S : Set G) ⊔ frattini G = ⊤) : IsGeneratingSet S :=
  frattini_nongenerating h

/-- **`dGens` is insensitive to the Frattini subgroup**: for a finite group, a generating set of
`G` has the same size as a generating set of `G ⧸ Φ(G)`, so
`dGens G ≤ #S` for a generating set `S` of `G ⧸ Φ(G)` lifted to `G`.  This is the precise sense in
which `dGens` is the dimension of the elementary abelian quotient. -/
theorem dGens_le_card_of_closure_sup_frattini {G : Type*} [Group G] [Finite G] (S : Finset G)
    (h : Subgroup.closure (S : Set G) ⊔ frattini G = ⊤) : dGens G ≤ S.card :=
  dGens_le_card (isGeneratingSet_of_sup_frattini_eq_top S h)

end Work.ProPDeficiency
