/-
# The amalgam `K ∗_{⟨z ^ p⟩} ⟨z⟩` is the free group `F(RootIdx α t)`

This is the target lemma `Work.ORLocInd.CohenLyndon.rootAmaEquiv`: the amalgam
`Ama t p = rootK ∗_{rootC} rootZ` of the Karrass--Solitar descent (where
`rootK t p = (rootHom t p).range`, `rootZ t = ⟨z⟩` and `rootC t p = ⟨z ^ p⟩` inside the free group
`P = F(RootIdx α t)`) is isomorphic to `P` itself, via an isomorphism that restricts to the
vertex map `Ama.ofK` on `rootK` and to the edge map `Ama.base` on `rootC`.

The maps are those of `Submission/Work/ORLocInd/CohenLyndon/rootAmaDefs.lean`:
`rootIsoAmaFwd : P →* Ama t p` (sending the extra letter `z` to the `⟨z⟩`-vertex and each letter
`a ≠ t` to the `K`-vertex) and `rootIsoAmaBwd : Ama t p →* P` (the pushout universal property
applied to the two inclusions `rootK ↪ P`, `rootZ ↪ P`).  The two needed identities are
`rootAmaBwdComp` (delegated) and `rootIsoAmaFwd_comp_rootIsoAmaBwd` below.
-/
import Mathlib
import Submission.Work.ORLocInd.CohenLyndon.rootAmaSetup
import Submission.Work.ORLocInd.CohenLyndon.substDefs
import Submission.Work.ORLocInd.CohenLyndon.rootAmaDefs
import Submission.Work.ORLocInd.CohenLyndon.rootAmaSubZ
import Submission.Work.ORLocInd.CohenLyndon.rootAmaBwdComp

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORLocInd.CohenLyndon

/-- The forward map `rootIsoAmaFwd` is a left inverse of the backward map `rootIsoAmaBwd`: on the
amalgam, checking the two vertices `rootK` and `rootZ` (and the edge subgroup `rootC`) suffices. -/
theorem rootIsoAmaFwd_comp_rootIsoAmaBwd {α : Type u} [DecidableEq α] (t : α) (p : ℤ) :
    (rootIsoAmaFwd t p).comp (rootIsoAmaBwd t p) = MonoidHom.id (Ama t p) := by
  refine Monoid.PushoutI.hom_ext (φ := amaPhi t p) ?_ ?_
  · intro i
    cases i
    · rw [MonoidHom.comp_assoc, rootIsoAmaBwd_comp_ofK, rootIsoAmaFwd_subK, MonoidHom.id_comp]
    · rw [MonoidHom.comp_assoc, rootIsoAmaBwd_comp_ofZ, rootAmaSubZ, MonoidHom.id_comp]
  · rw [MonoidHom.comp_assoc, rootIsoAmaBwd_comp_base, rootIsoAmaFwd_subC, MonoidHom.id_comp]

/-- **The amalgam `rootK ∗_{rootC} rootZ` is the free group `F(RootIdx α t)`**, via an isomorphism
which is `Ama.ofK` on the `K`-vertex and `Ama.base` on the edge subgroup. -/
theorem rootAmaEquiv {α : Type u} [DecidableEq α] (t : α) (p : ℤ) :
    ∃ Φ : FreeGroup (RootIdx α t) ≃* Ama t p,
      (∀ (x : FreeGroup (RootIdx α t)) (hx : x ∈ rootK t p),
        Φ x = Ama.ofK t p ⟨x, hx⟩) ∧
      (∀ (x : FreeGroup (RootIdx α t)) (hx : x ∈ rootC t p),
        Φ x = Ama.base t p ⟨x, hx⟩) := by
  refine ⟨MonoidHom.toMulEquiv (rootIsoAmaFwd t p) (rootIsoAmaBwd t p)
    (rootAmaBwdComp t p) (rootIsoAmaFwd_comp_rootIsoAmaBwd t p), ?_, ?_⟩
  · intro x hx
    simpa using DFunLike.congr_fun (rootIsoAmaFwd_subK t p) ⟨x, hx⟩
  · intro x hx
    simpa using DFunLike.congr_fun (rootIsoAmaFwd_subC t p) ⟨x, hx⟩

end Work.ORLocInd.CohenLyndon
