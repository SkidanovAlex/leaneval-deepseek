import Mathlib
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.Defs
import Submission.Work.StemsB.Fibrations
import Submission.Work.Thom.Cohomology

/-!
# The conclusion of the CW-model Thom case, as a predicate

`Work.Serre.ThomCylAt r N q` is the conclusion of `Work.Serre.cwModelThomCase` at a fixed
fibration `q : C(X,Γ)`: the pair `(cyl q, range (cylIncl q))` of the mapping cylinder carries a
relative class `U ∈ H^{r+1}` whose *mixed* cup product with the pullback along the retraction
`cylRetract q` is an isomorphism in the range `m + r + 1 ≤ N + 1`.

The definitions live in this separate module so that the lemmas proved about `ThomCylAt` elsewhere
(`Submission/Work/Serre/thomCylAt_of_homeo.lean`, the tower induction) can be imported by
`Submission/Work/Serre/cwModelThomCase.lean` without a circular import.
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- **The conclusion of the CW-model Thom case**, as a predicate of a fibration `q : C(X,Γ)`:
there is a relative class `U ∈ H^{r+1}(cyl q, range (cylIncl q); ℚ)` whose mixed cup product with
the pullback along the retraction `cylRetract q` is an isomorphism in the range
`m + r + 1 ≤ N + 1`. -/
def ThomCylAt (r N : ℕ) {Γ : Type} [TopologicalSpace Γ] {X : Type} [TopologicalSpace X]
    (q : C(X, Γ)) : Prop :=
  ∃ U : Work.Thom.RelCoh ℚ (r + 1) (cyl q) (Set.range (cylIncl q)),
    ∀ m : ℕ, m + r + 1 ≤ N + 1 → CategoryTheory.IsIso (ModuleCat.ofHom
      (((Work.Thom.mixedCupC ℚ (Set.range (cylIncl q)) m (r + 1))).flip U ∘ₗ
        (Work.Thom.CohMap (cylRetract q) ℚ m).hom))

/-- The restriction of a fibration `q : C(X,Γ)` to the preimage of a subset `S ⊆ Γ`. -/
def restrictFibre {Γ : Type} [TopologicalSpace Γ] {X : Type} [TopologicalSpace X]
    (q : C(X, Γ)) (S : Set Γ) : C(↥(q ⁻¹' S), ↥S) where
  toFun x := ⟨q x.1, x.2⟩
  continuous_toFun :=
    Continuous.subtype_mk (q.continuous.comp continuous_subtype_val) (fun x => x.2)

end

end Work.Serre
