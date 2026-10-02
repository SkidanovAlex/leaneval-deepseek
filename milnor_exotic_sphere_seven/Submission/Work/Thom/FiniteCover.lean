import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

/-!
# Finite families of pieces: intersections and their basic inclusions

For an open family `U : Fin N → Set B` of pieces of a base, the *finite-cover* form of the Thom
isomorphism theorem (`Work.Thom.thomClass_of_finite_cover`) needs the intersections
`⋂_{k ∈ S} U k` of subfamilies and the inclusions between them.  This module fixes the notation
`Work.Thom.finInter U S` and provides the inclusions used by the statement:

* `finInter_mono` : `S ⊆ T ⟹ ⋂_{k∈T} U k ⊆ ⋂_{k∈S} U k` (the restriction direction);
* `finInter_singleton` : `⋂_{k ∈ {k}} U k = U k`;
* `finInter_nonempty_subset_iUnion` : a nonempty intersection is contained in the union.
-/

namespace Work.Thom

variable {B : Type} {N : ℕ}

/-- **The intersection of a finite subfamily** of the pieces `U : Fin N → Set B`. -/
def finInter (U : Fin N → Set B) (S : Finset (Fin N)) : Set B :=
  ⋂ k ∈ (S : Set (Fin N)), U k

theorem mem_finInter {U : Fin N → Set B} {S : Finset (Fin N)} {x : B} :
    x ∈ finInter U S ↔ ∀ k ∈ S, x ∈ U k := by
  simp [finInter]

/-- **The restriction direction**: a larger family of pieces has a smaller intersection. -/
theorem finInter_mono {U : Fin N → Set B} {S T : Finset (Fin N)} (h : S ⊆ T) :
    finInter U T ⊆ finInter U S :=
  Set.biInter_subset_biInter_left (s := (T : Set (Fin N))) (s' := (S : Set (Fin N)))
    (t := U) (by intro x hx; exact h hx)

@[simp] theorem finInter_singleton (U : Fin N → Set B) (k : Fin N) :
    finInter U {k} = U k := by
  ext x
  simp [finInter]

/-- A nonempty intersection is contained in the union of the pieces. -/
theorem finInter_nonempty_subset_iUnion {U : Fin N → Set B} {S : Finset (Fin N)}
    (hS : S.Nonempty) : finInter U S ⊆ Set.iUnion U :=
  (Set.biInter_subset_of_mem (s := (S : Set (Fin N))) (t := U) hS.choose_spec).trans
    (Set.subset_iUnion U _)

end Work.Thom
