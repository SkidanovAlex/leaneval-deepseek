import Mathlib
import Submission.Work.Serre.relCohPreimageDefs
import Submission.Work.Serre.C1Cyl
import Submission.Work.Thom.Cohomology
import Submission.Work.Cohomology.cohomologicalExcision
import Submission.Work.Serre.relCohTripleIsoOfVanishing
import Submission.Work.Serre.relCohPreimageAux
import Submission.Work.Serre.TripleCohLES
import Submission.Work.Serre.DiscPair.subsingleton_relCoh_cylPre
import Submission.Work.Serre.DiscPair.isIso_relCohMap_incl_of_isZero
import Submission.Work.Serre.DiscPair.relCoh_cylBot_trimming

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The bottom copy of the mapping cylinder over `V`, relative to the one over `S`

This file proves `Work.Serre.DiscPair.subsingleton_relCoh_cylBot_pair`: for `S ⊆ V ⊆ B` and
`q : C(X,B)`, if both pairs `(V,S)` and `(cylPre q V, cylBot q ∪ cylPre q S)` have vanishing
rational relative cohomology in all degrees `≤ N+2`, then the pair

  `(cylPre q V ∩ cylBot q, cylPre q V ∩ cylBot q ∩ cylPre q S)`

of the *bottom copy* of the mapping cylinder has vanishing rational relative cohomology in all
degrees `≤ N+1`.

The proof is a three-step reduction.

* `subsingleton_relCoh_cylPre` turns `hvanV` into the vanishing of `H^n(P, Q)`, where
  `P = cylPre q V` and `Q = cylPre q S`;
* the long exact sequence of the triple `Q ⊆ R ⊆ P`, where `R = (cylBot q ∩ P) ∪ Q` is the
  relative set of `hvanX`, then gives the vanishing of `H^n(R, R ∩ Q)` from `hvanX` in degrees
  `n` and `n+1` (this is `subsingleton_relCoh_cylBot_union` below);
* the "trimming" isomorphism `H^n(R, R ∩ Q) ≅ H^n(cylBot q ∩ P, cylBot q ∩ P ∩ Q)`
  (`Work.Serre.DiscPair.relCoh_cylBot_trimming`, the collar excision plus the collar shrink)
  transports it to the pair of the bottom copy.
-/

namespace Work.Serre.DiscPair

noncomputable section

set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

/-- **The long exact sequence of the triple `Q ⊆ R ⊆ P`.**  With `P = cylPre q V`,
`Q = cylPre q S` and `R = (cylBot q ∩ P) ∪ Q`, the restriction
`H^n(P,Q) → H^n(R, R ∩ Q)` is an isomorphism as soon as the relative cohomology of the larger
pair `(P,R)` vanishes in degrees `n` and `n+1`.  (This is
`Work.Serre.DiscPair.isIso_relCohMap_incl_of_isZero` at the triple `Q ⊆ R ⊆ P`.)

Here we record the consequence needed below: `H^n(P,Q) = 0` and `H^{n+1}(P,R) = 0` imply
`H^n(R, R ∩ Q) = 0`. -/
theorem subsingleton_relCoh_cylBot_union {B : Type} [TopologicalSpace B] {X : Type}
    [TopologicalSpace X] (q : C(X, B)) (S V : Set B) (hSV : S ⊆ V) (N : ℕ)
    (hvanV : ∀ j : ℕ, j ≤ N + 2 →
      CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ j ↥V {x : ↥V | (x : B) ∈ S}))
    (hvanX : ∀ j : ℕ, j ≤ N + 2 →
      CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ j ↥(Work.Serre.cylPre q V)
        {x : ↥(Work.Serre.cylPre q V) | (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
          (x : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}))
    (n : ℕ) (hn : n ≤ N + 1) :
    Subsingleton (Work.Thom.RelCoh ℚ n
      ↥{x : ↥(Work.Serre.cylPre q V) | (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
          (x : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}
      {y : ↥{x : ↥(Work.Serre.cylPre q V) | (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
          (x : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S} |
        ((y : ↥(Work.Serre.cylPre q V)) : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}) := by
  haveI hQ : Subsingleton (Work.Thom.RelCoh ℚ n ↥(Work.Serre.cylPre q V)
      {x : ↥(Work.Serre.cylPre q V) | (x : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}) :=
    subsingleton_relCoh_cylPre q S V hSV N hvanV n (by omega)
  let φ : Work.Thom.RelCoh ℚ n ↥(Work.Serre.cylPre q V)
        {x : ↥(Work.Serre.cylPre q V) | (x : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}
      ⟶ Work.Thom.RelCoh ℚ n
        ↥{x : ↥(Work.Serre.cylPre q V) | (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
            (x : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}
        {y : ↥{x : ↥(Work.Serre.cylPre q V) | (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
            (x : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S} |
          ((y : ↥(Work.Serre.cylPre q V)) : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S} :=
    Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥{x : ↥(Work.Serre.cylPre q V) |
            (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
              (x : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S},
          TopCat.of ↥(Work.Serre.cylPre q V)))
      {y : ↥{x : ↥(Work.Serre.cylPre q V) | (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
          (x : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S} |
        ((y : ↥(Work.Serre.cylPre q V)) : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}
      {x : ↥(Work.Serre.cylPre q V) | (x : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}
      (fun y hy => hy) ℚ n
  haveI : IsIso φ :=
    isIso_relCohMap_incl_of_isZero (TopCat.of ↥(Work.Serre.cylPre q V))
      {x : ↥(Work.Serre.cylPre q V) | (x : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}
      {x : ↥(Work.Serre.cylPre q V) | (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
        (x : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}
      (fun x hx => Or.inr hx) n (hvanX n (by omega)) (hvanX (n + 1) (by omega))
  exact ⟨fun a b => (asIso φ).toLinearEquiv.symm.injective (Subsingleton.elim _ _)⟩

/-- **The bottom copy of the mapping cylinder over `V`, relative to the one over `S`.** -/
theorem subsingleton_relCoh_cylBot_pair {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (S V : Set B) (hSV : S ⊆ V) (N : ℕ)
    (hvanV : ∀ j : ℕ, j ≤ N + 2 →
      CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ j ↥V {x : ↥V | (x : B) ∈ S}))
    (hvanX : ∀ j : ℕ, j ≤ N + 2 →
      CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ j ↥(Work.Serre.cylPre q V)
        {x : ↥(Work.Serre.cylPre q V) | (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
          (x : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}))
    (n : ℕ) (hn : n ≤ N + 1) :
    Subsingleton (Work.Thom.RelCoh ℚ n
      ↥{x : ↥(Work.Serre.cylPre q V) | (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q}
      {y : ↥{x : ↥(Work.Serre.cylPre q V) | (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q} |
        ((y : ↥(Work.Serre.cylPre q V)) : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}) := by
  have hR : Subsingleton (Work.Thom.RelCoh ℚ n
      ↥{x : ↥(Work.Serre.cylPre q V) | (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
          (x : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}
      {y : ↥{x : ↥(Work.Serre.cylPre q V) | (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
          (x : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S} |
        ((y : ↥(Work.Serre.cylPre q V)) : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}) :=
    subsingleton_relCoh_cylBot_union q S V hSV N hvanV hvanX n hn
  obtain ⟨e⟩ := relCoh_cylBot_trimming q S V hSV n
  exact ⟨fun a b => e.toLinearEquiv.symm.injective (Subsingleton.elim _ _)⟩

end

end Work.Serre.DiscPair
