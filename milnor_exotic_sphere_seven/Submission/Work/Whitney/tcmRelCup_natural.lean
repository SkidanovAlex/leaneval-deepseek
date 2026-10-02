import Mathlib
import Submission.Work.Whitney.TCMDefs
import Submission.Work.Whitney.RelRelCupNat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

/-!
# Naturality of the canonical relative–relative cup `Work.Whitney.tcmRelCup`

`Work.Whitney.tcmRelCup` (`Submission/Work/Whitney/TCMDefs.lean`) is the *canonical*
relative–relative cup product `H^m(X,A) → H^n(X,B) → H^{m+n}(X,A∪B)` for open `A B ⊆ X`: the
Alexander–Whitney product `Work.Whitney.relRelCupHMap` on the `A+B` complex `C^*(X,A) ∩ C^*(X,B)`,
transported to `H^*(X,A∪B)` along the inverse of the quasi-isomorphism
`C^*(X,A∪B) → C^*(X,A+B)` (`Work.Whitney.tcmRelCupInv`).

The Whitney area already owns the naturality of this construction under a continuous map of pairs,
for the *same* transport: `Work.Whitney.relRelCupOpen_natural`
(`Submission/Work/Whitney/RelRelCupNat.lean`, a file with no unfinished proofs, and with no
statement in common with the still-open top-class module `Work.Whitney.chernClass_whitneySum_top`).  The two operations are
pointwise the same — `Work.Whitney.tcmRelCup` and `Work.Whitney.relRelCupOpen` differ only in that
the transport `Work.Whitney.tcmRelCupInv` of `TCMDefs.lean` and the transport
`Work.Whitney.pdABInvTransport` of `RelRelCupNat.lean` are two copies of the inverse of the *same*
map `H^{m+n}(X,A∪B) → H^{m+n}(X,A+B)`, hence definitionally equal — so naturality transfers:

`f^* (a ⌣ b) = f^* a ⌣ f^* b`, for `f : C(X',X)` with `f '' A' ⊆ A` and `f '' B' ⊆ B`.

This is the form of naturality needed to restrict the canonical cup to the charts of a bundle
(`Work.Whitney.tcmModelMul` / `Work.Whitney.topClassMul`).
-/

namespace Work.Whitney

/-- **`Work.Whitney.tcmRelCup` is the canonical relative–relative cup
`Work.Whitney.relRelCupOpen`**: both are the Alexander–Whitney product `Work.Whitney.relRelCupHMap`
transported along the inverse of the quasi-isomorphism `C^*(X,A∪B) → C^*(X,A+B)`, and the two
transports (`tcmRelCupInv` and `pdABInvTransport`) are the same map, unfolding to the same
`CategoryTheory.inv` of the same homology isomorphism. -/
lemma tcmRelCup_eq_relRelCupOpen {R : Type} [CommRing R] {X : Type} [TopologicalSpace X]
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (m n : ℕ)
    (a : Work.Thom.RelCoh R m X A) (b : Work.Thom.RelCoh R n X B) :
    tcmRelCup A B hA hB m n a b = relRelCupOpen A B hA hB m n a b := by
  rw [tcmRelCup, tcmRelCupG_apply, relRelCupOpen_apply, relRelCupG_apply]
  rfl

theorem tcmRelCup_natural (R : Type) [CommRing R] {X' X : Type} [TopologicalSpace X']
    [TopologicalSpace X] (f : C(X', X)) (A B : Set X) (A' B' : Set X')
    (hA : IsOpen A) (hB : IsOpen B) (hA' : IsOpen A') (hB' : IsOpen B')
    (hmA : ∀ x ∈ A', f x ∈ A) (hmB : ∀ x ∈ B', f x ∈ B)
    (hmU : ∀ x ∈ A' ∪ B', f x ∈ A ∪ B)
    (m n : ℕ) (a : Work.Thom.RelCoh R m X A) (b : Work.Thom.RelCoh R n X B) :
    (Work.Thom.relCohMap f (A' ∪ B') (A ∪ B) hmU R (m + n)).hom
        (Work.Whitney.tcmRelCup A B hA hB m n a b)
      = Work.Whitney.tcmRelCup A' B' hA' hB' m n
          ((Work.Thom.relCohMap f A' A hmA R m).hom a)
          ((Work.Thom.relCohMap f B' B hmB R n).hom b) := by
  simpa only [tcmRelCup_eq_relRelCupOpen] using
    relRelCupOpen_natural f A B A' B' hA hB hA' hB' hmA hmB hmU m n a b

end Work.Whitney
