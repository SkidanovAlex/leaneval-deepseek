import Mathlib
import Submission.Work.Spike.janiszewski_pointInter
import Submission.Work.BoxShrink.Pinch.UnicoherencePlane

/-!
# Borrowed reconstruction: unicoherence of the plane and the Phragmén–Brouwer property

**Ownership.**  This file is *not* part of the push-off chapter `Work.BoxShrink.Pinch` (it is not
imported by `All.lean` and is not covered by the chapter's axiom audit `Check.lean`).  It is a
reconstruction of a lost module of the **`Submission/Work/JordanSeparation/`** area, which imports
it in eight places; it lives in this directory only because that is where the lost module happened
to be.  It is kept here, with its original statements, so that those imports keep working.

**Status.**  All three declarations below are now **proved**; none carries a placeholder.
Of the three,

* `phragmenBrouwer_isClosed` is now **proved**, by citing the workspace's own proof of the closed
  Phragmén–Brouwer property, `Work.Spike.phragmen_brouwer_closed`;
* `isPreconnected_frontier_of_compl_preconnected` is now **proved** from
  `isPreconnected_inter_of_union_eq_univ` (unicoherence), by the standard derivation
  `frontier C = closure C ∩ Cᶜ`;
* `isPreconnected_inter_of_union_eq_univ` — **unicoherence of the plane** — is now **proved** too:
  it is `Work.BoxShrink.Pinch.UnicoherencePlane` of `UnicoherencePlane.lean`, proved in this
  directory from the workspace's Phragmén–Brouwer theorem for closed sets
  (`Work.Spike.phragmen_brouwer_closed`), the Brouwer property for closed preconnected plane sets,
  and Wilder's Theorem II 3.10 (`Work.BoxShrink.Pinch.BorsukAux.exists_preconnected_closure_inter`).

For the paper's challenge (`Work.BoxShrink.Pinch`), everything is in `All.lean`/`Check.lean` and
carries no placeholder proof; this file is fenced off from that audit.
-/

open Set

namespace Work.BoxShrink.Pinch

theorem isPreconnected_inter_of_union_eq_univ {P Q : Set ℂ}
    (hP : IsClosed P) (hQ : IsClosed Q) (hPp : IsPreconnected P) (hQp : IsPreconnected Q)
    (hcover : P ∪ Q = Set.univ) : IsPreconnected (P ∩ Q) :=
  Work.BoxShrink.Pinch.UnicoherencePlane hP hQ hPp hQp hcover

/-- **Phragmén–Brouwer for disjoint closed sets in the plane**: if `x` lies in the same connected
component of `Aᶜ` and of `Bᶜ` as a point of both, then it lies in the same connected component of
`(A ∪ B)ᶜ`.  This is the closed form of Phragmén–Brouwer, which the workspace proves in
`Work.Spike.phragmen_brouwer_closed`. -/
theorem phragmenBrouwer_isClosed {A B : Set ℂ} (hAc : IsClosed A) (hBc : IsClosed B)
    (hAB : Disjoint A B) {x : ℂ} (hx : x ∉ A ∪ B) :
    connectedComponentIn Aᶜ x ∩ connectedComponentIn Bᶜ x =
      connectedComponentIn (A ∪ B)ᶜ x :=
  Work.Spike.phragmen_brouwer_closed hAc hBc hAB hx

/-- **The frontier of a set whose complement is connected is preconnected.**  The derivation from
unicoherence: `frontier C = closure C ∩ Cᶜ`, and `closure C` and `Cᶜ` are closed preconnected sets
covering the plane, so their intersection — the frontier — is preconnected. -/
theorem isPreconnected_frontier_of_compl_preconnected {C : Set ℂ} (hC : IsOpen C)
    (hCp : IsPreconnected C) (hCc : IsPreconnected Cᶜ) :
    IsPreconnected (frontier C) := by
  have hcover : closure C ∪ Cᶜ = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr (fun x => ?_)
    by_cases hx : x ∈ Cᶜ
    · exact Or.inr hx
    · exact Or.inl (subset_closure (by simpa using hx))
  have hmain := isPreconnected_inter_of_union_eq_univ isClosed_closure hC.isClosed_compl
    hCp.closure hCc hcover
  rw [frontier_eq_closure_inter_closure, hC.isClosed_compl.closure_eq]
  exact hmain

end Work.BoxShrink.Pinch
