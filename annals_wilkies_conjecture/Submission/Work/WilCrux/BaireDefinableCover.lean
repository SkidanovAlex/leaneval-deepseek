import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilkG4c.Pre
import Submission.Work.WilG1.Cell.thin_closure

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCrux

open WilkiesDesign

/-! ## Covering one definable set by a closed nowhere dense set

The heart of the Baire argument: an `Ω`-definable set `X` is covered, on any set `Q` disjoint
from its interior, by a closed nowhere dense set.  Concretely: if `X ∈ S.Ω F D a` and
`interior X ∩ Q = ∅`, then there is a closed `N` with `interior N = ∅` and `X ∩ Q ⊆ N`.

Proof: take the sharp cylindrical decomposition of `ℝᵃ` compatible with `X` (`S.SharpCD`).
Every cell of the decomposition is `⊆ X` or disjoint from `X`, so the cells contained in `X`
cover `X`.  Among those, a cell with nonempty interior is *open* (a cylindrical cell with
nonempty interior is open, `isCell_isOpen_of_interior_nonempty`), hence lies in `interior X`
and therefore misses `Q`; a cell with empty interior has nowhere dense closure
(`isCell_isNowhereDense`).  So `X ∩ Q` lies in the finite union of the closures of the thin
cells of the decomposition. -/
theorem exists_closed_nowhereDense_cover {S : WilkiesDesign.SOMin} (hcd : S.SharpCD)
    {a F D : ℕ} {X : Set (Fin a → ℝ)} (hX : X ∈ S.Ω F D a) (Q : Set (Fin a → ℝ))
    (hQdisj : interior X ∩ Q = ∅) :
    ∃ N : Set (Fin a → ℝ), IsClosed N ∧ interior N = ∅ ∧ X ∩ Q ⊆ N := by
  classical
  obtain ⟨a', b', c', hsharp⟩ := hcd F a
  obtain ⟨C, hdec, hsep, -, -⟩ := hsharp D 1 (fun _ => X) (fun _ => hX)
  -- the cells of the decomposition that lie inside `X`
  set T : Finset (Set (Fin a → ℝ)) := C.filter (fun κ => κ ⊆ X) with hT
  -- the thin ones, whose closures are nowhere dense
  set B : Finset (Set (Fin a → ℝ)) := T.filter (fun κ => interior κ = ∅) with hB
  have hcl : IsClosed (⋃ κ ∈ B, closure κ) := isClosed_biUnion_finset (fun κ _ => isClosed_closure)
  refine ⟨⋃ κ ∈ B, closure κ, hcl, ?_, ?_⟩
  · have hnd_each : ∀ κ ∈ B, IsNowhereDense (closure κ) := by
      intro κ hκB
      obtain ⟨hκT, hemp⟩ := Finset.mem_filter.mp hκB
      have hκC : κ ∈ C := (Finset.mem_filter.mp hκT).1
      have hcell : IsCell a κ := Work.WilG1.Cell.isCell_of_mem_cylDecomp hdec hκC
      exact (Work.WilG1.Cell.isCell_isNowhereDense hcell hemp).closure
    have hnd : IsNowhereDense (⋃ κ ∈ B, closure κ) :=
      IsNowhereDense.biUnion (u := B) (f := fun κ => closure κ) hnd_each
    have hnd' : interior (closure (⋃ κ ∈ B, closure κ)) = ∅ := hnd
    rw [hcl.closure_eq] at hnd'
    exact hnd'
  · intro z hz
    obtain ⟨hzX, hzQ⟩ := hz
    obtain ⟨κ, hκC, hzκ⟩ := Work.WilG1.Cell.exists_mem_of_cylDecomp hdec z
    have hκT : κ ∈ T := by
      rw [hT]
      refine Finset.mem_filter.mpr ⟨hκC, ?_⟩
      rcases hsep 0 κ hκC with hsub | hdis
      · exact hsub
      · exact (Set.disjoint_left.mp hdis hzκ hzX).elim
    have hκsub : κ ⊆ X := (Finset.mem_filter.mp hκT).2
    by_cases hemp : interior κ = ∅
    · have hκB : κ ∈ B := by rw [hB]; exact Finset.mem_filter.mpr ⟨hκT, hemp⟩
      exact Set.mem_biUnion hκB (subset_closure hzκ)
    · exfalso
      have hne : (interior κ).Nonempty := Set.nonempty_iff_ne_empty.mpr hemp
      have hcell : IsCell a κ := Work.WilG1.Cell.isCell_of_mem_cylDecomp hdec hκC
      have hκopen : IsOpen κ := Work.WilkG4c.isCell_isOpen_of_interior_nonempty a hcell hne
      have hsub : κ ⊆ interior X := interior_maximal hκsub hκopen
      have hz' : z ∈ interior X ∩ Q := ⟨hsub hzκ, hzQ⟩
      rw [hQdisj] at hz'
      exact hz'

/-- **N4c1 (Baire over an `Omega`-definable cover).** If a nonempty open `Q` is covered by a
countable family of `Omega`-definable sets, then one of them has interior meeting `Q`.

Proof: otherwise every `A k ∩ Q` has empty interior in `Q`, so it is nowhere dense there
(an `Omega`-definable set of empty interior has nowhere dense closure, `thin_closure`);
this contradicts Baire for the nonempty open `Q`. -/
theorem BaireDefinableCover (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) {a : ℕ}
    (A : ℕ → Set (Fin a → ℝ)) (hA : ∀ k, ∃ F D : ℕ, A k ∈ S.Ω F D a)
    (Q : Set (Fin a → ℝ)) (hQ : IsOpen Q) (hQne : Q.Nonempty) (hcov : Q ⊆ ⋃ k, A k) :
    ∃ k, (interior (A k) ∩ Q).Nonempty := by
  classical
  by_contra hcon
  -- `hcon` says no `A k` has interior meeting `Q`, i.e. every `interior (A k) ∩ Q` is empty.
  have hdisj : ∀ k, interior (A k) ∩ Q = ∅ := fun k =>
    Set.not_nonempty_iff_eq_empty.mp (fun h => hcon ⟨k, h⟩)
  -- Replace every `A k` by a closed nowhere dense `N k` still covering `A k ∩ Q`.
  have hex : ∀ k, ∃ N : Set (Fin a → ℝ), IsClosed N ∧ interior N = ∅ ∧ A k ∩ Q ⊆ N := by
    intro k
    obtain ⟨F, D, hAk⟩ := hA k
    exact exists_closed_nowhereDense_cover hcd hAk Q (hdisj k)
  choose N hNclosed hNint hNsub using hex
  -- The complements of the `N k` are open dense, so their intersection is dense (Baire).
  have hfdense : ∀ k, Dense ((N k)ᶜ) := by
    intro k
    rw [dense_iff_closure_eq, closure_compl, hNint k]
    simp
  have hdense : Dense (⋂ k, (N k)ᶜ) :=
    dense_iInter_of_isOpen (fun k => (hNclosed k).isOpen_compl) hfdense
  -- The dense set meets the nonempty open `Q`; the point is in some `A j`, hence in `N j`,
  -- but it also avoids `N j`.
  obtain ⟨x, hxS, hxQ⟩ := hdense.exists_mem_open hQ hQne
  obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp (hcov hxQ)
  exact (Set.mem_iInter.mp hxS j) (hNsub j ⟨hxj, hxQ⟩)

end Work.WilCrux
