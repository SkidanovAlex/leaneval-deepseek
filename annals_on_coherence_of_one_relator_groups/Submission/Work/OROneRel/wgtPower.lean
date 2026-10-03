import Mathlib
import Submission.Work.OROneRel.wgtMMDefs
import Submission.Work.OROneRel.wvListAuxAppend
import Submission.Work.OROneRel.wvListAuxFlattenReplicate
import Submission.Work.OROneRel.wordOf_pow_flatten
import Submission.Work.OROneRel.lsig_wordOf_eq_zero

/-!
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The weighted Magnus relator of a power

Let `c : α → ℤ` be an integer weight with `cohom c u = 1` and let `u` be a cyclically reduced
relator.  The weighted Magnus rewriting of `u ^ l` is obtained from that of `u` by taking `l`
copies: because the total weight of `u` vanishes (`lsig c (wordOf u) = 0`), each copy of `u`
starts at running weight `0` again, so the decorated words are the same and

* the set of occurring symbols agrees, `wDecSet c t (u ^ l) = wDecSet c t u`, and the identity on
  the underlying symbols is a bijection `wBeta c t (u ^ l) ≃ wBeta c t u`;
* the relator satisfies `wW c t (u ^ l) = wW c t u ^ l` (up to that identification of the symbol
  types).

This is the statement `Work.OROneRel.wgtPower` used by
`Submission.Work.OROneRel.magnusStepCase2_of_weight`.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ## Two generic list lemmas -/

/-- The word of `l` copies of a list, evaluated in a free group, is the `l`-th power. -/
theorem mkFlattenReplicate {β : Type*} (L : List (β × Bool)) (l : ℕ) :
    FreeGroup.mk (List.flatten (List.replicate l L)) = (FreeGroup.mk L) ^ l := by
  induction l with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, ← FreeGroup.mul_mk, ih, pow_succ']

/-- A letter occurring in the word of `l ≥ 1` copies of `L` occurs in `L`. -/
theorem memFlattenReplicate {β : Type*} {a : β × Bool} {L : List (β × Bool)} {l : ℕ}
    (hl : l ≠ 0) : a ∈ List.flatten (List.replicate l L) ↔ a ∈ L := by
  simp only [List.mem_flatten, List.mem_replicate]
  constructor
  · rintro ⟨L', ⟨-, rfl⟩, h⟩; exact h
  · intro h; exact ⟨L, ⟨hl, rfl⟩, h⟩

/-! ## The main theorem -/

theorem wgtPower {α : Type u} [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α) (l : ℕ)
    (hl : 1 ≤ l) (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hcu : Work.OROneRel.cohom c u = 1) :
    ∃ eβ : Work.OROneRel.wBeta c t (u ^ l) ≃ Work.OROneRel.wBeta c t u,
      (∀ p, (eβ p).1 = p.1) ∧
      FreeGroup.map (fun p : Work.OROneRel.wBeta c t (u ^ l) => eβ p)
          (Work.OROneRel.wW c t (u ^ l)) = (Work.OROneRel.wW c t u) ^ l := by
  classical
  -- the total weight of `u` vanishes, so every copy of `u` starts at running weight `0`
  have hlsig : lsig c (wordOf u) = 0 := lsig_wordOf_eq_zero c u hcu
  have hword : wordOf (u ^ l) = List.flatten (List.replicate l (wordOf u)) :=
    wordOf_pow_flatten u l hcyc
  have hWl : wvListAux c t 0 (wordOf (u ^ l))
      = List.flatten (List.replicate l (wvListAux c t 0 (wordOf u))) := by
    rw [hword]
    exact wvListAuxFlattenReplicate c t 0 (wordOf u) l hlsig
  have hl0 : l ≠ 0 := by omega
  -- ### the decorated words agree, hence so do the occurring symbols
  have hdec : ∀ x : {x : α // x ≠ t}, wDecs c t (u ^ l) x = wDecs c t u x := by
    intro x
    apply Finset.ext
    intro k
    rw [mem_wDecs_iff c t (u ^ l) x k, mem_wDecs_iff c t u x k, hWl]
    constructor
    · intro h
      obtain ⟨b, hb⟩ := h
      exact ⟨b, (memFlattenReplicate (β := WgtBeta t) hl0).mp hb⟩
    · intro h
      obtain ⟨b, hb⟩ := h
      exact ⟨b, (memFlattenReplicate (β := WgtBeta t) hl0).mpr hb⟩
  have hlo : ∀ x : {x : α // x ≠ t}, wLo c t (u ^ l) x = wLo c t u x := by
    intro x
    rw [wLo, wLo, hdec x]
  have hhi : ∀ x : {x : α // x ≠ t}, wHi c t (u ^ l) x = wHi c t u x := by
    intro x
    rw [wHi, wHi, hdec x]
  have hset : wDecSet c t (u ^ l) = wDecSet c t u := by
    ext p
    simp only [wDecSet, Set.mem_ofPred_eq]
    rw [hlo p.1, hhi p.1]
  -- ### the symbols of the two rewritings
  let eβ : wBeta c t (u ^ l) ≃ wBeta c t u :=
    Equiv.subtypeEquivRight (fun p => by rw [hset])
  have heβval : ∀ p : wBeta c t (u ^ l), (eβ p).1 = p.1 := fun _ => rfl
  refine ⟨eβ, heβval, ?_⟩
  have hWL_l : wWL c t (u ^ l)
      = (wvListAux c t 0 (wordOf (u ^ l))).map
          (fun p : WgtBeta t × Bool => (wBetaOf c t (u ^ l) p.1, p.2)) := rfl
  have hWL_u : wWL c t u
      = (wvListAux c t 0 (wordOf u)).map
          (fun p : WgtBeta t × Bool => (wBetaOf c t u p.1, p.2)) := rfl
  -- on the symbols of `u` the two ways of relabelling agree
  have hmap : (wvListAux c t 0 (wordOf u)).map
        ((fun x : wBeta c t (u ^ l) × Bool => (eβ x.1, x.2)) ∘
          (fun p : WgtBeta t × Bool => (wBetaOf c t (u ^ l) p.1, p.2)))
      = (wvListAux c t 0 (wordOf u)).map
          (fun p : WgtBeta t × Bool => (wBetaOf c t u p.1, p.2)) := by
    apply List.map_congr_left
    intro p hp
    obtain ⟨q, b⟩ := p
    have hq : q ∈ wDecSet c t u := wList_mem_decSet c t u hp
    have hq' : q ∈ wDecSet c t (u ^ l) := by rw [hset]; exact hq
    show (eβ (wBetaOf c t (u ^ l) q), b) = (wBetaOf c t u q, b)
    rw [Prod.mk.injEq]
    refine ⟨?_, rfl⟩
    apply Subtype.ext
    rw [show (eβ (wBetaOf c t (u ^ l) q)).1 = (wBetaOf c t (u ^ l) q).1 from rfl,
      wBetaOf_val (c := c) (t := t) (u := u ^ l) hq',
      wBetaOf_val (c := c) (t := t) (u := u) hq]
  -- ### the two words agree
  have key : (wWL c t (u ^ l)).map (fun x : wBeta c t (u ^ l) × Bool => (eβ x.1, x.2))
      = List.flatten (List.replicate l (wWL c t u)) := by
    have h1 : (wWL c t (u ^ l)).map (fun x : wBeta c t (u ^ l) × Bool => (eβ x.1, x.2))
        = List.flatten (List.replicate l
            ((wvListAux c t 0 (wordOf u)).map
              (fun p : WgtBeta t × Bool => (wBetaOf c t u p.1, p.2)))) := by
      rw [hWL_l, hWl, List.map_map, List.map_flatten, List.map_replicate, hmap]
    rw [h1, hWL_u]
  rw [wW, FreeGroup.map.mk]
  rw [show (fun x : wBeta c t (u ^ l) × Bool => ((fun p : wBeta c t (u ^ l) => eβ p) x.1, x.2))
        = (fun x : wBeta c t (u ^ l) × Bool => (eβ x.1, x.2)) from rfl]
  rw [key]
  exact mkFlattenReplicate (wWL c t u) l

end Work.OROneRel
