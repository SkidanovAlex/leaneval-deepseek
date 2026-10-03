import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.twoLetter_F2_generation
import Submission.Work.OROneRel.winRho_winRoot
import Submission.Work.OROneRel.decor_invRev
import Submission.Work.OROneRel.mk_expand
import Submission.Work.OROneRel.decor_pow_flatMap
import Submission.Work.OROneRel.coedgeBase
import Submission.Work.OROneRel.walkE_edgeWordSigned
import Submission.Work.OROneRel.walkE_flatten_map
import Submission.Work.OROneRel.lsig_edgeWordSigned

/-!
# The range of the window class map, as a set of closed walks

For the two-letter band data (`c = tlW p q`, the window `[0,p*q]`, a gauge `Wt`) this file proves
the description of the range of the class map `winRho Wt c 0 (p*q) : F β →* F a,b` of the vertex as
the set of *closed walks inside the window*:

`x ∈ (winRho Wt c 0 (p*q)).range ↔ ∃ L, (every edge of the walk of L lies in the window)
                                   ∧ lsig c L = 0 ∧ FreeGroup.mk L = x`.

## The two directions

The backward direction (`←`) is the closed-walk criterion
`Work.OROneRel.mk_mem_winRho_range_of_decor` (proved in
`Submission/Work/OROneRel/twoLetter_F2_generation.lean`): a word of weight `0` whose walk stays in
the window spells an element of `π₁` of the window, i.e. of the range of `winRho`.  Note that it does
not use the hypotheses `hwin`/`htree`; these enter the statement through the caller.

The forward direction (`→`) is the expansion `winExpand`: an element `v ∈ F β` is a word in the
non-tree edges of the window, and each symbol `e = (x,i)` of `β` is realised by the **loop word**

`edgeWord Wt c e = wordOf (Wt i) ++ [(x,true)] ++ wordOf ((Wt (i + c x))⁻¹)`,

the tree path from level `0` out to the edge, the edge itself and the tree path back — a closed walk
of weight `0` based at level `0` (`lsig_edgeWordSigned`), all of whose edges lie in the window
(`walkE_edgeWordSigned`: the two tree paths stay in the window by `htree`, and the middle edge is in
the window because `e ∈ β ⊆ winE`).  Replacing each symbol of the word of `v` (reversed for the
negative letters, `edgeWordSigned ... false = invRev (edgeWord ...)`) gives a word `winExpand v`, and

* `winExpand_mk`: `FreeGroup.mk (winExpand v) = winRho v` — the telescoping computation, via
  `mk_flatten_expand` and the pointwise `mk_edgeWordSigned`;
* `winExpand_walk`: every edge of the walk of `winExpand v` is in the window — a concatenation of
  walks that each start and end at level `0`, via `walkE_flatten_map`;
* `winExpand_lsig`: `lsig c (winExpand v) = 0`, the sum of the weights of the pieces.

The ingredients of the walk condition are the two delegated lemmas
`Work.OROneRel.walkE_edgeWordSigned` and `Work.OROneRel.walkE_flatten_map`, and the weight vanishing
is `Work.OROneRel.lsig_edgeWordSigned`.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The decidability instance making `FreeGroup.toWord` available on the window alphabet. -/
noncomputable instance winBetaDecEq (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) :
    DecidableEq (winBeta Wt c lo hi) := Classical.decEq _

/-- **The expansion of a word in the window alphabet**: replace every signed symbol `(e,b)` of the
reduced word of `v ∈ F β` by the loop word `edgeWord Wt c e` of the edge `e` (inverted for
`b = false`).  The result is a word of `F α` whose walk is a concatenation of closed walks based at
level `0`, and which spells `winRho v`. -/
noncomputable def winExpand (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (v : FreeGroup (winBeta Wt c lo hi)) : List (α × Bool) :=
  ((FreeGroup.toWord v).map (fun p => edgeWordSigned Wt c p.1.1 p.2)).flatten

/-- **The expansion spells the class-map image.** -/
theorem winExpand_mk (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (v : FreeGroup (winBeta Wt c lo hi)) :
    FreeGroup.mk (winExpand Wt c lo hi v) = winRho Wt c lo hi v := by
  have key : FreeGroup.mk (winExpand Wt c lo hi v)
      = FreeGroup.lift (fun e : winBeta Wt c lo hi => coverClassAt Wt c e.1)
          (FreeGroup.mk (FreeGroup.toWord v)) :=
    mk_flatten_expand (fun p : winBeta Wt c lo hi × Bool => edgeWordSigned Wt c p.1.1 p.2)
      (fun e : winBeta Wt c lo hi => coverClassAt Wt c e.1)
      (fun p => mk_edgeWordSigned Wt c p.1.1 p.2) (FreeGroup.toWord v)
  rw [key, FreeGroup.mk_toWord]
  rfl

/-- The weight of the concatenation of a list of words of vanishing weight vanishes. -/
theorem lsig_flatten_eq_zero (c : α → ℤ) (L : List (List (α × Bool)))
    (h : ∀ l ∈ L, lsig c l = 0) : lsig c L.flatten = 0 := by
  induction L with
  | nil => simp [lsig]
  | cons a t ih =>
      rw [List.flatten_cons, lsig_append_gen, h a (List.mem_cons_self ..),
        ih (fun l hl => h l (List.mem_cons_of_mem _ hl))]
      simp

/-- **The expansion has weight zero.**  Each piece `edgeWordSigned Wt c e b` is a closed walk of
weight `0` (`Work.OROneRel.lsig_edgeWordSigned`), using that `Wt` is a gauge: the tree path out to
level `i` has weight `i` and the tree path back from level `i + c x` has weight `-(i + c x)`. -/
theorem winExpand_lsig (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (hcoh : ∀ i : ℤ, lo ≤ i → i ≤ hi → cohom c (Wt i) = Multiplicative.ofAdd i)
    (v : FreeGroup (winBeta Wt c lo hi)) :
    lsig c (winExpand Wt c lo hi v) = 0 := by
  show lsig c (((FreeGroup.toWord v).map (fun p : winBeta Wt c lo hi × Bool =>
    edgeWordSigned Wt c p.1.1 p.2)).flatten) = 0
  refine lsig_flatten_eq_zero c ((FreeGroup.toWord v).map (fun p : winBeta Wt c lo hi × Bool =>
    edgeWordSigned Wt c p.1.1 p.2)) (fun l hl => ?_)
  rcases List.mem_map.mp hl with ⟨p, _, rfl⟩
  have hmem := mem_winE.mp (winBeta_val_mem (Wt := Wt) (c := c) p.1)
  refine lsig_edgeWordSigned Wt c p.1.1 p.2 ?_ ?_
  · rw [hcoh p.1.1.2 hmem.1 hmem.2.1]
    rfl
  · rw [hcoh (p.1.1.2 + c p.1.1.1) hmem.2.2.1 hmem.2.2.2]
    rfl

/-- **The expansion stays in the window.**  Every edge of the walk of `winExpand Wt c lo hi v` lies in
`winE c lo hi`, provided the gauge words `Wt i` are walks inside the window for the levels
`i ∈ [lo,hi]` (the hypothesis `htree` of the band case). -/
theorem winExpand_walk (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (hWt : ∀ i : ℤ, lo ≤ i → i ≤ hi → ∀ e ∈ decor c 0 (wordOf (Wt i)), coverEdge e ∈ winE c lo hi)
    (hcoh : ∀ i : ℤ, lo ≤ i → i ≤ hi → cohom c (Wt i) = Multiplicative.ofAdd i)
    (v : FreeGroup (winBeta Wt c lo hi)) :
    ∀ q ∈ decor c 0 (winExpand Wt c lo hi v), coverEdge q ∈ winE c lo hi := by
  refine walkE_flatten_map c lo hi (FreeGroup.toWord v)
    (fun p : winBeta Wt c lo hi × Bool => edgeWordSigned Wt c p.1.1 p.2) ?_ ?_
  · intro p _hp q hq
    have hmem := mem_winE.mp (winBeta_val_mem (Wt := Wt) (c := c) p.1)
    refine walkE_edgeWordSigned Wt c lo hi p.1.1 p.2 (winBeta_val_mem p.1)
      (hWt p.1.1.2 hmem.1 hmem.2.1) (hWt (p.1.1.2 + c p.1.1.1) hmem.2.2.1 hmem.2.2.2)
      ?_ ?_ q hq
    · rw [hcoh p.1.1.2 hmem.1 hmem.2.1]
      rfl
    · rw [hcoh (p.1.1.2 + c p.1.1.1) hmem.2.2.1 hmem.2.2.2]
      rfl
  · intro p _hp
    have hmem := mem_winE.mp (winBeta_val_mem (Wt := Wt) (c := c) p.1)
    refine lsig_edgeWordSigned Wt c p.1.1 p.2 ?_ ?_
    · rw [hcoh p.1.1.2 hmem.1 hmem.2.1]
      rfl
    · rw [hcoh (p.1.1.2 + c p.1.1.1) hmem.2.2.1 hmem.2.2.2]
      rfl

/-- **Every element of the range of `winRho` is spelled by a closed walk in the window.**  This is the
general (two-directional-ready) form of the forward implication of the target, proved by expanding a
preimage in `F β` with `winExpand`. -/
theorem exists_walk_mem_winRho_range (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (hWt : ∀ i : ℤ, lo ≤ i → i ≤ hi → ∀ e ∈ decor c 0 (wordOf (Wt i)), coverEdge e ∈ winE c lo hi)
    (hcoh : ∀ i : ℤ, lo ≤ i → i ≤ hi → cohom c (Wt i) = Multiplicative.ofAdd i)
    {x : FreeGroup α} (hx : x ∈ (winRho Wt c lo hi).range) :
    ∃ L : List (α × Bool), (∀ q ∈ decor c 0 L, coverEdge q ∈ winE c lo hi) ∧
      lsig c L = 0 ∧ FreeGroup.mk L = x := by
  obtain ⟨v, rfl⟩ := hx
  exact ⟨winExpand Wt c lo hi v, winExpand_walk Wt c lo hi hWt hcoh v,
    winExpand_lsig Wt c lo hi hcoh v, winExpand_mk Wt c lo hi v⟩

theorem mem_winRho_range_iff (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (x : FreeGroup (Fin 2)) :
    (x ∈ (Work.OROneRel.winRho Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))).range) ↔
      ∃ L : List (Fin 2 × Bool),
        (∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 L,
          Work.OROneRel.coverEdge e ∈
            Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))) ∧
        Work.OROneRel.lsig (Work.OROneRel.tlW p q) L = 0 ∧ FreeGroup.mk L = x := by
  constructor
  · -- `→`: expand a preimage in `F β` into a closed walk in the window.
    intro hx
    exact exists_walk_mem_winRho_range Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ))
      (fun i hi0 hipq e he => (mem_winTree.mp (htree i hi0 hipq e he)).1)
      (fun i _ _ => hcoh i) hx
  · -- `←`: a closed walk in the window spells an element of the vertex group.
    rintro ⟨L, hwalk, hlsig, rfl⟩
    exact mk_mem_winRho_range_of_decor Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ)) hW0 L hlsig hwalk

end Work.OROneRel
