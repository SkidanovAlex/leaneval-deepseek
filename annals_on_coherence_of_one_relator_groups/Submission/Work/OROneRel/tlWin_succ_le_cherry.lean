/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The "cherry" step of the window recursion of the two-letter band

`tlWin p q m` (`Work.OROneRel.tlWin`) is the **gauge-free window subgroup** `π₁(Y[0,m])` of the
level graph of the weight `tlW p q` (`a = 0 ↦ q`, `b = 1 ↦ -p`): the subgroup of `F₂` of the
elements spelled by a word of weight `0` whose decorated walk (read from level `0`) stays in the
window `[0,m]`.

**Van Kampen.**  For `m ≥ p+q-1` the window `[0,m+1]` is obtained from the window `[0,m]` by
attaching a *cherry* at the new vertex `m+1`: the two edges

* `e_a = (0, m+1-q)`, running from level `m+1-q` up to level `m+1`,
* `e_b = (1, m+1)`, running from level `m+1` down to level `m+1-p`,

whose attachment levels `m+1-q`, `m+1-p` both lie in `[0,m]` (`winE_succ_union` states exactly that
these are the only two new edges).  Given *connection paths* `pα`, `pβ` from the base level `0` to
the attachment levels — elements of `F₂` represented by words of weights `m+1-q`, `m+1-p` whose
walks lie in `[0,m]` (the hypotheses `hα`, `hβ`) — the single new cycle is the loop

  `P = pα · a · b · pβ⁻¹`,   `a = FreeGroup.of 0`, `b = FreeGroup.of 1`,

and hence

  `tlWin p q (m+1) ≤ tlWin p q m ⊔ ⟪P⟫`.

This is the statement proved here (`tlWin_succ_le_cherry`).  It is the exact form in which the
window recursion is consumed by the climb of the band (`Work.OROneRel.tlWin_succ_le_shift`): it is
the *lower* half of the recursion, and it isolates the new generator instead of the conjugate
`τ · tlWin m · τ⁻¹`.

**Proof.**  Every loop of `[0,m+1]` decomposes, at the first letter whose traversed edge leaves the
old window, into an old prefix `A`, a *unit* `[x,y]` of two new letters (up to `m+1` and back), and
a strictly shorter tail `D`:

  `mk L = mk A · mk [x,y] · mk D`.

Conjugating the three factors by the connection elements attached to the (three) outer levels
`0`, `m+1-q`, `m+1-p` turns them into: a loop of the old window (`cherryOld_mem`), the cherry
generator or its inverse (`cherry_unit_mem_ne`, `cherry_unit_mem_eq`, with the degenerate case
`p = q` handled by `cherry_beta_alpha_inv_mem`), and, by induction, the same statement for `D`.
The bookkeeping lemmas are delegated to the files imported below:

* `Work.OROneRel.winE_succ_union` -- the two new edges;
* `Work.OROneRel.exists_old_prefix` -- the split at the first new letter;
* `Work.OROneRel.cherry_new_letter`, `Work.OROneRel.cherry_down_letter` -- the two new letters;
* `Work.OROneRel.cherry_old_end_window` -- the end of an old walk stays in `[0,m]`;
* `Work.OROneRel.cherryOld_mem` -- the old prefix after conjugation;
* `Work.OROneRel.cherry_unit_mem_ne`, `Work.OROneRel.cherry_unit_mem_eq`,
  `Work.OROneRel.cherry_beta_alpha_inv_mem` -- the unit.

All the definitions of the argument (`decorAt`, `cherryNewE`, `cherryOuter`, `cherryConn`,
`cherryConnList`) are in `Submission/Work/OROneRel/tlWinCherryDefs.lean`.
-/
import Mathlib
import Submission.Work.OROneRel.band_hnnConjMap_injective
import Submission.Work.OROneRel.bandWinDefs
import Submission.Work.OROneRel.twoLetter_generation
import Submission.Work.OROneRel.tlWinCherryDefs
import Submission.Work.OROneRel.winE_succ_union
import Submission.Work.OROneRel.exists_old_prefix
import Submission.Work.OROneRel.cherryOld_mem
import Submission.Work.OROneRel.cherry_beta_alpha_inv_mem
import Submission.Work.OROneRel.cherry_new_letter
import Submission.Work.OROneRel.cherry_down_letter
import Submission.Work.OROneRel.cherry_old_end_window
import Submission.Work.OROneRel.cherry_unit_mem_ne
import Submission.Work.OROneRel.cherry_unit_mem_eq

namespace Work.OROneRel

/-- The target subgroup of the cherry lemma: the old window together with the cherry loop. -/
noncomputable def cherryWin (p q : ℕ) (m : ℤ) (P : FreeGroup (Fin 2)) :
    Subgroup (FreeGroup (Fin 2)) :=
  tlWin p q m ⊔ Subgroup.closure ({P} : Set (FreeGroup (Fin 2)))

/-- The cherry loop `pα · a · b · pβ⁻¹`. -/
noncomputable def cherryP (pα pβ : FreeGroup (Fin 2)) : FreeGroup (Fin 2) :=
  pα * FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) * pβ⁻¹

/-- The class of a two-letter word followed by `D`. -/
theorem mk_pair_eq (x y : Fin 2 × Bool) (D : List (Fin 2 × Bool)) :
    FreeGroup.mk (x :: y :: D) = FreeGroup.mk [x, y] * FreeGroup.mk D := by
  rw [show x :: y :: D = [x, y] ++ D from rfl, FreeGroup.mul_mk]

/-- The weight of a two-letter word is the sum of the weights of its letters. -/
theorem lsig_pair (c : Fin 2 → ℤ) (x y : Fin 2 × Bool) :
    lsig c [x, y] = linc c x + linc c y := by
  simp only [lsig, linc, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-- **The invariant of the cherry argument.**  For a word `L` read from an outer level `s` (one of
`0`, `m+1-q`, `m+1-p`), ending at an outer level `t`, whose decorated walk stays in the window
`[0,m+1]` and whose weight is `t - s`, the conjugation by the connection elements at `s` and `t`
lands in `cherryWin p q m (cherryP pα pβ)`.  The target is the case `s = t = 0` (where the
connection elements are `1`). -/
theorem cherry_main (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {m : ℤ}
    (hm1 : ((p : ℤ) + (q : ℤ) - 1) ≤ m)
    {Lα Lβ : List (Fin 2 × Bool)} {pα pβ : FreeGroup (Fin 2)}
    (hmkα : FreeGroup.mk Lα = pα) (hmkβ : FreeGroup.mk Lβ = pβ)
    (hlsigα : lsig (tlW p q) Lα = m + 1 - (q : ℤ))
    (hlsigβ : lsig (tlW p q) Lβ = m + 1 - (p : ℤ))
    (hwalkα : ∀ e ∈ decor (tlW p q) 0 Lα, coverEdge e ∈ winE (tlW p q) 0 m)
    (hwalkβ : ∀ e ∈ decor (tlW p q) 0 Lβ, coverEdge e ∈ winE (tlW p q) 0 m) :
    ∀ (L : List (Fin 2 × Bool)) (s t : ℤ), cherryOuter p q m s → cherryOuter p q m t →
      (∀ e ∈ decor (tlW p q) s L, coverEdge e ∈ winE (tlW p q) 0 (m + 1)) →
      lsig (tlW p q) L = t - s →
      cherryConn p q m pα pβ s * FreeGroup.mk L * (cherryConn p q m pα pβ t)⁻¹ ∈
        cherryWin p q m (cherryP pα pβ) := by
  have key : ∀ n : ℕ, ∀ (L : List (Fin 2 × Bool)), L.length = n →
      ∀ s t : ℤ, cherryOuter p q m s → cherryOuter p q m t →
      (∀ e ∈ decor (tlW p q) s L, coverEdge e ∈ winE (tlW p q) 0 (m + 1)) →
      lsig (tlW p q) L = t - s →
      cherryConn p q m pα pβ s * FreeGroup.mk L * (cherryConn p q m pα pβ t)⁻¹ ∈
        cherryWin p q m (cherryP pα pβ) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih L hLen s t hs ht hwalk hlsig
    rcases exists_old_prefix p q hp hq hm1 s L hwalk with
      hall | ⟨A, x, B, hL, hA, hxne, hxle, hwalkB⟩
    · -- ### the loop is an old loop
      exact Subgroup.mem_sup_left (cherryOld_mem p q hp hq hm1 hmkα hmkβ hlsigα hlsigβ
        hwalkα hwalkβ hs ht hall hlsig)
    · -- ### the split point
      obtain ⟨h0s, hms⟩ := cherryOuter_mem_window p q hp hq hm1 hs
      obtain ⟨h0s', hms'⟩ := cherry_old_end_window p q hp hq hm1 h0s hms hA
      obtain ⟨hs', hup⟩ := cherry_new_letter p q hp hq hm1 h0s' hms' hxle hxne
      have hlevel : (s + lsig (tlW p q) A) + linc (tlW p q) x = m + 1 :=
        hup.elim (fun h => h.2.2) (fun h => h.2.2)
      -- ### `B` is nonempty: the walk has to come back down from the new vertex
      have hBne : B ≠ [] := by
        intro hBnil
        have hl : lsig (tlW p q) L = m + 1 - s := by
          have h1 : lsig (tlW p q) (A ++ [x]) = lsig (tlW p q) A + linc (tlW p q) x := by
            simp only [lsig, linc, List.map_append, List.map_cons, List.map_nil,
              List.sum_append, List.sum_cons, List.sum_nil, add_zero]
          have h2 : lsig (tlW p q) A = (s + lsig (tlW p q) A) - s := by ring
          rw [hL, hBnil, h1, h2]
          linarith
        have ht_eq : t = m + 1 := by linarith
        rcases ht with h | h | h <;> omega
      obtain ⟨y, D, rfl⟩ := List.exists_cons_of_ne_nil hBne
      -- ### the first letter after the new vertex is one of the two new letters
      have hy_mem : coverEdge (decorAt (tlW p q) (m + 1) y) ∈ winE (tlW p q) 0 (m + 1) := by
        have h := hwalkB (decorAt (tlW p q) ((s + lsig (tlW p q) A) + linc (tlW p q) x) y) ?_
        rwa [hlevel] at h
        rw [decor_cons_decorAt, decor_cons_decorAt]
        exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      have hynew : coverEdge (decorAt (tlW p q) (m + 1) y) ∈ cherryNewE p q m := by
        rcases (winE_succ_union p q hp hq hm1
          (coverEdge (decorAt (tlW p q) (m + 1) y))).mp hy_mem with h1 | h2 | h2
        · exfalso
          have hsrc : coverSrc (tlW p q) (decorAt (tlW p q) (m + 1) y) = m + 1 :=
            coverSrc_head_l (tlW p q) (m + 1) y
          have hb := (coverEdge_mem_winE_iff (tlW p q) 0 m
            (decorAt (tlW p q) (m + 1) y)).mp h1
          rw [hsrc] at hb
          omega
        · rw [mem_cherryNewE]; exact Or.inl h2
        · rw [mem_cherryNewE]; exact Or.inr h2
      have hy0 : y = ((0 : Fin 2), false) ∨ y = ((1 : Fin 2), true) := by
        rcases cherry_down_letter p q hp hq hynew with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact Or.inl h1
        · exact Or.inr h1
      -- ### the unit
      have hlev2 : ((s + lsig (tlW p q) A) + linc (tlW p q) x) + linc (tlW p q) y =
          (s + lsig (tlW p q) A) + lsig (tlW p q) [x, y] := by
        rw [lsig_pair]; ring
      have hup' : (s + lsig (tlW p q) A = m + 1 - (q : ℤ) ∧ x = ((0 : Fin 2), true)) ∨
          (s + lsig (tlW p q) A = m + 1 - (p : ℤ) ∧ x = ((1 : Fin 2), false)) :=
        hup.elim (fun h => Or.inl ⟨h.1, h.2.1⟩) (fun h => Or.inr ⟨h.1, h.2.1⟩)
      have hUn : cherryConn p q m pα pβ (s + lsig (tlW p q) A) * FreeGroup.mk [x, y] *
            (cherryConn p q m pα pβ ((s + lsig (tlW p q) A) + lsig (tlW p q) [x, y]))⁻¹ ∈
              cherryWin p q m (cherryP pα pβ) ∧
          cherryOuter p q m ((s + lsig (tlW p q) A) + lsig (tlW p q) [x, y]) := by
        by_cases hcase : m + 1 - (p : ℤ) = m + 1 - (q : ℤ)
        · exact cherry_unit_mem_eq p q hp hq m hcase
            (cherry_beta_alpha_inv_mem p q hp hq hm1 hmkα hmkβ hlsigα hlsigβ
              hwalkα hwalkβ hcase) (s := s + lsig (tlW p q) A) x y hup' hy0
        · exact cherry_unit_mem_ne p q hp hq m hcase
            (s := s + lsig (tlW p q) A) x y hup' hy0
      obtain ⟨hUn_mem, ht'⟩ := hUn
      -- ### the old prefix
      have hlsigA : lsig (tlW p q) A = (s + lsig (tlW p q) A) - s := by ring
      have hA_mem : cherryConn p q m pα pβ s * FreeGroup.mk A *
          (cherryConn p q m pα pβ (s + lsig (tlW p q) A))⁻¹ ∈ cherryWin p q m (cherryP pα pβ) :=
        Subgroup.mem_sup_left (cherryOld_mem p q hp hq hm1 hmkα hmkβ hlsigα hlsigβ
          hwalkα hwalkβ hs hs' hA hlsigA)
      -- ### the tail
      have hdec : decor (tlW p q) s L =
          decor (tlW p q) s A ++ decorAt (tlW p q) (s + lsig (tlW p q) A) x ::
            decorAt (tlW p q) ((s + lsig (tlW p q) A) + linc (tlW p q) x) y ::
              decor (tlW p q) ((s + lsig (tlW p q) A) + lsig (tlW p q) [x, y]) D := by
        rw [hL, decor_append, decor_cons_decorAt, decor_cons_decorAt, hlev2]
      have hwalkD : ∀ e ∈ decor (tlW p q) ((s + lsig (tlW p q) A) + lsig (tlW p q) [x, y]) D,
          coverEdge e ∈ winE (tlW p q) 0 (m + 1) := by
        intro e he
        apply hwalk
        rw [hdec]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      have hlsigD : lsig (tlW p q) D =
          t - ((s + lsig (tlW p q) A) + lsig (tlW p q) [x, y]) := by
        have h1 : lsig (tlW p q) L =
            lsig (tlW p q) A + linc (tlW p q) x + linc (tlW p q) y + lsig (tlW p q) D := by
          rw [hL, decor_lsig_append, lsig_cons_l, lsig_cons_l]
          ring
        rw [h1] at hlsig
        rw [lsig_pair]
        linarith
      have hLlen : L.length = A.length + 2 + D.length := by
        rw [hL]; simp only [List.length_append, List.length_cons]; ring
      have hlt : D.length < n := by omega
      have hD_mem : cherryConn p q m pα pβ ((s + lsig (tlW p q) A) + lsig (tlW p q) [x, y]) *
          FreeGroup.mk D * (cherryConn p q m pα pβ t)⁻¹ ∈ cherryWin p q m (cherryP pα pβ) :=
        ih D.length hlt D rfl ((s + lsig (tlW p q) A) + lsig (tlW p q) [x, y]) t ht' ht
          hwalkD hlsigD
      -- ### assembly
      have hfac : cherryConn p q m pα pβ s * FreeGroup.mk L * (cherryConn p q m pα pβ t)⁻¹ =
          (cherryConn p q m pα pβ s * FreeGroup.mk A *
              (cherryConn p q m pα pβ (s + lsig (tlW p q) A))⁻¹) *
            (cherryConn p q m pα pβ (s + lsig (tlW p q) A) * FreeGroup.mk [x, y] *
              (cherryConn p q m pα pβ ((s + lsig (tlW p q) A) + lsig (tlW p q) [x, y]))⁻¹) *
          (cherryConn p q m pα pβ ((s + lsig (tlW p q) A) + lsig (tlW p q) [x, y]) *
            FreeGroup.mk D * (cherryConn p q m pα pβ t)⁻¹) := by
        have hmkL : FreeGroup.mk L = FreeGroup.mk A * (FreeGroup.mk [x, y] * FreeGroup.mk D) := by
          rw [hL]
          rw [show A ++ x :: y :: D = A ++ (x :: y :: D) from rfl, ← FreeGroup.mul_mk, mk_pair_eq]
        rw [hmkL]
        group
      rw [hfac]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hA_mem hUn_mem) hD_mem
  intro L s t hs ht hwalk hlsig
  exact key L.length L rfl s t hs ht hwalk hlsig

theorem tlWin_succ_le_cherry (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    {m : ℤ} (hm1 : ((p : ℤ) + (q : ℤ) - 1) ≤ m)
    {pα pβ : FreeGroup (Fin 2)}
    (hα : ∃ L : List (Fin 2 × Bool), FreeGroup.mk L = pα ∧ lsig (tlW p q) L = m + 1 - (q : ℤ) ∧
      ∀ e ∈ decor (tlW p q) 0 L, coverEdge e ∈ winE (tlW p q) 0 m)
    (hβ : ∃ L : List (Fin 2 × Bool), FreeGroup.mk L = pβ ∧ lsig (tlW p q) L = m + 1 - (p : ℤ) ∧
      ∀ e ∈ decor (tlW p q) 0 L, coverEdge e ∈ winE (tlW p q) 0 m) :
    tlWin p q (m + 1) ≤ tlWin p q m ⊔
      Subgroup.closure ({pα * FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) * pβ⁻¹} :
        Set (FreeGroup (Fin 2))) := by
  obtain ⟨Lα, hmkα, hlsigα, hwalkα⟩ := hα
  obtain ⟨Lβ, hmkβ, hlsigβ, hwalkβ⟩ := hβ
  have hmain := cherry_main p q hp hq hm1 hmkα hmkβ hlsigα hlsigβ hwalkα hwalkβ
  unfold tlWin
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨L, rfl, hlsig, hwalk⟩
  have h := hmain L 0 0 (Or.inl rfl) (Or.inl rfl) hwalk ?_
  · rw [cherryConn_zero p q hp hq hm1, inv_one, one_mul,
      mul_one] at h
    exact h
  · rw [hlsig]; ring

end Work.OROneRel
