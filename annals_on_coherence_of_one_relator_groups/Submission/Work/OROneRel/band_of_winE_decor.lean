/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# A word whose decorated edges lie in a window has all its levels in the window

Let `c : α → ℤ` be a weight function and `L` a word.  The decorated word `decor c 0 L`
(`Submission.Work.OROneRel.MagnusGenDefs`) is the walk of `L` on the levels `ℤ`: the `k`-th
decorated letter runs from the level `lsig c (L.take k)` to the level `lsig c (L.take (k+1))`.
The window `winE c lo hi` (`Submission.Work.OROneRel.winBasisDefs`) consists of the edges *both*
of whose endpoints lie in `[lo,hi]`.

This file proves `band_of_winE_decor`: a **nonempty** word all of whose decorated edges lie in the
window has *every visited level* in the window, i.e. `band c lo hi L`.  Nonemptiness is needed
because the walk of the empty word has a single level, `0`, to which no edge is attached.

The proof is the elementary observation that the levels visited by the walk are exactly
`lsig c (L.take k)` for `0 ≤ k ≤ L.length`, and each such level is the source of the `k`-th
decorated letter (`k < L.length`) or the target of the last one (`k = L.length`), hence an
endpoint of an edge of the window.  This is packaged in the auxiliary lemma `band_aux`, which
carries the (stronger, level-shifted) statement that the *running* levels of a walk started at any
window level stay in the window.
-/
import Mathlib
import Submission.Work.OROneRel.winBandDefs
import Submission.Work.OROneRel.gaugeLevelDefs
import Submission.Work.OROneRel.exists_treeGauge

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- **The level window `[lo,hi]`** as a set of integers. -/
def levelWindow (lo hi : ℤ) : Set ℤ := {x | lo ≤ x ∧ x ≤ hi}

@[simp] theorem mem_levelWindow {lo hi x : ℤ} :
    x ∈ levelWindow lo hi ↔ lo ≤ x ∧ x ≤ hi := Iff.rfl

/-- The source level of the decorated head letter `((p.1,·),p.2)` read at running level `i` is
`i`: the level stored in the decoration is `i` for a positive letter and `i - c p.1` for a negative
one, and `coverSrc` compensates for the negative case. -/
theorem coverSrc_head_decor (c : α → ℤ) (i : ℤ) (p : α × Bool) :
    coverSrc c ((p.1, if p.2 then i else i - c p.1), p.2) = i := by
  obtain ⟨a, b⟩ := p
  cases b <;> simp [coverSrc]

/-- The target level of the decorated head letter read at running level `i` is `i + linc c p`. -/
theorem coverTgt_head_decor (c : α → ℤ) (i : ℤ) (p : α × Bool) :
    coverTgt c ((p.1, if p.2 then i else i - c p.1), p.2) = i + linc c p := by
  obtain ⟨a, b⟩ := p
  cases b <;> simp [coverTgt, linc, sub_eq_add_neg]

/-- **The running levels of a walk whose decorated edges lie in the window stay in the window.**

If the walk of `L` is started at a level `i` of the window, and every decorated letter of `L` has
both its endpoints in the window, then every running level `i + lsig c (L.take k)`
(`0 ≤ k ≤ L.length`) lies in the window. -/
private theorem band_aux (c : α → ℤ) (lo hi : ℤ) :
    ∀ (L : List (α × Bool)) (i : ℤ), i ∈ levelWindow lo hi →
      (∀ q ∈ decor c i L, coverSrc c q ∈ levelWindow lo hi ∧
        coverTgt c q ∈ levelWindow lo hi) →
      ∀ k, k ≤ L.length → (i + lsig c (L.take k)) ∈ levelWindow lo hi := by
  intro L
  induction L with
  | nil =>
      intro i hi_mem hdec k hk
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst hk0
      simpa [lsig] using hi_mem
  | cons p L' ih =>
      intro i hi_mem hdec k hk
      simp only [List.length_cons] at hk
      have hcons := decor_cons' c i p L'
      have hq : ((p.1, if p.2 then i else i - c p.1), p.2) ∈ decor c i (p :: L') := by
        rw [hcons]; exact List.mem_cons_self ..
      have hqW := hdec _ hq
      have htgt := coverTgt_head_decor c i p
      have hi'_mem : i + linc c p ∈ levelWindow lo hi := by
        rw [← htgt]; exact hqW.2
      have hdec' : ∀ q ∈ decor c (i + linc c p) L', coverSrc c q ∈ levelWindow lo hi ∧
          coverTgt c q ∈ levelWindow lo hi := by
        intro q hq'
        exact hdec q (by rw [hcons]; exact List.mem_cons_of_mem _ hq')
      rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simpa [lsig] using hi_mem
      · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
        have hk' : k' ≤ L'.length := by omega
        have hih := ih (i + linc c p) hi'_mem hdec' k' hk'
        have htake : (p :: L').take (k' + 1) = p :: L'.take k' := List.take_succ_cons ..
        rw [htake, lsig_cons']
        rw [show i + (linc c p + lsig c (L'.take k')) = (i + linc c p) + lsig c (L'.take k')
            from by ring]
        exact hih

theorem band_of_winE_decor {α : Type u} (c : α → ℤ) (lo hi : ℤ) (L : List (α × Bool))
    (hne : L ≠ [])
    (h : ∀ q ∈ Work.OROneRel.decor c 0 L,
      Work.OROneRel.coverEdge q ∈ Work.OROneRel.winE c lo hi) :
    Work.OROneRel.band c lo hi L := by
  -- every decorated letter has both endpoints in the window
  have hW : ∀ q ∈ decor c 0 L, coverSrc c q ∈ levelWindow lo hi ∧
      coverTgt c q ∈ levelWindow lo hi := by
    intro q hq
    have h1 := (coverEdge_mem_winE_iff c lo hi q).mp (h q hq)
    rw [mem_levelWindow]
    exact ⟨⟨h1.1, h1.2.1⟩, ⟨h1.2.2.1, h1.2.2.2⟩⟩
  obtain ⟨p, L', rfl⟩ := List.exists_cons_of_ne_nil hne
  -- the starting level `0` is the source of the first decorated letter, hence in the window
  have h0mem : (0 : ℤ) ∈ levelWindow lo hi := by
    have hcons := decor_cons' c 0 p L'
    have hq : ((p.1, if p.2 then (0 : ℤ) else (0 : ℤ) - c p.1), p.2) ∈
        decor c 0 (p :: L') := by
      rw [hcons]; exact List.mem_cons_self ..
    have hsrc := coverSrc_head_decor c 0 p
    have key := (hW _ hq).1
    rwa [hsrc] at key
  intro k hk
  have hk' := band_aux c lo hi (p :: L') 0 h0mem hW k hk
  simpa using hk'

end Work.OROneRel
