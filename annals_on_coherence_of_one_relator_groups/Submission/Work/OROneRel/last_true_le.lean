import Mathlib
import Submission.Work.OROneRel.globalGauge

namespace Work.OROneRel

/-!
# The last letter `b` of a band gauge word forces the level up by `p`

Let `c = tlW p q` (`a = 0 ↦ q`, `b = 1 ↦ -p`) and let `Wt : ℤ → FreeGroup (Fin 2)` be a *band gauge*:
`cohom c (Wt i) = ofAdd i` for all `i`, and every decorated letter of `wordOf (Wt i)` for
`i ∈ [0, pq]` traverses an edge of the tree of the window `[0, pq]` (`htree`).

If the reduced word of the band gauge element at the level `i ∈ [0, pq]` *ends* with the positive
letter `b = (1, true)` -- i.e. `(wordOf (Wt i)).getLast? = some (1, true)` -- then reading that last
letter runs from level `i + p` down to `i` (its weight is `c 1 = -p`), so the edge `(1, i+p)` it
traverses must be an edge of the window `[0, pq]` by `htree`, forcing `i + p ≤ pq`.

This is one of the two "last letter" facts on which the reducedness of the window chains rests (see
`Submission/Work/OROneRel/gauge_band_last_not.lean` for the companion statements).
-/

/-- The decoration of a singleton positive letter: it is decorated at the level at which it is read. -/
theorem decor_singleton_true {α : Type*} (c : α → ℤ) (i : ℤ) (x : α) :
    decor c i ([(x, true)] : List (α × Bool)) = [((x, i), true)] := by
  rw [show ([(x, true)] : List (α × Bool)) = (x, true) :: [] from rfl, decor]
  rfl

/-- **The edge of the last decorated letter.**  If the last letter of the word `w` is the positive
letter `x`, then the last decorated letter of `decor c v w` traverses the edge
`(x, v + lsig c w - c x)`: the level at which `x` is read is the level reached at the end of the word
minus its own weight `c x`. -/
theorem exists_mem_decor_coverEdge_getLast_true {α : Type*} (c : α → ℤ) (v : ℤ)
    {w : List (α × Bool)} {x : α} (h : w.getLast? = some (x, true)) :
    ∃ a ∈ decor c v w, coverEdge a = (x, v + lsig c w - c x) := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp h
  refine ⟨((x, v + lsig c ys), true), ?_, ?_⟩
  · rw [decor_append, decor_singleton_true]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · simp only [coverEdge]
    congr 1
    rw [lsig_append, lsig_singleton_true]
    ring

theorem last_true_le {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) {Wt : ℤ → FreeGroup (Fin 2)}
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ Work.OROneRel.npq p q →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 (Work.OROneRel.npq p q))
    {i : ℤ} (hi1 : 0 ≤ i) (hi2 : i ≤ Work.OROneRel.npq p q)
    (h : (Work.OROneRel.wordOf (Wt i)).getLast? = some ((1 : Fin 2), true)) :
    i + (p : ℤ) ≤ Work.OROneRel.npq p q := by
  -- `hp`, `hq` are part of the interface (they are not needed for this last-letter bound).
  have _hp : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  have _hq : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  -- The weight of the reduced word of `Wt i` is `i`.
  have hlsig : lsig (tlW p q) (wordOf (Wt i)) = i := by
    rw [lsig_wordOf, hcoh i]
    rfl
  -- The last decorated letter traverses the edge `(1, i + p)`.
  obtain ⟨a, ha, hcov⟩ := exists_mem_decor_coverEdge_getLast_true (tlW p q) 0 h
  -- `htree` places that edge in the tree of the window `[0, pq]`, hence in the window.
  have ht := htree i hi1 hi2 a ha
  rw [mem_winTree] at ht
  have htE : coverEdge a ∈ winE (tlW p q) 0 (npq p q) := ht.1
  rw [mem_winE] at htE
  have hcov2 : (coverEdge a).2 = i + (p : ℤ) := by
    have htlw1 : tlW p q (1 : Fin 2) = -(p : ℤ) := by simp [tlW]
    rw [hcov, hlsig, htlw1]
    ring
  rw [← hcov2]
  exact htE.2.1

end Work.OROneRel
