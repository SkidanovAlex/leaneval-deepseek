import Mathlib
import Submission.Work.OROneRel.globalGauge
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.exists_treeGauge
import Submission.Work.OROneRel.winBandDefs
import Submission.Work.OROneRel.cohom_mk

/-!
# The last letter of a band gauge word is a *short* step

Let `c = tlW p q` (`a ↦ q`, `b ↦ -p`) and let `Wt` be a gauge for `c` on the band `[0, pq]`:
`cohom c (Wt i) = ofAdd i` for every `i`, and every edge traversed by the walk of `Wt i`
(`0 ≤ i ≤ pq`) has trivial loop class (`htree`), i.e. lies in the tree `winTree Wt c 0 (pq)` of the
window.

The walk of `Wt w` visits the levels `0, …, w` (`lsig c (wordOf (Wt w)) = w`, from `hcoh`), and
every edge it traverses lies in the window `[0, pq]` — in particular, both endpoints of every
traversed edge are non-negative.  Reading the last letter `g` of `wordOf (Wt w)` at the running
level `lsig c (wordOf (Wt w)).dropLast`, this forces the increment `linc c g` of that last letter
to be at most `w`:

* if `g = (x, true)` is a positive letter, the decorated edge is `(x, lsig c L')` where `L'` is
  `wordOf (Wt w)` without its last letter, and `w = lsig c L' + c x` with `0 ≤ lsig c L'`;
* if `g = (x, false)` is a negative letter, the decorated edge is `(x, lsig c L' - c x)` and
  `w = lsig c L' - c x` with `0 ≤ lsig c L'`.

Specialising to `g = a = (0, true)` (`linc c g = q`) gives `w ≥ q`, and to `g = b⁻¹ = (1, false)`
(`linc c g = p`) gives `w ≥ p`.  Hence a word of the band gauge at a level `w < q` does not end in
`a`, and one at a level `w < p` does not end in `b⁻¹`.  These are exactly the two last-letter facts
that make the chains `gPosL` / `gNegL` of `Submission/Work/OROneRel/globalGauge.lean` reduced
(compare the notes at the end of that file).
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The source level of the letter decorating a single letter `(x, b)` read at running level `i` is
`i`. -/
theorem coverSrc_dec_single {c : α → ℤ} (i : ℤ) (p : α × Bool) :
    Work.OROneRel.coverSrc c ((p.1, if p.2 then i else i - c p.1), p.2) = i := by
  obtain ⟨x, b⟩ := p
  cases b
  · show i - c x + c x = i
    ring
  · rfl

/-- **The weight of a word representing an element of level `i` is `i`.**  Immediate from the
list-level description of `cohom` (`cohom_mk`) and `mk_wordOf`. -/
theorem lsig_wordOf_of_cohom {c : α → ℤ} {u : FreeGroup α} {i : ℤ}
    (h : Work.OROneRel.cohom c u = Multiplicative.ofAdd i) :
    Work.OROneRel.lsig c (wordOf u) = i := by
  have h1 := cohom_mk c (wordOf u)
  rw [mk_wordOf, h] at h1
  have h2 := congrArg Multiplicative.toAdd h1
  simpa using h2.symm

/-- **The last step of a band gauge word is short.**  If the last letter `g` of `wordOf (Wt w)` is
read at the running level `lsig (tlW p q) (wordOf (Wt w)).dropLast`, then the level increment
`linc (tlW p q) g` of that letter is at most `w`.

The proof: the last decorated letter of `decor (tlW p q) 0 (wordOf (Wt w))` is the decoration of `g`
at level `lsig (tlW p q) L'` (`L'` = the word with its last letter deleted); by `htree` its edge
lies in `winTree ⊆ winE`, so its *source* level `lsig (tlW p q) L'` is non-negative; and
`w = lsig (tlW p q) L' + linc (tlW p q) g` since `lsig` is additive over `L' ++ [g]`. -/
theorem linc_le_of_getLast {p q : ℕ} {Wt : ℤ → FreeGroup (Fin 2)}
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) =
      Multiplicative.ofAdd i)
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ Work.OROneRel.npq p q →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 (Work.OROneRel.npq p q))
    {w : ℤ} (h0 : 0 ≤ w) (hw : w ≤ Work.OROneRel.npq p q) {g : Fin 2 × Bool}
    (hl : (Work.OROneRel.wordOf (Wt w)).getLast? = some g) :
    Work.OROneRel.linc (Work.OROneRel.tlW p q) g ≤ w := by
  obtain ⟨L', hL'⟩ := List.getLast?_eq_some_iff.mp hl
  -- the last decorated letter of the walk of `wordOf (Wt w)`
  have hdecor : Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt w)) =
      Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 L' ++
        [((g.1,
            if g.2 then Work.OROneRel.lsig (Work.OROneRel.tlW p q) L'
            else Work.OROneRel.lsig (Work.OROneRel.tlW p q) L' - Work.OROneRel.tlW p q g.1),
          g.2)] := by
    rw [hL', Work.OROneRel.decor_append', zero_add,
      Work.OROneRel.decor_singleton']
  have hmem : ((g.1,
        if g.2 then Work.OROneRel.lsig (Work.OROneRel.tlW p q) L'
        else Work.OROneRel.lsig (Work.OROneRel.tlW p q) L' - Work.OROneRel.tlW p q g.1), g.2) ∈
      Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt w)) := by
    rw [hdecor]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  -- its edge lies in the window `[0, pq]`, hence its source level is non-negative
  have hwin : Work.OROneRel.coverEdge
        ((g.1,
          if g.2 then Work.OROneRel.lsig (Work.OROneRel.tlW p q) L'
          else Work.OROneRel.lsig (Work.OROneRel.tlW p q) L' - Work.OROneRel.tlW p q g.1), g.2) ∈
      Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 (Work.OROneRel.npq p q) :=
    (Work.OROneRel.mem_winTree.mp (htree w h0 hw _ hmem)).1
  have hsrc : 0 ≤ Work.OROneRel.lsig (Work.OROneRel.tlW p q) L' := by
    have h1 := (Work.OROneRel.coverEdge_mem_winE_iff (Work.OROneRel.tlW p q) 0
      (Work.OROneRel.npq p q)
      ((g.1,
        if g.2 then Work.OROneRel.lsig (Work.OROneRel.tlW p q) L'
        else Work.OROneRel.lsig (Work.OROneRel.tlW p q) L' - Work.OROneRel.tlW p q g.1), g.2)).mp
      hwin
    have h2 := h1.1
    rwa [coverSrc_dec_single] at h2
  -- and the total weight is the source level plus the increment of `g`
  have hlsig : Work.OROneRel.lsig (Work.OROneRel.tlW p q) (Work.OROneRel.wordOf (Wt w)) = w :=
    lsig_wordOf_of_cohom (hcoh w)
  have hsum : w = Work.OROneRel.lsig (Work.OROneRel.tlW p q) L' +
      Work.OROneRel.linc (Work.OROneRel.tlW p q) g := by
    rw [← hlsig, hL', Work.OROneRel.lsig_append', Work.OROneRel.lsig_singleton']
  omega

theorem gauge_band_last_not {p q : ℕ} {Wt : ℤ → FreeGroup (Fin 2)}
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ Work.OROneRel.npq p q →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 (Work.OROneRel.npq p q))
    {w : ℤ} (h0 : 0 ≤ w) (hw : w ≤ Work.OROneRel.npq p q) :
    (w < (q : ℤ) → (Work.OROneRel.wordOf (Wt w)).getLast? ≠ some ((0 : Fin 2), true)) ∧
    (w < (p : ℤ) → (Work.OROneRel.wordOf (Wt w)).getLast? ≠ some ((1 : Fin 2), false)) := by
  constructor
  · intro hwq hlast
    have h := linc_le_of_getLast (p := p) (q := q) hcoh htree h0 hw hlast
    rw [show Work.OROneRel.linc (Work.OROneRel.tlW p q) ((0 : Fin 2), true) = (q : ℤ) from by
      simp [Work.OROneRel.linc, Work.OROneRel.tlW]] at h
    omega
  · intro hwp hlast
    have h := linc_le_of_getLast (p := p) (q := q) hcoh htree h0 hw hlast
    rw [show Work.OROneRel.linc (Work.OROneRel.tlW p q) ((1 : Fin 2), false) = (p : ℤ) from by
      simp [Work.OROneRel.linc, Work.OROneRel.tlW]] at h
    omega

end Work.OROneRel
