import Mathlib
import Submission.Work.OROneRel.globalGauge
import Submission.Work.OROneRel.decor_winE_of_red

/-!
# Walking along the global gauge: the vocabulary of `gaugeExt_hwalk`

For the two-letter data `c = tlW p q` (`a ↦ q`, `b ↦ -p`) and a gauge `G : ℤ → FreeGroup (Fin 2)`
we say that a list `L` is a *trivial walk* from the level `lvl` if every decorated traversal of `L`
(started at level `lvl`) traverses an edge of trivial loop class:

  `walkTriv G c lvl L  ↔  ∀ p ∈ decor c lvl L, coverClassAt G c (coverEdge p) = 1`.

The content of this file is the bookkeeping that lets one build trivial walks from trivial walks:
additivity under concatenation (`walkTriv_append`), the two `a`-edges of the chains
(`walkTriv_single_zero_false`, `walkTriv_single_zero_true`), the band words
(`walkTriv_band`, from the hypothesis `htree`), the passage to the reduced word
(`walkTriv_of_red`), and finally the two `a`-chains themselves
(`walkTriv_gNegL`, `walkTriv_gPosL`).
-/

namespace Work.OROneRel

noncomputable section

/-- **Trivial walks.**  Every traversal of the word `L`, read from the level `lvl` in the `ℤ`-cover
of the weight `c`, traverses an edge whose loop class under the gauge `G` is trivial. -/
def walkTriv (G : ℤ → FreeGroup (Fin 2)) (c : Fin 2 → ℤ) (lvl : ℤ) (L : List (Fin 2 × Bool)) : Prop :=
  ∀ p ∈ decor c lvl L, coverClassAt G c (coverEdge p) = 1

/-- **Trivial walks are additive under concatenation.**  The decoration of a concatenation is the
concatenation of the decorations, the second one started at the level reached at the end of the
first. -/
theorem walkTriv_append (G : ℤ → FreeGroup (Fin 2)) (c : Fin 2 → ℤ) (lvl : ℤ)
    (L M : List (Fin 2 × Bool)) :
    walkTriv G c lvl (L ++ M) ↔
      walkTriv G c lvl L ∧ walkTriv G c (lvl + lsig c L) M := by
  unfold walkTriv
  rw [decor_append]
  constructor
  · intro h
    exact ⟨fun p hp => h p (List.mem_append_left _ hp),
      fun p hp => h p (List.mem_append_right _ hp)⟩
  · rintro ⟨h1, h2⟩ p hp
    rcases List.mem_append.mp hp with h | h
    · exact h1 p h
    · exact h2 p h

/-- **The last `a`-edge of the lower chain is trivial.**  A single backward letter `a` read at a
level `lvl` traverses the edge `(0, lvl - q)`, which is trivial as soon as `lvl - q < 0`. -/
theorem walkTriv_single_zero_false {p q : ℕ} (hp : 1 ≤ p) {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)}
    {lvl : ℤ} (h : lvl - tlW p q (0 : Fin 2) < 0) :
    walkTriv (gaugeExt p q hq Wt) (tlW p q) lvl [((0 : Fin 2), false)] := by
  intro e he
  rw [show decor (tlW p q) lvl [((0 : Fin 2), false)]
      = [(((0 : Fin 2), lvl - tlW p q (0 : Fin 2)), false)] from rfl] at he
  rw [List.mem_singleton] at he
  subst he
  exact coverClassAt_aedge_neg (p := p) (q := q) hp (Wt := Wt) h

/-- **The last `a`-edge of the upper chain is trivial.**  A single forward letter `a` read at a
level `lvl > pq - q` traverses the edge `(0, lvl)`, which is trivial. -/
theorem walkTriv_single_zero_true {p q : ℕ} (hp : 1 ≤ p) {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)}
    {lvl : ℤ} (h : npq p q - (q : ℤ) < lvl) :
    walkTriv (gaugeExt p q hq Wt) (tlW p q) lvl [((0 : Fin 2), true)] := by
  intro e he
  rw [show decor (tlW p q) lvl [((0 : Fin 2), true)] = [(((0 : Fin 2), lvl), true)] from rfl] at he
  rw [List.mem_singleton] at he
  subst he
  exact coverClassAt_aedge_pos (p := p) (q := q) hp (Wt := Wt) h

/-- **The loop class of an edge of the band is the same for `Wt` and for `gaugeExt`**: both
endpoints of the edge lie in `[0, pq]`, where the two gauges agree. -/
theorem coverClassAt_gaugeExt_eq {p q : ℕ} {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)}
    {e : Fin 2 × ℤ} (h1 : 0 ≤ e.2) (h2 : e.2 + tlW p q e.1 ≤ npq p q)
    (h3 : 0 ≤ e.2 + tlW p q e.1) (h4 : e.2 ≤ npq p q) :
    coverClassAt (gaugeExt p q hq Wt) (tlW p q) e = coverClassAt Wt (tlW p q) e := by
  obtain ⟨x, j⟩ := e
  simp only [coverClassAt, gaugeMap_of]
  rw [gaugeExt_of_band (p := p) (q := q) (hq := hq) (Wt := Wt) h1 h4,
    gaugeExt_of_band (p := p) (q := q) (hq := hq) (Wt := Wt) h3 h2]

/-- **The band words are trivial walks.**  This is the hypothesis `htree`: the walk of `Wt i` for
`i ∈ [0, pq]` runs through edges of the band of trivial loop class, and on the band the gauge
`gaugeExt` agrees with `Wt`. -/
theorem walkTriv_band {p q : ℕ} (hp : 1 ≤ p) {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)}
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ npq p q →
      ∀ e ∈ decor (tlW p q) 0 (wordOf (Wt i)),
        coverEdge e ∈ winTree Wt (tlW p q) 0 (npq p q))
    {i : ℤ} (h0 : 0 ≤ i) (h1 : i ≤ npq p q) :
    walkTriv (gaugeExt p q hq Wt) (tlW p q) 0 (wordOf (Wt i)) := by
  intro e he
  have htw := htree i h0 h1 e he
  rw [mem_winTree] at htw
  obtain ⟨hE, hcl⟩ := htw
  rw [mem_winE] at hE
  obtain ⟨ha, hb, hc, hd⟩ := hE
  rw [coverClassAt_gaugeExt_eq (p := p) (q := q) (hq := hq) (Wt := Wt) ha hd hc hb, hcl]

/-- `wordOf` is `FreeGroup.toWord` at the ambient (arbitrary) decidable equality: the resulting
*list* does not depend on the instance. -/
theorem wordOf_eq_toWord_inst {α : Type} [DecidableEq α] (r : FreeGroup α) :
    wordOf r = r.toWord := by
  have h1 : FreeGroup.IsReduced (wordOf r) :=
    @FreeGroup.isReduced_toWord α (Classical.decEq α) r
  have h2 : FreeGroup.IsReduced r.toWord := FreeGroup.isReduced_toWord
  have h3 : FreeGroup.mk (wordOf r) = r := mk_wordOf r
  have h4 : FreeGroup.mk r.toWord = r := FreeGroup.mk_toWord
  have h5 : FreeGroup.reduce (wordOf r) = FreeGroup.reduce r.toWord :=
    FreeGroup.reduce.sound (by rw [h3, h4])
  rw [FreeGroup.IsReduced.reduce_eq h1, FreeGroup.IsReduced.reduce_eq h2] at h5
  exact h5

/-- The word of the global gauge is the reduction of the explicit chain word. -/
theorem wordOf_gaugeExt_reduce (p q : ℕ) (hq : 1 ≤ q) (Wt : ℤ → FreeGroup (Fin 2)) (j : ℤ) :
    wordOf (gaugeExt p q hq Wt j) = FreeGroup.reduce (gaugeExtL p q hq Wt j) := by
  rw [wordOf_eq_toWord_inst]
  exact FreeGroup.toWord_mk

/-- **Trivial walks survive reduction.**  If every traversal of `L` is trivial, then so is every
traversal of the reduced word of `L`. -/
theorem walkTriv_of_red {p q : ℕ} {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)}
    {L₁ L₂ : List (Fin 2 × Bool)}
    (h : FreeGroup.Red L₁ L₂)
    (hL : walkTriv (gaugeExt p q hq Wt) (tlW p q) 0 L₁) :
    walkTriv (gaugeExt p q hq Wt) (tlW p q) 0 L₂ := by
  intro e he
  exact hL e (List.Sublist.mem he (decor_sublist_of_red (tlW p q) 0 h))

end

end Work.OROneRel
