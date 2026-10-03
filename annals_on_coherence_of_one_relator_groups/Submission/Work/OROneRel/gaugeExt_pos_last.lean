import Mathlib
import Submission.Work.OROneRel.globalGauge
import Submission.Work.OROneRel.gaugeExtWalkDefs
import Submission.Work.OROneRel.exists_treeGauge

/-!
# Above the band, the reduced word of the global gauge ends in `a`

For `c = tlW p q` (`a = 0 ↦ q`, `b = 1 ↦ -p`), a *band* gauge `Wt` (`cohom c (Wt i) = ofAdd i` for
all `i`, and `htree`: the walk of `Wt i` for `0 ≤ i ≤ pq` runs through edges of the band whose loop
class vanishes) and the global gauge `G = gaugeExt p q hq Wt` of
`Submission/Work/OROneRel/globalGauge.lean`, the target of this file is

  `(wordOf (G j)).getLast? = some ((0 : Fin 2), true)`   for all `j > pq`,

i.e. **above the band the reduced word of the global gauge ends in the letter `a`**.  This is the
`getLast?` input of the last-letter computations for the `b`-edges above the band
(`Work.OROneRel.gaugeExt_bedge_gt`).

## The two ingredients

* `band_last_ne_aInv_aux`: **on the top slice `(pq - q, pq]` of the band the reduced word of `Wt w`
  does not end in `a⁻¹`.**  If it did, the last decorated letter of
  `decor (tlW p q) 0 (wordOf (Wt w))` would be the `a⁻¹`-traversal of the edge `(0,w)` -- the level
  component of a decorated letter is its *target* level, which is the total weight `w` of the word,
  by `hcoh` -- and `htree` puts that edge in the band, so that both of its endpoints lie in `[0,pq]`;
  but its far endpoint is `w + q > pq`.

* `gPosL_reduced`: **for `j > pq` the chain word `gPosL j` is reduced and ends in `a`.**  Both hold
  by strong recursion on the level (`Int.strongRec`, following the recursion of `gPosL` itself): the
  chain at `j` is the chain at `j - q`, or the band word `wordOf (Wt (j - q))` when `j - q` is back
  in the band, followed by a single forward `a`.  The appended `a` cannot cancel with the last letter
  `a⁻¹` of the inner word: on the band this is `band_last_ne_aInv_aux` (there `j - q ∈ (pq - q, pq]`),
  and above the band the inner chain already ends in `a`.

Finally, for `j > pq` the global gauge *is* the upper chain (`gaugeExtL` selects `gPosL` above the
band), and a reduced word is its own reduction (`wordOf_mk_of_isReduced`), so the last letter of
`wordOf (G j)` is the last letter of `gPosL j`, namely `a`.
-/

namespace Work.OROneRel

noncomputable section

/-! ## The last letter of a band word on the top slice -/

/-- The weight of a band word is its level: `cohom (tlW p q) (Wt t) = ofAdd t` says exactly that
`lsig (tlW p q) (wordOf (Wt t)) = t`. -/
private theorem lsig_wordOf_Wt {p q : ℕ} {Wt : ℤ → FreeGroup (Fin 2)}
    (hcoh : ∀ i : ℤ, cohom (tlW p q) (Wt i) = Multiplicative.ofAdd i) (t : ℤ) :
    lsig (tlW p q) (wordOf (Wt t)) = t := by
  rw [lsig_wordOf (tlW p q) (Wt t), hcoh t]
  rfl

/-- **On the top slice `(pq - q, pq]` of the band, no band word ends in `a⁻¹`.**

Suppose `wordOf (Wt w)` ends in the letter `(0,false) = a⁻¹`.  The total weight of the word is `w`
(`hcoh`), so the weight of its prefix is `w + q`; hence the *last* decorated letter of
`decor (tlW p q) 0 (wordOf (Wt w))` is `(((0 : Fin 2), w), false)`, the `a⁻¹`-traversal of the edge
`(0,w)`.  By `htree` that edge lies in the band `winE (tlW p q) 0 (pq)`, whose fourth condition reads
`w + q ≤ pq` -- against `w > pq - q`. -/
theorem band_last_ne_aInv_aux {p q : ℕ} (hq : 1 ≤ q) {Wt : ℤ → FreeGroup (Fin 2)}
    (hcoh : ∀ i : ℤ, cohom (tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ npq p q →
      ∀ e ∈ decor (tlW p q) 0 (wordOf (Wt i)),
        coverEdge e ∈ winTree Wt (tlW p q) 0 (npq p q))
    {w : ℤ} (hw0 : 0 ≤ w) (hw1 : w ≤ npq p q) (hw2 : npq p q - (q : ℤ) < w) :
    (wordOf (Wt w)).getLast? ≠ some ((0 : Fin 2), false) := by
  intro hlast
  have htl0 : tlW p q (0 : Fin 2) = (q : ℤ) := by simp [tlW]
  -- the total weight of the band word is its level
  have hsig : lsig (tlW p q) (wordOf (Wt w)) = w := lsig_wordOf_Wt hcoh w
  -- split off the last letter
  obtain ⟨L', hL'⟩ := List.getLast?_eq_some_iff.mp hlast
  -- the prefix has weight `w + q`
  have hsig' : lsig (tlW p q) L' = w + (q : ℤ) := by
    have h := hsig
    rw [hL', lsig_append, lsig_singleton_false, htl0] at h
    linarith
  -- the last decorated letter is the decoration of the last letter
  have hdecor : (decor (tlW p q) 0 (wordOf (Wt w))).getLast? = some ((((0 : Fin 2), w), false)) := by
    rw [hL', decor_append, hsig']
    have hsingle : decor (tlW p q) (0 + (w + (q : ℤ))) [((0 : Fin 2), false)] =
        [(((0 : Fin 2), w), false)] := by
      show [(((0 : Fin 2), 0 + (w + (q : ℤ)) - tlW p q (0 : Fin 2)), false)] = _
      rw [htl0, show (0 : ℤ) + (w + (q : ℤ)) - (q : ℤ) = w from by ring]
    rw [hsingle, List.getLast?_concat]
  -- so it is one of the decorated letters of the band word
  have hmem : ((((0 : Fin 2), w), false)) ∈ decor (tlW p q) 0 (wordOf (Wt w)) :=
    List.mem_of_mem_getLast? (Option.mem_def.mpr hdecor)
  -- `htree` puts its edge in the band, whose fourth condition bounds its far endpoint by `pq`
  have hwin : ((0 : Fin 2), w) ∈ winE (tlW p q) 0 (npq p q) := by
    have h := htree w hw0 hw1 ((((0 : Fin 2), w), false)) hmem
    rw [mem_winTree] at h
    exact h.1
  obtain ⟨-, -, -, h4⟩ := mem_winE.mp hwin
  rw [htl0] at h4
  omega

/-! ## The upper chain is reduced and ends in `a` -/

/-- **For `j > pq` the chain word `gPosL j` is reduced and ends in `a`.**

Strong recursion on the level (`Int.strongRec`), following the two branches of the recursion of
`gPosL`: the chain at `j` is the chain at `j - q`, or the band word `wordOf (Wt (j - q))` when
`j - q` is back in the band, followed by a single forward `a`.  The appended `a` cannot cancel with
the last letter `a⁻¹` of the inner word: on the band this is `hlast` (there `j - q ∈ (pq - q, pq]`),
and above the band the inner chain already ends in `a`. -/
theorem gPosL_reduced {p q : ℕ} {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)}
    (hlast : ∀ w : ℤ, npq p q - (q : ℤ) < w → w ≤ npq p q →
      (wordOf (Wt w)).getLast? ≠ some ((0 : Fin 2), false))
    {j : ℤ} (hj : npq p q < j) :
    FreeGroup.IsReduced (gPosL p q hq Wt j) ∧
      (gPosL p q hq Wt j).getLast? = some ((0 : Fin 2), true) := by
  have key : ∀ i : ℤ, npq p q < i →
      FreeGroup.IsReduced (gPosL p q hq Wt i) ∧
        (gPosL p q hq Wt i).getLast? = some ((0 : Fin 2), true) := by
    intro i
    refine Int.strongRec (m := npq p q + 1)
      (motive := fun i => npq p q < i →
        FreeGroup.IsReduced (gPosL p q hq Wt i) ∧
          (gPosL p q hq Wt i).getLast? = some ((0 : Fin 2), true)) ?_ ?_ i
    · intro n hn hni
      omega
    · intro n _ ih hni
      have hstep := gPosL_eq (p := p) (q := q) (hq := hq) (Wt := Wt) n
      by_cases hcase : n - (q : ℤ) ≤ npq p q
      · -- the level `n - q` is back in the band: the chain is a band word followed by `a`
        rw [hstep, if_pos hcase]
        have hred : FreeGroup.IsReduced (wordOf (Wt (n - (q : ℤ)))) := by
          rw [wordOf_eq_toWord_inst]
          exact FreeGroup.isReduced_toWord
        refine ⟨FreeGroup.IsReduced.append_singleton' hred ?_, List.getLast?_concat⟩
        intro r hr hcon
        have hr' : (wordOf (Wt (n - (q : ℤ)))).getLast? = some r := Option.mem_def.mp hr
        rw [show r = ((0 : Fin 2), false) from Prod.ext hcon.1 hcon.2] at hr'
        exact hlast (n - (q : ℤ)) (by omega) hcase hr'
      · -- the level `n - q` is still above the band: descend one step
        rw [hstep, if_neg hcase]
        have hgt : npq p q < n - (q : ℤ) := by omega
        obtain ⟨hred, hgl⟩ := ih (n - (q : ℤ)) (by omega) hgt
        refine ⟨FreeGroup.IsReduced.append_singleton' hred ?_, List.getLast?_concat⟩
        intro r hr hcon
        have hr' : (gPosL p q hq Wt (n - (q : ℤ))).getLast? = some r := Option.mem_def.mp hr
        rw [hgl] at hr'
        have hrt : ((0 : Fin 2), true) = r := (Option.some.injEq _ _).mp hr'
        rw [← hrt] at hcon
        exact absurd hcon.2 (by decide)
  exact key j hj

end

/-! ## The target -/

theorem gaugeExt_pos_last {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) {Wt : ℤ → FreeGroup (Fin 2)}
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ Work.OROneRel.npq p q →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 (Work.OROneRel.npq p q)) :
    ∀ j : ℤ, Work.OROneRel.npq p q < j →
      (Work.OROneRel.wordOf (Work.OROneRel.gaugeExt p q hq Wt j)).getLast? =
        some ((0 : Fin 2), true) := by
  intro j hj
  -- the band last-letter fact, on the slice `(pq - q, pq]` of the band
  have hlast : ∀ w : ℤ, npq p q - (q : ℤ) < w → w ≤ npq p q →
      (wordOf (Wt w)).getLast? ≠ some ((0 : Fin 2), false) := by
    intro w hw2 hw1
    have hq0 : (0 : ℤ) ≤ npq p q - (q : ℤ) := npq_sub_q_nonneg (p := p) (q := q) hp
    exact band_last_ne_aInv_aux hq hcoh htree (by omega) hw1 hw2
  obtain ⟨hred, hgl⟩ := gPosL_reduced (p := p) (q := q) hlast hj
  -- above the band the global gauge is the upper chain
  have hL : gaugeExtL p q hq Wt j = gPosL p q hq Wt j := by
    have hnpq0 : (0 : ℤ) ≤ npq p q := npq_nonneg (p := p) (q := q)
    rw [gaugeExtL, dif_neg (by rintro ⟨-, h2⟩; omega : ¬ (0 ≤ j ∧ j ≤ npq p q)),
      dif_neg (by omega : ¬ j < 0)]
  rw [gaugeExt, hL, wordOf_mk_of_isReduced hred, hgl]

end Work.OROneRel
