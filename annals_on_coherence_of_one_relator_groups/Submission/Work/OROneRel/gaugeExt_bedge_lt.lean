import Mathlib
import Submission.Work.OROneRel.globalGauge
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.gauge_band_last_not
import Submission.Work.OROneRel.gaugeExt_neg_wordOf

/-!
# The `b`-edges below the band have non-trivial loop class

Let `c = tlW p q` (`a ↦ q`, `b ↦ -p`) and let `gaugeExt` be the global gauge of
`Submission/Work/OROneRel/globalGauge.lean`: the band gauge `Wt` on the levels `[0, pq]`, extended
below the band by the descending chain `gNegL` and above it by the ascending chain `gPosL`; all the
`a`-edges of the two chains have trivial loop class.

Here we show that, for every level `j ≤ p - 1`, the loop class of the `b`-edge `(1, j)` is
non-trivial.  The edge `(1, j)` runs from the level `j` to the level `j - p < 0`:

* the level `j` is at or below `p - 1`, so the word of the gauge there ends *not* with `b⁻¹`
  (for `0 ≤ j ≤ p - 1` this is `gauge_band_last_not`: the last edge of the walk of `Wt j` would be
  `(1, j)`, whose target level `j - p` is negative; for `j < 0` the gauge word is the chain word
  `gNegL j`, which ends with `a⁻¹`);
* the level `j - p` is *below* the band, so the gauge word there is the chain word `gNegL (j - p)`,
  which ends with `a⁻¹` (`gaugeExt_neg_wordOf`);
* hence if the loop class `gaugeExt j * b * (gaugeExt (j - p))⁻¹` were `1`, the reduced word of the
  left hand side — which ends with `b` — would have to end with `a⁻¹`, a contradiction.
-/

namespace Work.OROneRel

noncomputable section

/-- The maximal reduction of words, at the classical `DecidableEq` instance — the instance that
`wordOf` is defined with, so that `FreeGroup.toWord` lemmas apply to `wordOf` verbatim. -/
private def redC (L : List (Fin 2 × Bool)) : List (Fin 2 × Bool) :=
  @FreeGroup.reduce (Fin 2) (Classical.decEq (Fin 2)) L

private lemma wordOf_mulC (x y : FreeGroup (Fin 2)) :
    wordOf (x * y) = redC (wordOf x ++ wordOf y) := by
  rw [Work.OROneRel.wordOf, Work.OROneRel.wordOf, Work.OROneRel.wordOf]
  exact @FreeGroup.toWord_mul (Fin 2) (Classical.decEq (Fin 2)) x y

private lemma wordOf_ofC (a : Fin 2) : wordOf (FreeGroup.of a) = [(a, true)] := by
  rw [Work.OROneRel.wordOf]
  exact @FreeGroup.toWord_of (Fin 2) (Classical.decEq (Fin 2)) a

private lemma isReduced_wordOfC (x : FreeGroup (Fin 2)) : FreeGroup.IsReduced (wordOf x) := by
  rw [Work.OROneRel.wordOf]
  exact @FreeGroup.isReduced_toWord (Fin 2) (Classical.decEq (Fin 2)) x

private lemma redC_eq_self {L : List (Fin 2 × Bool)} (h : FreeGroup.IsReduced L) : redC L = L := by
  unfold redC
  exact @FreeGroup.IsReduced.reduce_eq (Fin 2) L (Classical.decEq (Fin 2)) h

/-- Appending a letter to a reduced word keeps it reduced, provided the last letter is not the
inverse of the appended one. -/
private lemma isReduced_append_singleton {L : List (Fin 2 × Bool)} {c : Fin 2 × Bool}
    (h : FreeGroup.IsReduced L) (hlast : L.getLast? ≠ some (c.1, !c.2)) :
    FreeGroup.IsReduced (L ++ [c]) := by
  rw [FreeGroup.IsReduced, List.isChain_append]
  refine ⟨h, ?_, ?_⟩
  · exact FreeGroup.IsReduced.singleton
  · intro x hx y hy h1
    rw [List.head?_singleton, Option.mem_some_iff] at hy
    subst hy
    rcases hL : L.getLast? with _ | z
    · simp [hL] at hx
    · rw [hL, Option.mem_some_iff] at hx
      subst hx
      by_contra h2
      have h2' : z.2 = !c.2 := by revert h2; cases z.2 <;> cases c.2 <;> simp
      have hzeq : z = (c.1, !c.2) := Prod.ext h1 h2'
      exact hlast (by rw [hL, hzeq])

/-- **The word of the global gauge at a level `j ≤ p - 1` does not end with the inverse of `b`.** -/
private lemma gaugeExt_getLast_ne {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    {Wt : ℤ → FreeGroup (Fin 2)}
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ Work.OROneRel.npq p q →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 (Work.OROneRel.npq p q))
    {j : ℤ} (hj : j ≤ (p : ℤ) - 1) :
    (wordOf (gaugeExt p q hq Wt j)).getLast? ≠ some ((1 : Fin 2), false) := by
  by_cases hj0 : 0 ≤ j
  · -- `j` is in the band: this is the band last-letter fact
    have hjnpq : j ≤ npq p q := by
      have hp1 : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
      have hq1 : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
      have hppq : (p : ℤ) ≤ npq p q := by
        have : (p : ℤ) * 1 ≤ (p : ℤ) * (q : ℤ) := mul_le_mul_of_nonneg_left hq1 (by linarith)
        simpa [npq] using this
      linarith
    rw [gaugeExt_of_band (p := p) (q := q) (hq := hq) (Wt := Wt) hj0 hjnpq]
    exact (gauge_band_last_not hcoh htree hj0 hjnpq).2 (by omega)
  · -- `j` is below the band: the gauge word is the chain word, which ends with `a⁻¹`
    have hj0' : j < 0 := not_le.mp hj0
    rw [(gaugeExt_neg_wordOf hp hq hcoh htree hj0').1,
      (gaugeExt_neg_wordOf hp hq hcoh htree hj0').2]
    simp

theorem gaugeExt_bedge_lt {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) {Wt : ℤ → FreeGroup (Fin 2)}
    (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ Work.OROneRel.npq p q →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 (Work.OROneRel.npq p q))
    {j : ℤ} (hj : j ≤ (p : ℤ) - 1) :
    Work.OROneRel.coverClassAt (Work.OROneRel.gaugeExt p q hq Wt) (Work.OROneRel.tlW p q)
      ((1 : Fin 2), j) ≠ 1 := by
  intro hcon
  -- the loop class of `(1,j)` is `gaugeExt j * b * (gaugeExt (j-p))⁻¹`
  rw [coverClassAt, gaugeMap_of] at hcon
  have htl : tlW p q (1 : Fin 2) = -(p : ℤ) := by simp [tlW]
  rw [htl, ← sub_eq_add_neg] at hcon
  have h1 : gaugeExt p q hq Wt j * FreeGroup.of (1 : Fin 2) =
      gaugeExt p q hq Wt (j - (p : ℤ)) :=
    mul_inv_eq_one.mp hcon
  -- the two words to compare
  have hjp : j - (p : ℤ) < 0 := by omega
  have hlastR : (wordOf (gaugeExt p q hq Wt (j - (p : ℤ)))).getLast? =
      some ((0 : Fin 2), false) := by
    rw [(gaugeExt_neg_wordOf hp hq hcoh htree hjp).1,
      (gaugeExt_neg_wordOf hp hq hcoh htree hjp).2]
  have hlastL : (wordOf (gaugeExt p q hq Wt j * FreeGroup.of (1 : Fin 2))).getLast? =
      some ((1 : Fin 2), true) := by
    rw [wordOf_mulC, wordOf_ofC,
      redC_eq_self (isReduced_append_singleton (isReduced_wordOfC _)
        (gaugeExt_getLast_ne hp hq hcoh htree hj))]
    exact List.getLast?_concat
  have h2 : (wordOf (gaugeExt p q hq Wt j * FreeGroup.of (1 : Fin 2))).getLast? =
      (wordOf (gaugeExt p q hq Wt (j - (p : ℤ)))).getLast? := by rw [h1]
  rw [hlastL, hlastR] at h2
  exact absurd h2 (by decide)

end

end Work.OROneRel
