import Mathlib
import Submission.Work.OROneRel.globalGauge
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.gaugeExt_pos_last
import Submission.Work.OROneRel.last_true_le
import Submission.Work.OROneRel.exists_treeGauge

/-!
# The `b`-edges above the band have non-trivial loop class (two-letter case)

For `c = tlW p q` (`a = 0 ↦ q`, `b = 1 ↦ -p`), the band window `[0,pq]` and a band gauge `Wt`, the
global gauge `G = gaugeExt p q hq Wt` of `Submission/Work/OROneRel/globalGauge.lean` extends `Wt` to
all of `ℤ` by the two `a`-chains.  This file proves that the `b`-edges `(1,j)` with `j > pq` have
*non-trivial* loop class under the global gauge:

  `coverClassAt G (tlW p q) (1,j) ≠ 1`     (`j > pq`).

This is the input `hbgt` of `Work.OROneRel.trivTree_sub`
(`Submission/Work/OROneRel/globalGaugeProps.lean`): it is one of the two facts identifying the
trivial loop classes of the global gauge with the `TallGlob` tree of the window chain.

## The argument

Abbreviate `G = gaugeExt p q hq Wt`.  Suppose the loop class vanished:
`G j * b * (G (j - p))⁻¹ = 1`, i.e. `G j * b = G (j - p)`.

* **Above the band the reduced word of `G` ends in `a`.**  For `j > pq` we have
  `G j = G (j - q) * a` (`gaugeExt_pos_step`), and the band base case `G (j - q) = Wt (j - q)`
  cannot end in `a⁻¹`: otherwise the last decorated letter would be the `a⁻¹`-traversal of the edge
  `(0, j - q)`, whose far endpoint `j` exceeds `pq`, contradicting `htree`.  Descending by `q`
  (strong recursion on `ℤ`, `Int.strongRec`) gives the claim `Work.OROneRel.gaugeExt_pos_last`.
* Hence `wordOf (G j * b) = wordOf (G j) ++ [b]`, so the left side of the equation ends in `b`.
* The right side does not: if `j - p > pq` its reduced word ends in `a` (`gaugeExt_pos_last`), and
  if `0 ≤ j - p ≤ pq` then `G (j - p) = Wt (j - p)`, whose reduced word cannot end in `b` — the last
  decorated letter would be the `b`-traversal of the edge `(1,j)`, and `htree` puts that edge in the
  band `[0,pq]`, forcing `j ≤ pq`.  That `getLast?` statement is `Work.OROneRel.last_true_le`.

The two facts about the *band* gauge are delegated to `Work.OROneRel.last_true_le` and (internally,
for the `a⁻¹` companion) `Work.OROneRel.gaugeExt_pos_last`; the assembly is below.
-/

namespace Work.OROneRel

universe u

/-- If the reduced word of `u` does not end in `a⁻¹`, then appending `a` concatenates the words.

This is the free-group list fact behind the last-letter computation of `gaugeExt_bedge_gt`: the
reduced word of `u * of a` is obtained by simply appending the letter `a` (read as `(a,true)`)
whenever no cancellation occurs. -/
theorem bedgeGt_wordOf_mul_pos {α : Type u} (u : FreeGroup α) (a : α)
    (h : (wordOf u).getLast? ≠ some (a, false)) :
    wordOf (u * FreeGroup.of a) = wordOf u ++ [(a, true)] := by
  have hred : FreeGroup.IsReduced (wordOf u) := by
    show FreeGroup.IsReduced (@FreeGroup.toWord α (Classical.decEq α) u)
    exact @FreeGroup.isReduced_toWord α (Classical.decEq α) u
  have hred2 : FreeGroup.IsReduced (wordOf u ++ [(a, true)]) :=
    FreeGroup.IsReduced.append_singleton' hred (fun q hq hc => by
      apply h
      have hq' : q = (a, false) := Prod.ext hc.1 hc.2
      rwa [hq'] at hq)
  have hmk : FreeGroup.mk (wordOf u ++ [(a, true)]) = u * FreeGroup.of a := by
    rw [mk_append_true, mk_wordOf]
  rw [← hmk]
  exact wordOf_mk_of_isReduced hred2

/-- **The `b`-edges above the band are not trivial.**  For `j > pq` the loop class of the edge
`(1,j)` of the level graph under the global gauge is non-trivial. -/
theorem gaugeExt_bedge_gt {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) {Wt : ℤ → FreeGroup (Fin 2)}
    (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ Work.OROneRel.npq p q →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 (Work.OROneRel.npq p q))
    {j : ℤ} (hj : Work.OROneRel.npq p q < j) :
    Work.OROneRel.coverClassAt (Work.OROneRel.gaugeExt p q hq Wt) (Work.OROneRel.tlW p q)
      ((1 : Fin 2), j) ≠ 1 := by
  intro hcon
  -- `(p : ℤ) ≤ pq`, so that `j - p ≥ 0` and hence `gaugeExt` agrees with `Wt` on the band there
  have hp_le : (p : ℤ) ≤ npq p q := by
    rw [npq]
    nlinarith [show (0 : ℤ) ≤ (p : ℤ) by positivity,
      show (1 : ℤ) ≤ (q : ℤ) by exact_mod_cast hq]
  -- the vanishing loop class rearranges to `G j * b = G (j - p)`
  have hmain : gaugeExt p q hq Wt j * FreeGroup.of (1 : Fin 2) =
      gaugeExt p q hq Wt (j - (p : ℤ)) := by
    simp only [coverClassAt, gaugeMap_of, show tlW p q (1 : Fin 2) = -(p : ℤ) from by simp [tlW],
      show j + -(p : ℤ) = j - (p : ℤ) from by ring] at hcon
    exact mul_inv_eq_one.mp hcon
  -- the reduced word of `G j` ends in `a`, so `wordOf (G j * b) = wordOf (G j) ++ [b]`
  have hpos := gaugeExt_pos_last (p := p) (q := q) hp hq hcoh htree j hj
  have hL : (wordOf (gaugeExt p q hq Wt j * FreeGroup.of (1 : Fin 2))).getLast? =
      some ((1 : Fin 2), true) := by
    rw [bedgeGt_wordOf_mul_pos _ _ (by rw [hpos]; exact by decide), List.getLast?_append,
      List.getLast?_singleton, Option.some_or]
  -- but the reduced word of `G (j - p)` does not end in `b`
  have hR : (wordOf (gaugeExt p q hq Wt (j - (p : ℤ)))).getLast? ≠
      some ((1 : Fin 2), true) := by
    by_cases hpj : j - (p : ℤ) ≤ npq p q
    · -- on the band: `G (j-p) = Wt (j-p)`, and `htree` forbids a final `b`
      rw [gaugeExt_of_band (p := p) (q := q) (hq := hq) (Wt := Wt) (by omega) hpj]
      intro hh
      have hle := last_true_le (p := p) (q := q) hp hq hcoh htree
        (i := j - (p : ℤ)) (by omega) hpj hh
      omega
    · -- above the band the reduced word ends in `a`
      have hgt : npq p q < j - (p : ℤ) := by omega
      have hlast := gaugeExt_pos_last (p := p) (q := q) hp hq hcoh htree (j - (p : ℤ)) hgt
      intro hh
      rw [hlast] at hh
      exact absurd hh (by decide)
  rw [congrArg wordOf hmain] at hL
  exact hR hL

end Work.OROneRel
