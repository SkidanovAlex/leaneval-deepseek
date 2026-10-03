import Mathlib
import Submission.Work.OROneRel.globalGauge
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.gaugeExtWalkDefs
import Submission.Work.OROneRel.decor_winE_of_red
import Submission.Work.OROneRel.walkTriv_gNegL
import Submission.Work.OROneRel.walkTriv_gPosL

/-!
# The walks of the global gauge traverse only edges of trivial loop class

`gaugeExt p q hq Wt` extends a band gauge `Wt` of the level graph of `c = tlW p q` to all of `ℤ` by
the two `a`-chains of `globalGauge.lean`.  Here we prove that **every** edge traversed by the walk
of `gaugeExt j` has trivial loop class *with respect to `gaugeExt` itself* -- the `hwalk` input
advertised at the bottom of `globalGauge.lean`:

* for a band level `0 ≤ j ≤ pq` the walk of `gaugeExt j = Wt j` lies in the band by `htree`, and on
  the band the two gauges agree (`coverClassAt_gaugeExt_eq`), so the classes are `1`;
* for a chain level the walk is a band word followed by a chain of `a`-edges, and the `a`-edges
  outside the band are trivial (`coverClassAt_aedge_pos`, `coverClassAt_aedge_neg`); this is the
  content of `walkTriv_gNegL` / `walkTriv_gPosL`;
* finally `wordOf (gaugeExt j)` is the reduction of the explicit chain word `gaugeExtL j`, so its
  traversals are a sublist of the traversals of `gaugeExtL j` (`decor_sublist_of_red`).
-/

namespace Work.OROneRel

theorem gaugeExt_hwalk {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) {Wt : ℤ → FreeGroup (Fin 2)}
    (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ Work.OROneRel.npq p q →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 (Work.OROneRel.npq p q)) :
    ∀ j : ℤ, ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.wordOf (Work.OROneRel.gaugeExt p q hq Wt j)),
      Work.OROneRel.coverClassAt (Work.OROneRel.gaugeExt p q hq Wt) (Work.OROneRel.tlW p q)
        (Work.OROneRel.coverEdge e) = 1 := by
  -- the band words of `Wt` have total weight the level, by the coherence hypothesis `hcoh`
  have hl : ∀ t : ℤ, Work.OROneRel.lsig (Work.OROneRel.tlW p q) (Work.OROneRel.wordOf (Wt t)) = t := by
    intro t
    have h1 : Work.OROneRel.cohom (Work.OROneRel.tlW p q) (FreeGroup.mk (Work.OROneRel.wordOf (Wt t))) =
        Multiplicative.ofAdd (Work.OROneRel.lsig (Work.OROneRel.tlW p q) (Work.OROneRel.wordOf (Wt t))) :=
      Work.OROneRel.cohom_mk _ _
    rw [Work.OROneRel.mk_wordOf, hcoh t] at h1
    exact Multiplicative.ofAdd.injective h1.symm
  intro j e he
  -- the explicit chain word `gaugeExtL j` is a trivial walk
  have hroot : Work.OROneRel.walkTriv (Work.OROneRel.gaugeExt p q hq Wt)
      (Work.OROneRel.tlW p q) 0 (Work.OROneRel.gaugeExtL p q hq Wt j) := by
    rw [Work.OROneRel.gaugeExtL]
    by_cases h : 0 ≤ j ∧ j ≤ Work.OROneRel.npq p q
    · rw [dif_pos h]
      exact Work.OROneRel.walkTriv_band hp htree h.1 h.2
    · rw [dif_neg h]
      by_cases h2 : j < 0
      · rw [dif_pos h2]
        exact (Work.OROneRel.walkTriv_gNegL hp htree hl j h2).2
      · rw [dif_neg h2]
        exact (Work.OROneRel.walkTriv_gPosL hp htree hl j (by omega)).2
  -- the reduced word of `gaugeExt j` traverses a sublist of those edges
  have hred : FreeGroup.Red (Work.OROneRel.gaugeExtL p q hq Wt j)
      (Work.OROneRel.wordOf (Work.OROneRel.gaugeExt p q hq Wt j)) := by
    rw [Work.OROneRel.wordOf_gaugeExt_reduce]
    exact FreeGroup.reduce.red
  exact Work.OROneRel.walkTriv_of_red hred hroot e he

end Work.OROneRel
