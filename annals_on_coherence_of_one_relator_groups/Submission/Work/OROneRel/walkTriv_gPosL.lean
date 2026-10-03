import Mathlib
import Submission.Work.OROneRel.gaugeExtWalkDefs

namespace Work.OROneRel

/-- **The upper `a`-chain of the global gauge is a trivial walk, and its weight is the level.**

For `i > pq` the chain word `gPosL i` is the band word `wordOf (Wt (i - q))` followed by a single
forward `a`, if the level `i - q` is back in the band; otherwise it is the chain at the level `i - q`
followed by a forward `a`.  In both cases the weight of the chain is `i` (the band word contributes
`i - q`, the `a` contributes `q`), and every traversal runs through a trivial edge: the band word is
a trivial walk by `htree` (`walkTriv_band`), and the new `a`-edge sits at a level `> pq - q`
(`walkTriv_single_zero_true`). -/
theorem walkTriv_gPosL {p q : ℕ} (hp : 1 ≤ p) {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)}
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ Work.OROneRel.npq p q →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 (Work.OROneRel.npq p q))
    (hl : ∀ t : ℤ, Work.OROneRel.lsig (Work.OROneRel.tlW p q) (Work.OROneRel.wordOf (Wt t)) = t) :
    ∀ i : ℤ, Work.OROneRel.npq p q < i →
      Work.OROneRel.lsig (Work.OROneRel.tlW p q) (Work.OROneRel.gPosL p q hq Wt i) = i ∧
      Work.OROneRel.walkTriv (Work.OROneRel.gaugeExt p q hq Wt) (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.gPosL p q hq Wt i) := by
  have hqpos : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hqp : (q : ℤ) ≤ npq p q := q_le_npq (p := p) (q := q) hp
  have htl0 : tlW p q (0 : Fin 2) = (q : ℤ) := by simp [tlW]
  have key : ∀ i : ℤ, npq p q < i →
      lsig (tlW p q) (gPosL p q hq Wt i) = i ∧
      walkTriv (gaugeExt p q hq Wt) (tlW p q) 0 (gPosL p q hq Wt i) := by
    intro i
    refine Int.strongRec (m := npq p q + 1) (motive := fun i => npq p q < i →
        lsig (tlW p q) (gPosL p q hq Wt i) = i ∧
        walkTriv (gaugeExt p q hq Wt) (tlW p q) 0 (gPosL p q hq Wt i)) ?_ ?_ i
    · -- levels below the threshold cannot exceed the band
      intro n hn hlt
      omega
    · -- a level above the band
      intro n _ ih hni
      by_cases hcase : n - (q : ℤ) ≤ npq p q
      · -- the level `n - q` is back in the band: the chain is a band word plus one `a`
        have hbase : gPosL p q hq Wt n = wordOf (Wt (n - (q : ℤ))) ++ [((0 : Fin 2), true)] := by
          have h := gPosL_base (p := p) (q := q) (hq := hq) (Wt := Wt) (i := n - (q : ℤ)) hcase
          rwa [sub_add_cancel] at h
        have h0 : 0 ≤ n - (q : ℤ) := by omega
        refine ⟨?_, ?_⟩
        · rw [hbase, lsig_append, hl (n - (q : ℤ)), lsig_singleton_true, htl0]
          ring
        · rw [hbase, walkTriv_append]
          refine ⟨walkTriv_band (p := p) (q := q) hp (hq := hq) (Wt := Wt) htree h0 hcase, ?_⟩
          rw [zero_add, hl (n - (q : ℤ))]
          exact walkTriv_single_zero_true (p := p) (q := q) hp (Wt := Wt) (by omega)
      · -- the level `n - q` is still above the band: descend one step
        have hgt : npq p q < n - (q : ℤ) := by omega
        have hstep : gPosL p q hq Wt n =
            gPosL p q hq Wt (n - (q : ℤ)) ++ [((0 : Fin 2), true)] :=
          gPosL_above (p := p) (q := q) (hq := hq) (Wt := Wt) (i := n) (by omega)
        obtain ⟨hls, hwt⟩ := ih (n - (q : ℤ)) (by omega) hgt
        refine ⟨?_, ?_⟩
        · rw [hstep, lsig_append, hls, lsig_singleton_true, htl0]
          ring
        · rw [hstep, walkTriv_append]
          refine ⟨hwt, ?_⟩
          rw [zero_add, hls]
          exact walkTriv_single_zero_true (p := p) (q := q) hp (Wt := Wt) (by omega)
  exact key

end Work.OROneRel
