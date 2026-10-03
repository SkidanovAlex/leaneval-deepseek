import Mathlib
import Submission.Work.OROneRel.globalGauge

namespace Work.OROneRel

theorem lsig_gPosL {p q : ℕ} {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)}
    (hl : ∀ t : ℤ, Work.OROneRel.lsig (Work.OROneRel.tlW p q) (Work.OROneRel.wordOf (Wt t)) = t) :
    ∀ i : ℤ, Work.OROneRel.npq p q < i →
      Work.OROneRel.lsig (Work.OROneRel.tlW p q) (Work.OROneRel.gPosL p q hq Wt i) = i := by
  -- The `a`-letter `(0,true)` has weight `q`.
  have htl0 : tlW p q (0 : Fin 2) = (q : ℤ) := by simp [tlW]
  -- Strong recursion on the level, above the threshold `npq p q`.
  intro n
  refine Int.strongRec (m := npq p q + 1)
    (motive := fun i => npq p q < i →
      lsig (tlW p q) (gPosL p q hq Wt i) = i) ?_ ?_ n
  · -- levels below the threshold are not above the band
    intro k hk hgt
    omega
  · intro k _ ih hgt
    by_cases hcase : k - (q : ℤ) ≤ npq p q
    · -- the chain has returned to the band: it is the band word at `k - q` plus one `a`
      have hbase : gPosL p q hq Wt k =
          wordOf (Wt (k - (q : ℤ))) ++ [((0 : Fin 2), true)] := by
        have h := gPosL_base (p := p) (q := q) (hq := hq) (Wt := Wt) (i := k - (q : ℤ)) hcase
        rwa [sub_add_cancel] at h
      rw [hbase, lsig_append, hl (k - (q : ℤ)), lsig_singleton_true, htl0]
      omega
    · -- still above the band: one recursion step
      have hgt' : npq p q < k - (q : ℤ) := by omega
      have hstep : gPosL p q hq Wt k =
          gPosL p q hq Wt (k - (q : ℤ)) ++ [((0 : Fin 2), true)] :=
        gPosL_above (p := p) (q := q) (hq := hq) (Wt := Wt) (i := k) (by omega)
      rw [hstep, lsig_append, ih (k - (q : ℤ)) (by omega) hgt', lsig_singleton_true, htl0]
      omega

end Work.OROneRel
