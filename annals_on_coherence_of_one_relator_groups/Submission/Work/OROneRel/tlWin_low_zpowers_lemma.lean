import Mathlib
import Submission.Work.OROneRel.band_hnnConjMap_injective
import Submission.Work.OROneRel.bandWinDefs
import Submission.Work.OROneRel.bandLoopsDefs
import Submission.Work.OROneRel.tlLowCycStep
import Submission.Work.OROneRel.tlLowCyc_cycWord_mem
import Submission.Work.OROneRel.tlLowCyc_reduced_bool
import Submission.Work.OROneRel.tlLowCyc_fwd_prefix
import Submission.Work.OROneRel.tlLowCyc_bwd_prefix
import Submission.Work.OROneRel.tlLowCyc_prefix_pow

/-!
# The low window `[0, p+q-1]` of the two-letter band is cyclic

For the two-letter weight `tlW p q` (`a ↦ q`, `b ↦ -p`) the window `[0, p+q-1]` of the level graph
is a single cycle through its `p+q` levels: at every level exactly one positive traversal (the
letter `cycGen i`) and one negative traversal (the letter `cycGen (cycPred i)`) lie in the window,
and they are the two traversals of the *same* edge of the cycle.  Consequently a *reduced* word
whose decorated walk stays in the window is either a forward or a backward run along the cycle
(`tlLowCyc_reduced_bool`, `tlLowCyc_fwd_prefix`, `tlLowCyc_bwd_prefix`), and since the loop
condition `lsig (tlW p q) · = 0` forces the run length to be a multiple of `p+q`, its class is a
power of the cycle word `cycWord p q` (`tlLowCyc_prefix_pow`).

Hence `tlWin p q ((p:ℤ)+(q:ℤ)-1) = Subgroup.zpowers (cycWord p q)`.

The group `tlWin p q m` is the closure of the set of elements spelled by a word of weight `0` whose
decorated walk lies in `winE (tlW p q) 0 m` (`band_hnnConjMap_injective.lean`); by
`mem_loopsInE_iff` that set is exactly the carrier of `loopsInE (tlW p q) (winE (tlW p q) 0 m)`, so
the two subgroups coincide (`tlWin_eq_loopsInE` below), which is the form in which membership is
used.
-/

namespace Work.OROneRel

/-- **The gauge-free window subgroup is the loop subgroup of the window edge set.**  The closure of
the set of elements spelled by a weight-`0` word all of whose decorated edges lie in the window
`winE (tlW p q) 0 m` is the loop subgroup `loopsInE (tlW p q) (winE (tlW p q) 0 m)`. -/
theorem tlWin_eq_loopsInE (p q : ℕ) (m : ℤ) :
    tlWin p q m = loopsInE (tlW p q) (winE (tlW p q) 0 m) := by
  unfold tlWin
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    intro x hx
    exact (mem_loopsInE_iff (tlW p q) (winE (tlW p q) 0 m) x).mpr hx
  · intro x hx
    exact Subgroup.subset_closure ((mem_loopsInE_iff (tlW p q) (winE (tlW p q) 0 m) x).mp hx)

theorem tlWin_low_zpowers_lemma (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q) :
    ∃ w : FreeGroup (Fin 2), Work.OROneRel.tlWin p q ((p : ℤ) + (q : ℤ) - 1) = Subgroup.zpowers w := by
  refine ⟨cycWord p q, le_antisymm ?_ ?_⟩
  · -- every loop of the low window is a power of the cycle word
    rw [tlWin_eq_loopsInE]
    rintro x ⟨hcoh, hwalk⟩
    have hred : FreeGroup.IsReduced (wordOf x) := tlLow_wordOf_isReduced x
    have hwin : ∀ e ∈ decor (tlW p q) (cycLevel p q 0) (wordOf x),
        coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) + (q : ℤ) - 1) := by
      intro e he
      rw [cycLevel_zero] at he
      exact hwalk e he
    have hlsig : lsig (tlW p q) (wordOf x) = 0 := by
      rw [lsig_wordOf, hcoh]
      rfl
    rcases tlLowCyc_reduced_bool p q hp hq 0 (wordOf x) hred hwin with htrue | hfalse
    · -- a forward run along the cycle
      have hshape := tlLowCyc_fwd_prefix p q hp hq 0 (wordOf x) htrue hwin
      have hlev : cycLevel p q ((wordOf x).length : ℤ) = 0 := by
        have h := lsig_cycFwdList p q hp hq 0 (wordOf x).length
        rw [← hshape] at h
        rw [hlsig] at h
        rw [cycLevel_zero, zero_add, sub_zero] at h
        exact h.symm
      obtain ⟨c, hc⟩ := (cycLevel_eq_zero_iff_dvd_nat (p := p) (q := q) hp hcop).mp hlev
      have hx : x = cycWord p q ^ c := by
        have h1 : x = FreeGroup.mk (cycFwdList p q 0 ((p + q) * c)) := by
          rw [← mk_wordOf x, hshape, hc]
        rw [h1, (tlLowCyc_prefix_pow p q c).1]
      exact Subgroup.mem_zpowers_iff.mpr ⟨(c : ℤ), by rw [zpow_natCast]; exact hx.symm⟩
    · -- a backward run along the cycle
      have hshape := tlLowCyc_bwd_prefix p q hp hq 0 (wordOf x) hfalse hwin
      have hlev : cycLevel p q (-((wordOf x).length : ℤ)) = 0 := by
        have h := lsig_cycBwdList p q hp hq 0 (wordOf x).length
        rw [← hshape] at h
        rw [hlsig] at h
        rw [zero_sub, cycLevel_zero, sub_zero] at h
        exact h.symm
      obtain ⟨c, hc⟩ := (cycLevel_eq_zero_iff_dvd_nat_neg (p := p) (q := q) hp hcop).mp hlev
      have hx : x = cycWord p q ^ (-(c : ℤ)) := by
        have h1 : x = FreeGroup.mk (cycBwdList p q 0 ((p + q) * c)) := by
          rw [← mk_wordOf x, hshape, hc]
        rw [h1, (tlLowCyc_prefix_pow p q c).2]
      exact Subgroup.mem_zpowers_iff.mpr ⟨-(c : ℤ), hx.symm⟩
  · -- the cycle word itself is a loop of the low window
    exact Subgroup.zpowers_le.mpr (tlLowCyc_cycWord_mem p q hp hq)

end Work.OROneRel
