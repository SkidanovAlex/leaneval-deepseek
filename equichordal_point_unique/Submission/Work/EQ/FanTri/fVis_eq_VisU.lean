import Mathlib
import Submission.Work.EQ.FanTri.fan_split_defs

namespace Work.EQ.FanTri

open Work.EQ

/-- The level state `fLvl ε k` of `Base.lean` is the `k`-th reversed state of the walk read
along the reversed word: reading the last `k` letters of `ε` (i.e. the first `k` letters of
`ε.reverse`) leaves the walk in state `fLvl ε k`. -/
theorem fLvl_eq_wstate (ε : List Bool) (k : ℕ) :
    Work.EQ.fLvl ε k = wstate ε.reverse (ε.length - k) := by
  unfold Work.EQ.fLvl wstate
  rw [List.reverse_drop]

/-- `fVis` (counting the levels `k < |ε|` with nonzero state, level `k` being the suffix
`ε.drop k`) agrees with `VisU` of the reversed word (counting the times `t ∈ [1,|ε|]` at which
the walk along the prefix `ε.reverse.take t` is nonzero): the substitution `t = |ε| - k` is a
bijection `{0,…,|ε|-1} ≃ {1,…,|ε|}`. -/
theorem fVis_eq_VisU (ε : List Bool) : Work.EQ.fVis ε = Work.EQ.FanTri.VisU ε.reverse := by
  rw [Work.EQ.fVis, Work.EQ.FanTri.VisU, List.length_reverse]
  refine Finset.card_bij (fun k _ => ε.length - k) ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_filter] at hk ⊢
    obtain ⟨hkrange, hkne⟩ := hk
    rw [Finset.mem_range] at hkrange
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_Icc]; omega
    · rw [← fLvl_eq_wstate]; exact hkne
  · intro k1 h1 k2 h2 h
    rw [Finset.mem_filter] at h1 h2
    rw [Finset.mem_range] at h1 h2
    omega
  · intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨hbmem, hbne⟩ := hb
    rw [Finset.mem_Icc] at hbmem
    obtain ⟨hb1, hb2⟩ := hbmem
    refine ⟨ε.length - b, ?_, by omega⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    have hb' : ε.length - (ε.length - b) = b := by omega
    rw [fLvl_eq_wstate, hb']
    exact hbne

end Work.EQ.FanTri
