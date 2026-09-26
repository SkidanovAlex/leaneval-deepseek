import Mathlib
import Submission.Work.SG.SGsepDefs

namespace Work.SGsep

open Work.SG

/-- The pair `(k, l)` of a same-class pair with equal affine index lies in the filtered
`Data.sameClassPairs` list: `k` (resp. `l`) is in `List.range 230` by `hk` (resp. `hl`), the
`Bool` conjunction `k < l && repClass k == repClass l` is true by `hkl` and `hc`, and the
filter predicate `affIdx k == affIdx l` is true by `ha`. -/
private theorem sameClassPairs_filter_mem {k l : ℕ} (hk : k < 230) (hl : l < 230) (hkl : k < l)
    (hc : Data.repClass k = Data.repClass l) (ha : Data.affIdx k = Data.affIdx l) :
    (k, l) ∈ Data.sameClassPairs.filter (fun p => Data.affIdx p.1 == Data.affIdx p.2) := by
  rw [Data.sameClassPairs, List.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [List.mem_flatMap]
    refine ⟨k, by simp [List.mem_range, hk], ?_⟩
    rw [List.mem_map]
    refine ⟨l, ?_, rfl⟩
    rw [List.mem_filter]
    exact ⟨by simp [List.mem_range, hl], by simp [hkl, hc]⟩
  · exact beq_iff_eq.mpr ha

/-- Looking up an enantiomorphic merge: if `k < l` are representatives of the same arithmetic
class (`Data.repClass k = Data.repClass l`) with the same affine index
(`Data.affIdx k = Data.affIdx l`), then `Data.mergeList` contains an entry `(k, c)` whose
certificate targets `l` (`c.k = l`).  From `Data.mergeList_chk`
(`mergeList.map (fun p => (p.1, p.2.k)) = sameClassPairs.filter (fun p => affIdx p.1 == affIdx p.2)`)
and the explicit definition of `Data.sameClassPairs` (which lists the smaller index first). -/
theorem mergeList_lookup {k l : ℕ} (hk : k < 230) (hl : l < 230) (hkl : k < l)
    (hc : Data.repClass k = Data.repClass l) (ha : Data.affIdx k = Data.affIdx l) :
    ∃ c : Data.ConjCert, (k, c) ∈ Data.mergeList ∧ c.k = l := by
  have hmap := Data.mergeList_chk.1
  have hmem := sameClassPairs_filter_mem hk hl hkl hc ha
  rw [← hmap, List.mem_map] at hmem
  rcases hmem with ⟨⟨kp, c⟩, hp, hpe⟩
  simp only [Prod.mk.injEq] at hpe
  exact ⟨c, by rw [← hpe.1]; exact hp, hpe.2⟩

end Work.SGsep
