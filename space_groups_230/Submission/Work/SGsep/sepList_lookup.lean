import Mathlib
import Submission.Work.SG.SGsepDefs

namespace Work.SGsep

open Work.SG

/-- `(k, l)` with `k < 230`, `l < 230`, `k < l` and `repClass k = repClass l` belongs to the
explicit list `Data.sameClassPairs` of same-class pairs (smaller index first). -/
private lemma mem_sameClassPairs {k l : ℕ} (hk : k < 230) (hl : l < 230) (hkl : k < l)
    (hc : Data.repClass k = Data.repClass l) : (k, l) ∈ Data.sameClassPairs := by
  rw [Data.sameClassPairs]
  simp only [List.mem_flatMap, List.mem_range, List.mem_map]
  refine ⟨k, hk, l, ?_, rfl⟩
  simp only [List.mem_filter, List.mem_range]
  refine ⟨hl, ?_⟩
  simp [hkl, hc]

/-- Looking up a separation certificate: for every same-class pair `k < l` of representatives
(in the sense `Data.repClass k = Data.repClass l`, `k,l < 230`), the separation list contains
an entry whose key is `(k,l)` and which passes `Data.Sep.chk`.  From `Data.sepList_cover`
(`sepList.map Sep.kl = sameClassPairs`) and `Data.sepList_chk` (`sepList.all Sep.chk = true`),
using the explicit definition of `Data.sameClassPairs`. -/
theorem sepList_lookup {k l : ℕ} (hk : k < 230) (hl : l < 230) (hkl : k < l)
    (hc : Data.repClass k = Data.repClass l) :
    ∃ e ∈ Data.sepList, Data.Sep.kl e = (k, l) ∧ Data.Sep.chk e = true := by
  have h1 : (k, l) ∈ Data.sepList.map Data.Sep.kl := by
    rw [Data.sepList_cover]
    exact mem_sameClassPairs hk hl hkl hc
  rw [List.mem_map] at h1
  obtain ⟨e, he, hkey⟩ := h1
  exact ⟨e, he, hkey, (List.all_eq_true.mp Data.sepList_chk) e he⟩

end Work.SGsep
