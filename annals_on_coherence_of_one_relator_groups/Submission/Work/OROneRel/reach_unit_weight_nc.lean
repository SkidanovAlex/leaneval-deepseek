-- **Namespaced copy** (`Work.OROneRel.NC`) of a colleague's module, made so that the
-- window-data pipeline can be imported *together with* the Freiheitssatz pipeline:
-- `Work.OROneRel.decor_replicate_true` (declared in `Submission.Work.OROneRel.decor_wordOf_zpow_of`)
-- clashes with the declaration of the same name in
-- `Submission.Work.OROneRel.twoLetter_cycle_decor`, so no module can import both
-- `exists_window_support_data_cycred` and `bandFreiheitssatz_of_windowData`.  The copy lives in
-- the namespace `Work.OROneRel.NC`, where `decor_replicate_true` is `Work.OROneRel.NC.decor_replicate_true`
-- and no longer clashes.  Nothing here is new mathematics.
import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.decor_wordOf_zpow_of_nc

namespace Work.OROneRel.NC

universe u

/-- **The unit-weight case of the window reachability.**  Let `z` be a generator whose weight is
`±1`, and let `0` and `j` be levels of the window (`lo ≤ 0 ≤ hi`, `lo ≤ j ≤ hi`).  Then the level `j`
is reached from `0` by the word `w = of z ^ (j * c z)`: reading `(z,true)` raises the level by `c z`
and reading `(z,false)` lowers it by `c z`, so its walk runs monotonically from `0` to `j`.  Every
traversed edge therefore has both endpoints between `0` and `j`, hence in `[lo,hi]`.  (Careful: the
edge of a decorated *negative* letter `((z, i - c z), false)` is `(z, i - c z)`, whose endpoints are
`i - c z` and `i`; it is a window edge as soon as those two levels are, which is what `winE` says.) -/
theorem reach_unit_weight {α : Type u} [DecidableEq α] (c : α → ℤ) (z : α) (lo hi j : ℤ)
    (hz : c z = 1 ∨ c z = -1) (h0lo : lo ≤ 0) (h0hi : 0 ≤ hi) (hloj : lo ≤ j) (hjhi : j ≤ hi) :
    ∃ w : FreeGroup α, Work.OROneRel.cohom c w = Multiplicative.ofAdd j ∧
      ∀ q ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf w),
        Work.OROneRel.coverEdge q ∈ Work.OROneRel.winE c lo hi := by
  classical
  refine ⟨FreeGroup.of z ^ (j * c z), ?_, ?_⟩
  · -- `cohom c (of z ^ (j * c z)) = (ofAdd (c z)) ^ (j * c z) = ofAdd ((j * c z) * c z) = ofAdd j`
    rw [map_zpow, Work.OROneRel.cohom_of, ← ofAdd_zsmul, zsmul_eq_mul, Int.cast_id]
    congr 1
    rcases hz with h | h <;> rw [h] <;> ring
  · -- the walk of `of z ^ (j * c z)` runs monotonically from `0` to `j`
    intro q hq
    rw [decor_wordOf_zpow_of] at hq
    have key : ∀ v : ℤ, min 0 j ≤ v → v ≤ max 0 j → lo ≤ v ∧ v ≤ hi := by
      intro v hv1 hv2
      exact ⟨le_trans (le_min h0lo hloj) hv1, le_trans hv2 (max_le h0hi hjhi)⟩
    have hb : q.1.1 = z ∧ min 0 j ≤ q.1.2 ∧ q.1.2 ≤ max 0 j ∧
        min 0 j ≤ q.1.2 + c z ∧ q.1.2 + c z ≤ max 0 j := by
      by_cases hn : 0 ≤ j * c z
      · -- positive branch: the levels are `k * c z` (`0 ≤ k ≤ (j * c z).toNat`) and its successor
        rw [if_pos hn] at hq
        rw [List.mem_map] at hq
        obtain ⟨k, hk, hqk⟩ := hq
        have hklt : (k : ℤ) < j * c z := by
          have h1 : k < (j * c z).toNat := List.mem_range.mp hk
          have h2 : (k : ℤ) < ((j * c z).toNat : ℤ) := by exact_mod_cast h1
          rwa [Int.toNat_of_nonneg hn] at h2
        clear hk
        rw [← hqk]
        rcases hz with hz | hz
        · rw [hz] at hklt hn ⊢
          simp only [mul_one] at hklt hn ⊢
          refine ⟨trivial, ?_, ?_, ?_, ?_⟩ <;> omega
        · rw [hz] at hklt hn ⊢
          simp only [mul_neg, mul_one] at hklt hn ⊢
          refine ⟨trivial, ?_, ?_, ?_, ?_⟩ <;> omega
      · -- negative branch: the levels are `-((k + 1) * c z)` and `-(k * c z)`
        rw [if_neg hn] at hq
        rw [List.mem_map] at hq
        obtain ⟨k, hk, hqk⟩ := hq
        have hklt : (k : ℤ) < -(j * c z) := by
          have h1 : k < (-(j * c z)).toNat := List.mem_range.mp hk
          have h2 : (k : ℤ) < ((-(j * c z)).toNat : ℤ) := by exact_mod_cast h1
          rwa [Int.toNat_of_nonneg (by omega)] at h2
        clear hk
        rw [← hqk]
        rcases hz with hz | hz
        · rw [hz] at hklt hn ⊢
          simp only [mul_one] at hklt hn ⊢
          refine ⟨trivial, ?_, ?_, ?_, ?_⟩ <;> omega
        · rw [hz] at hklt hn ⊢
          simp only [mul_neg, mul_one] at hklt hn ⊢
          refine ⟨trivial, ?_, ?_, ?_, ?_⟩ <;> omega
    obtain ⟨hq1, hb1, hb2, hb3, hb4⟩ := hb
    rw [coverEdge, mem_winE, hq1]
    exact ⟨(key _ hb1 hb2).1, (key _ hb1 hb2).2, (key _ hb3 hb4).1, (key _ hb3 hb4).2⟩

end Work.OROneRel.NC
