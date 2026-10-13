import Mathlib
import Submission.Work.WilE7.DecompDefs

namespace Work.WilE7

/-- In `Fin (m+1)` there is no index strictly between `j.castSucc` and `j.succ`. -/
theorem not_between_castSucc_succ {m : ℕ} {j : Fin m} {k : Fin (m+1)}
    (h1 : j.castSucc < k) (h2 : k < j.succ) : False :=
  (not_le_of_gt h1) (Fin.le_castSucc_iff.mpr h2)

/-- Two members of the cell family `cfs C s` that share a point are equal: the family
consists of pairwise disjoint pieces (the graphs of the levels and the open bands
between them). -/
theorem decomp_cell_eq_of_mem {n q : ℕ} {C : Set (Fin n → ℝ)} {s : Fin q → (Fin n → ℝ) → ℝ}
    (hmono : ∀ x ∈ C, StrictMono fun j : Fin q => s j x)
    (hbnd : ∀ x ∈ C, ∀ j, |s j x| < 1)
    {κ κ' : Set (Fin (n+1) → ℝ)} (hκ : κ ∈ cfs C s) (hκ' : κ' ∈ cfs C s)
    {z : Fin (n+1) → ℝ} (hz : z ∈ κ) (hz' : z ∈ κ') : κ = κ' := by
  rw [mem_cfs] at hκ hκ'
  obtain ⟨i, rfl⟩ | ⟨i, rfl⟩ := hκ
  · obtain ⟨i', rfl⟩ | ⟨i', rfl⟩ := hκ'
    · -- graph of the level `i` against graph of the level `i'`
      rw [gr, Set.mem_ofPred_eq] at hz hz'
      have hL := strictMono_lvl (s := s) (x := Fin.init z) (hmono (Fin.init z) hz.1)
        (hbnd (Fin.init z) hz.1)
      have : i = i' := hL.injective (hz.2.symm.trans hz'.2)
      rw [this]
    · -- graph of the level `i` against the band `(i', i' + 1)`
      rw [gr, Set.mem_ofPred_eq] at hz
      rw [bd, Set.mem_ofPred_eq] at hz'
      obtain ⟨hx, hzeq⟩ := hz
      obtain ⟨-, h1, h2⟩ := hz'
      rw [hzeq] at h1 h2
      have hL := strictMono_lvl (s := s) (x := Fin.init z) (hmono (Fin.init z) hx)
        (hbnd (Fin.init z) hx)
      exact (not_between_castSucc_succ (hL.lt_iff_lt.mp h1) (hL.lt_iff_lt.mp h2)).elim
  · obtain ⟨i', rfl⟩ | ⟨i', rfl⟩ := hκ'
    · -- band `(i, i + 1)` against graph of the level `i'`
      rw [bd, Set.mem_ofPred_eq] at hz
      rw [gr, Set.mem_ofPred_eq] at hz'
      obtain ⟨hx, h1, h2⟩ := hz
      obtain ⟨-, hzeq⟩ := hz'
      rw [hzeq] at h1 h2
      have hL := strictMono_lvl (s := s) (x := Fin.init z) (hmono (Fin.init z) hx)
        (hbnd (Fin.init z) hx)
      exact (not_between_castSucc_succ (hL.lt_iff_lt.mp h1) (hL.lt_iff_lt.mp h2)).elim
    · -- band `(i, i + 1)` against band `(i', i' + 1)`
      rw [bd, Set.mem_ofPred_eq] at hz hz'
      obtain ⟨hx, h1, h2⟩ := hz
      obtain ⟨-, h1', h2'⟩ := hz'
      have hL := strictMono_lvl (s := s) (x := Fin.init z) (hmono (Fin.init z) hx)
        (hbnd (Fin.init z) hx)
      have : i = i' := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · have hs : i.succ ≤ i'.castSucc := Fin.succ_le_castSucc_iff.mpr hlt
          have hmono' := hL.monotone hs
          exact absurd (lt_of_lt_of_le h2 (le_trans hmono' (le_of_lt h1'))) (lt_irrefl _)
        · have hs : i'.succ ≤ i.castSucc := Fin.succ_le_castSucc_iff.mpr hlt
          have hmono' := hL.monotone hs
          exact absurd (lt_of_lt_of_le h2' (le_trans hmono' (le_of_lt h1))) (lt_irrefl _)
      rw [this]

end Work.WilE7
