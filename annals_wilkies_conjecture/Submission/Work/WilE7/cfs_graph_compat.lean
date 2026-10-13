import Mathlib
import Submission.Work.WilE7.DecompDefs

set_option autoImplicit false

namespace Work.WilE7

/-- Each cell of the decomposition `cfs C T` (the `k+2` graphs of the levels
`-1, T 0, …, T (k-1), 1` and the `k+1` open bands between consecutive levels)
is compatible with the union of the graphs of the sections `T j`: it is either
contained in it (the graphs of the interior levels) or disjoint from it (the two
boundary faces and every band). -/
theorem cfs_graph_compat {p k : ℕ} {C : Set (Fin p → ℝ)} {T : Fin k → (Fin p → ℝ) → ℝ}
    (hmono : ∀ x ∈ C, StrictMono fun j : Fin k => T j x)
    (hbnd : ∀ x ∈ C, ∀ j : Fin k, |T j x| < 1) :
    ∀ κ ∈ Work.WilE7.cfs C T,
      κ ⊆ (⋃ j : Fin k, {y : Fin (p + 1) → ℝ |
        Fin.init y ∈ C ∧ y (Fin.last p) = T j (Fin.init y)}) ∨
      Disjoint κ (⋃ j : Fin k, {y : Fin (p + 1) → ℝ |
        Fin.init y ∈ C ∧ y (Fin.last p) = T j (Fin.init y)}) := by
  intro κ hκ
  rw [mem_cfs] at hκ
  rcases hκ with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · -- graph cell of the level `lvl T · i`
    rcases Fin.eq_zero_or_eq_succ i with hz | ⟨i', rfl⟩
    · -- the bottom face `y = -1`
      rw [hz]
      right
      rw [Set.disjoint_left]
      intro y hy hyΓ
      rw [gr, Set.mem_ofPred_eq] at hy
      rw [Set.mem_iUnion] at hyΓ
      obtain ⟨j, hyj⟩ := hyΓ
      rw [Set.mem_ofPred_eq] at hyj
      have hlc : y (Fin.last p) = (-1 : ℝ) := by simpa only [lvl_zero] using hy.2
      have hsm := strictMono_lvl (hmono (Fin.init y) hy.1) (hbnd (Fin.init y) hy.1)
      have heq : lvl T (Fin.init y) (0 : Fin (k+2)) =
          lvl T (Fin.init y) (Fin.succ (Fin.castSucc j)) := by
        rw [lvl_zero, lvl_succ]
        exact hlc.symm.trans hyj.2
      have hcontra : (0 : Fin (k+2)) = Fin.succ (Fin.castSucc j) := hsm.injective heq
      have hv := congrArg Fin.val hcontra
      simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc] at hv
      omega
    · rcases Fin.eq_castSucc_or_eq_last i' with ⟨jj, hjj⟩ | hlast
      · -- the graph of the section `T jj`
        rw [hjj]
        left
        intro y hy
        rw [gr, Set.mem_ofPred_eq] at hy
        refine Set.mem_iUnion.mpr ⟨jj, ?_⟩
        rw [Set.mem_ofPred_eq]
        exact ⟨hy.1, by rw [hy.2, lvl_succ]⟩
      · -- the top face `y = 1`
        rw [hlast]
        right
        rw [Set.disjoint_left]
        intro y hy hyΓ
        rw [gr, Set.mem_ofPred_eq] at hy
        rw [Set.mem_iUnion] at hyΓ
        obtain ⟨j, hyj⟩ := hyΓ
        rw [Set.mem_ofPred_eq] at hyj
        rw [show (Fin.succ (Fin.last k)) = (Fin.last (k+1) : Fin (k+2)) from
          Fin.ext (by simp)] at hy
        have hlc : y (Fin.last p) = (1 : ℝ) := by simpa only [lvl_last] using hy.2
        have hsm := strictMono_lvl (hmono (Fin.init y) hy.1) (hbnd (Fin.init y) hy.1)
        have heq : lvl T (Fin.init y) (Fin.last (k+1)) =
            lvl T (Fin.init y) (Fin.succ (Fin.castSucc j)) := by
          rw [lvl_last, lvl_succ]
          exact hlc.symm.trans hyj.2
        have hcontra : (Fin.last (k+1)) = Fin.succ (Fin.castSucc j) := hsm.injective heq
        have hv := congrArg Fin.val hcontra
        simp only [Fin.val_last, Fin.val_succ, Fin.val_castSucc] at hv
        have hj : (j : ℕ) < k := j.isLt
        omega
  · -- band cell: always disjoint from the union of the graphs
    right
    rw [Set.disjoint_left]
    intro y hy hyΓ
    rw [bd, Set.mem_ofPred_eq] at hy
    obtain ⟨hyC, hy1, hy2⟩ := hy
    rw [Set.mem_iUnion] at hyΓ
    obtain ⟨j, hyj⟩ := hyΓ
    rw [Set.mem_ofPred_eq] at hyj
    have hsm := strictMono_lvl (hmono (Fin.init y) hyC) (hbnd (Fin.init y) hyC)
    have h1raw : lvl T (Fin.init y) (Fin.castSucc i) < T j (Fin.init y) :=
      lt_of_lt_of_le hy1 (le_of_eq hyj.2)
    have h2raw : T j (Fin.init y) < lvl T (Fin.init y) i.succ :=
      lt_of_le_of_lt (le_of_eq hyj.2.symm) hy2
    have h1 : Fin.castSucc i < Fin.succ (Fin.castSucc j) :=
      hsm.lt_iff_lt.mp (by rw [lvl_succ]; exact h1raw)
    have h2 : Fin.succ (Fin.castSucc j) < i.succ :=
      hsm.lt_iff_lt.mp (by rw [lvl_succ]; exact h2raw)
    have hv1 := Fin.lt_def.mp h1
    have hv2 := Fin.lt_def.mp h2
    simp only [Fin.val_castSucc, Fin.val_succ] at hv1 hv2
    omega

end Work.WilE7
