import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.Minkowski2

/-- Telescoping sum of successive differences over an initial segment of `Fin d`. -/
private theorem telescope_sum {d : ℕ} (lam : Fin (d+1) → ℝ) (m : Fin d) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin d => i ≤ m),
        (lam i.succ - lam i.castSucc)) = lam m.succ - lam 0 := by
  let F : ℕ → ℝ := fun n => lam ⟨n % (d + 1), Nat.mod_lt n (Nat.succ_pos d)⟩
  have hFa : ∀ (n : ℕ) (hn : n < d + 1), F n = lam ⟨n, hn⟩ := by
    intro n hn
    simp only [F, Nat.mod_eq_of_lt hn]
  have h1 : F (m.val + 1) = lam m.succ := by
    rw [hFa (m.val + 1) (by omega)]
    congr 1
  have h0 : F 0 = lam 0 := by
    rw [hFa 0 (by omega)]
    congr 1
  rw [← h1, ← h0, ← Finset.sum_range_sub F (m.val + 1)]
  refine Finset.sum_bij
    (fun a (_ : a ∈ Finset.univ.filter (fun i : Fin d => i ≤ m)) => a.val) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_range]
    have : (a : ℕ) ≤ m.val := by
      have := (Finset.mem_filter.mp ha).2
      rwa [Fin.le_def] at this
    omega
  · intro a1 _ a2 _ h
    exact Fin.ext h
  · intro b hb
    simp only [Finset.mem_range] at hb
    refine ⟨⟨b, by omega⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
    omega
  · intro a _
    rw [hFa (a.val + 1) (by omega), hFa a.val (by omega)]
    congr 2

theorem diag_telescope {d : ℕ} (lam : Fin (d+1) → ℝ) (hlam0 : lam 0 = 0) (m : Fin d) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin d => i ≤ m),
        (lam i.succ - lam i.castSucc) / 2) = lam m.succ / 2 := by
  rw [← Finset.sum_div, telescope_sum lam m, hlam0, sub_zero]

end Work.BW.Minkowski2
