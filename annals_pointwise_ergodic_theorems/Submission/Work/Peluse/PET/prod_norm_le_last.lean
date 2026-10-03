import Mathlib

namespace Work.Peluse.PET

/-- **The last factor dominates a product of `1`-bounded factors.**

For a family `F : Fin (m+1) → ℤ → ℂ` whose values are all bounded by `1` in norm, the product of
the norms of the `m` terms indexed by `1, …, m` (i.e. `F i.succ` for `i : Fin m`) is bounded by the
norm of the *last* of them, `F ⟨m, …⟩`.  Indeed each factor lies in `[0,1]`, so the product over all
`i : Fin m` is at most the factor at the index `j` with `j.succ = ⟨m, …⟩`.

This is the elementary estimate used in `Work.Peluse.PET.norm_lambda_le` to bound the `Λ`-average
of Peluse's inverse theorem by the average of the last factor. -/
theorem prod_norm_le_last {m : ℕ} (hm : 0 < m) (c : Fin (m + 1) → ℤ) (F : Fin (m + 1) → ℤ → ℂ)
    (hF : ∀ i x, ‖F i x‖ ≤ 1) (x : ℤ) (y : ℕ) :
    ∏ i : Fin m, ‖F i.succ (x + c i.succ * (y : ℤ))‖
      ≤ ‖F ⟨m, Nat.lt_succ_self m⟩ (x + c ⟨m, Nat.lt_succ_self m⟩ * (y : ℤ))‖ := by
  classical
  -- The last index of `Fin (m+1)`, which is the successor of an index of `Fin m` because `m > 0`.
  set i : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩ with hi
  have hne : i ≠ 0 := by
    intro h
    have h2 : i.val = 0 := by
      rw [h]; rfl
    rw [hi] at h2
    simp at h2
    omega
  -- the index `j : Fin m` with `j.succ = i`
  set j : Fin m := i.pred hne with hj
  have hjs : j.succ = i := Fin.succ_pred i hne
  -- a product of numbers in `[0,1]` over `univ` is at most the product over any subset
  have hkey := Finset.prod_le_prod_of_subset_of_le_one₀
      (s := ({j} : Finset (Fin m))) (t := Finset.univ)
      (f := fun k : Fin m => ‖F k.succ (x + c k.succ * (y : ℤ))‖)
      (Finset.singleton_subset_iff.mpr (Finset.mem_univ j))
      (fun k _ => norm_nonneg _)
      (fun k _ _ => hF k.succ _)
  rw [Finset.prod_singleton] at hkey
  rw [hjs] at hkey
  exact hkey

end Work.Peluse.PET
