import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.Minkowski2

/-- Monotonicity of the sequence `lam` along the shift `n ↦ n+1` extends to the
comparison of the `castSucc` embedding with the `succ` embedding: if `lam 0 = 0`,
if `lam` is positive on the positive indices and nondecreasing there, then
`lam i.castSucc ≤ lam i.succ` for every `i`. -/
theorem lam_castSucc_le_succ {d : ℕ} (lam : Fin (d+1) → ℝ) (hlam0 : lam 0 = 0)
    (hpos : ∀ i : Fin d, 0 < lam i.succ)
    (hmono : ∀ i j : Fin d, i ≤ j → lam i.succ ≤ lam j.succ) (i : Fin d) :
    lam i.castSucc ≤ lam i.succ := by
  rcases Nat.eq_zero_or_pos i.val with h0 | hpos'
  · -- `i = 0`: use `lam 0 = 0` and positivity at index `1`.
    have hd : 0 < d := by omega
    have hcs : i.castSucc = (0 : Fin (d+1)) := Fin.ext (by simp [Fin.val_castSucc]; omega)
    have hk : (⟨0, hd⟩ : Fin d).succ = i.succ := Fin.ext (by simp [Fin.val_succ]; omega)
    rw [hcs, hlam0, ← hk]
    exact le_of_lt (hpos ⟨0, hd⟩)
  · -- `i > 0`: `i.castSucc` is the successor of `i - 1`, so monotonicity applies.
    have hd : i.val - 1 < d := by omega
    have hle : (⟨i.val - 1, hd⟩ : Fin d) ≤ i := by
      simp only [Fin.le_def]; exact Nat.sub_le _ _
    have hs : (⟨i.val - 1, hd⟩ : Fin d).succ = i.castSucc :=
      Fin.ext (by simp [Fin.val_castSucc]; omega)
    rw [← hs]
    exact hmono _ i hle

end Work.BW.Minkowski2
