import Mathlib
import Submission.Work.ResMath.defs

namespace Work.ResMath

/-- `HvdH.permS s t` is a permutation matrix whenever `s` and `t` are coprime: it is
orthogonal (`Mᵀ M = 1` and `M Mᵀ = 1`). -/
theorem permS_transpose_mul (s t : ℕ) (h : Nat.Coprime s t) :
    (HvdH.permS s t).transpose * HvdH.permS s t = 1 ∧
      HvdH.permS s t * (HvdH.permS s t).transpose = 1 := by
  rcases s with _ | n
  · -- `s = 0`: the index type `Fin 0` is empty, so every matrix is the identity.
    constructor
    · ext i; exact i.elim0
    · ext i; exact i.elim0
  · -- `s = n + 1`: multiplication by `t` is a bijection of `Fin (n+1)` modulo `n+1`.
    have hpos : 0 < n + 1 := Nat.succ_pos n
    let f : Fin (n + 1) → Fin (n + 1) :=
      fun j => ⟨t * (j : ℕ) % (n + 1), Nat.mod_lt _ hpos⟩
    have hinj : Function.Injective f := by
      intro j₁ j₂ hjj
      have hval : t * (j₁ : ℕ) % (n + 1) = t * (j₂ : ℕ) % (n + 1) := by
        have := congrArg Fin.val hjj
        simpa only [f] using this
      have hmod : t * (j₁ : ℕ) ≡ t * (j₂ : ℕ) [MOD n + 1] := hval
      have hcancel := Nat.ModEq.cancel_left_of_coprime (m := n + 1) (c := t) h hmod
      exact Fin.ext (hcancel.eq_of_lt_of_lt j₁.isLt j₂.isLt)
    let σ : Equiv.Perm (Fin (n + 1)) := Equiv.ofBijective f hinj.bijective_of_finite
    have hσval : ∀ j : Fin (n + 1), (σ j).val = t * (j : ℕ) % (n + 1) :=
      fun j => by simp only [σ, Equiv.ofBijective_apply, f]
    have hperm : HvdH.permS (n + 1) t = σ.permMatrix ℂ := by
      ext j i
      show (if (i : ℕ) = t * (j : ℕ) % (n + 1) then (1 : ℂ) else 0) = σ.toPEquiv.toMatrix j i
      simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_some_iff]
      have hiff : ((i : ℕ) = t * (j : ℕ) % (n + 1)) ↔ (σ j = i) := by
        constructor
        · intro hci; exact Fin.ext (by rw [hσval j, hci])
        · intro hcij; rw [← hσval j, hcij]
      exact if_congr hiff rfl rfl
    rw [hperm]
    refine ⟨?_, ?_⟩
    · rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]
    · rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

end Work.ResMath
