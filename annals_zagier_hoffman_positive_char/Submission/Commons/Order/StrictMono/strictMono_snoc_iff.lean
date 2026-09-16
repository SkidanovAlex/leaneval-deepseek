import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.SuccPred

namespace Commons.Order.StrictMono

theorem strictMono_snoc_iff {r : ℕ} (w : Fin (r + 1) → ℕ) (d : ℕ) :
    StrictMono (Fin.snoc w d) ↔ StrictMono w ∧ w (Fin.last r) < d := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i j hij
      have h' := h (Fin.castSucc_lt_castSucc_iff.mpr hij)
      simpa [Fin.snoc_castSucc] using h'
    · have h' := h (Fin.castSucc_lt_last (Fin.last r))
      simpa [Fin.snoc_castSucc, Fin.snoc_last] using h'
  · rintro ⟨hw, hd⟩
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    by_cases hi : i = Fin.last r
    · subst hi
      rw [Fin.succ_last]
      simpa [Fin.snoc_castSucc, Fin.snoc_last] using hd
    · have hne : i.succ ≠ Fin.last (r + 1) := by
        intro h
        apply hi
        ext
        rw [Fin.val_last]
        have hv := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_last] at hv
        omega
      obtain ⟨k, hk⟩ := Fin.eq_castSucc_of_ne_last hne
      have hik : i < k := by
        have hlt : (i.castSucc : Fin (r + 2)) < k.castSucc := by
          rw [hk]
          simp [Fin.lt_def, Fin.val_succ]
        exact Fin.castSucc_lt_castSucc_iff.mp hlt
      have := hw hik
      simpa [Fin.snoc_castSucc, ← hk] using this

end Commons.Order.StrictMono