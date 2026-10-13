import Mathlib
import Submission.Work.WilkiesH.Cell

namespace Work.WilkiesH.Cell

/-- A cell of dimension at most `k` is a subsingleton as soon as `k = 0`: the
`band` constructor strictly increases the dimension, so a zero-dimensional cell
can only be reached from the base case by `graph` steps (each of which preserves
a subsingleton) and by the vacuous `mono` steps. -/
theorem cellDimLE_eq_zero_subsingleton {n : ℕ} {C : Set (Fin n → ℝ)} {k : ℕ} :
    CellDimLE n C k → k = 0 → C.Subsingleton := by
  intro h
  induction h with
  | zero =>
      intro _
      exact Set.subsingleton_univ
  | graph hC f hf ih =>
      intro hk
      have hs := ih hk
      intro z hz w hw
      have h1 : z = Fin.snoc (Fin.init z) (f (Fin.init z)) := by
        have hh := Fin.snoc_init_self z
        rw [hz.2] at hh
        exact hh.symm
      have h2 : w = Fin.snoc (Fin.init w) (f (Fin.init w)) := by
        have hh := Fin.snoc_init_self w
        rw [hw.2] at hh
        exact hh.symm
      have hinit : Fin.init z = Fin.init w := hs hz.1 hw.1
      calc z = Fin.snoc (Fin.init z) (f (Fin.init z)) := h1
        _ = Fin.snoc (Fin.init w) (f (Fin.init w)) := by rw [hinit]
        _ = w := h2.symm
  | band hC a b ha hb hab ih =>
      intro hk
      exact absurd hk (by omega)
  | mono hC hk ih =>
      intro hk'
      exact ih (Nat.eq_zero_of_le_zero (hk' ▸ hk))

theorem cellDimLE_zero_subsingleton {n : ℕ} {C : Set (Fin n → ℝ)} (h : CellDimLE n C 0) : C.Subsingleton :=
  cellDimLE_eq_zero_subsingleton h rfl

end Work.WilkiesH.Cell
