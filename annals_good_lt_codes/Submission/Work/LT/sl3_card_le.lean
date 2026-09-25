import Mathlib
import Submission.Work.LT.Defs

/-! The elementary matrix `E₁₂(t)` as an element of `SL₃(ℤ/p)`; the `p` of them are pairwise
distinct, so `|SL₃(ℤ/p)| ≥ p`. -/

namespace Work.LT

open Matrix

/-- The `(0,1)` entry of the elementary matrix `E₁₂(t) = sl3E p 0 1 t` is `t`. -/
lemma sl3E_zero_one_apply (p : ℕ) (t : ZMod p) :
    ((sl3E p 0 1 t : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) :
      Matrix (Fin 3) (Fin 3) (ZMod p)) 0 1 = t := by
  simp [sl3E, Matrix.transvection, Matrix.single_apply_same]

/-- The map `t ↦ E₁₂(t)` from `ℤ/p` to `SL₃(ℤ/p)` is injective: `t` is recovered as the `(0,1)`
entry. -/
lemma sl3E_zero_one_injective (p : ℕ) :
    Function.Injective (fun t : ZMod p => sl3E p 0 1 t) := by
  intro t s h
  have h' := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) =>
    (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 1) h
  rwa [sl3E_zero_one_apply p t, sl3E_zero_one_apply p s] at h'

/-- The special linear group `SL₃(ℤ/p)` has at least `p` elements: the `p` elementary matrices `E₁₂(t)` are pairwise distinct. -/
theorem sl3_card_le (p : ℕ) [Fact p.Prime] : p ≤ Fintype.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) := by
  have h := Fintype.card_le_of_injective (fun t : ZMod p => sl3E p 0 1 t)
    (sl3E_zero_one_injective p)
  rwa [ZMod.card] at h

end Work.LT
