import Mathlib
import Submission.Work.WilG1.Calc.ClosureDefs

set_option maxHeartbeats 1000000

namespace Work.WilG1.Calc

/-- Membership of a point in a set of functions on `Fin m`, transported along an equality
`m = k` of the index types: the transported point is the function `i ↦ w (Fin.cast h i)`. -/
theorem mem_of_cast_set {m k : ℕ} (h : m = k) (S : Set (Fin m → ℝ)) (w : Fin k → ℝ) :
    w ∈ (h ▸ S) ↔ (fun i : Fin m => w (Fin.cast h i)) ∈ S := by
  cases h
  simp

theorem closure_append_mem {n : ℕ} {X : Set (Fin n → ℝ)}
    {x : Fin n → ℝ} {r : ℝ} {u : Fin (n + 1) → ℝ} :
    Fin.append (Fin.snoc x r) u ∈
        (Work.WilG1.Calc.bigSpace_eq n ▸ Work.WilG1.Calc.bigJ X) ↔
      (fun j : Fin n => u (Fin.castSucc j)) ∈ X ∧
        (∑ j : Fin n, (u (Fin.castSucc j) - x j) ^ 2) + (u (Fin.last n)) ^ 2 - r ^ 2 = 0 := by
  rw [mem_of_cast_set, bigJ, Set.mem_inter_iff, mem_cylSet_iff, mem_hypSet_iff]
  -- Coordinates of the point `fun i => Fin.append (Fin.snoc x r) u (Fin.cast (bigSpace_eq n) i)`.
  have hbx : ∀ j : Fin n,
      Fin.cast (bigSpace_eq n) (bxIdx j) = Fin.castAdd (n + 1) (Fin.castSucc j) := by
    intro j
    apply Fin.ext
    simp [bxIdx]
  have hby : ∀ j : Fin n,
      Fin.cast (bigSpace_eq n) (byIdx j) = Fin.natAdd (n + 1) (Fin.castSucc j) := by
    intro j
    apply Fin.ext
    simp [byIdx, Fin.natAdd]
  have hbr : Fin.cast (bigSpace_eq n) (brIdx n) = Fin.castAdd (n + 1) (Fin.last n) := by
    apply Fin.ext
    simp [brIdx, Fin.last]
  have hbs : Fin.cast (bigSpace_eq n) (bsIdx n) = Fin.natAdd (n + 1) (Fin.last n) := by
    apply Fin.ext
    simp [bsIdx, Fin.last, Fin.natAdd]
    try omega
  simp only [hbx, hby, hbr, hbs, Fin.append_left, Fin.append_right,
    Fin.snoc_castSucc, Fin.snoc_last]

end Work.WilG1.Calc
