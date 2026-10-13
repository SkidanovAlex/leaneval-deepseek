import Mathlib
import Submission.Work.WilE7.AboveAux.AboveLevelDefs
import Submission.Work.WilE7.AboveAux.blocksOf_fibBlkIdx
import Submission.Work.WilE8.Extend

namespace Work.WilE7.AboveAux

/-- The cube `[-1,1]^{n+m}` is the product of the cubes `[-1,1]^n` and `[-1,1]^m`, read through
the concatenation `Fin.append`. -/
theorem append_mem_cubeC_iff {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ) :
    Fin.append a b ∈ WilkiesDesign.E.cubeC (n + m) ↔
      a ∈ WilkiesDesign.E.cubeC n ∧ b ∈ WilkiesDesign.E.cubeC m := by
  constructor
  · intro h
    exact ⟨fun i => by rw [← Fin.append_left a b i]; exact h _,
      fun j => by rw [← Fin.append_right a b j]; exact h _⟩
  · rintro ⟨ha, hb⟩ i
    exact Fin.addCases (motive := fun i => |Fin.append a b i| ≤ 1)
      (fun i => by rw [Fin.append_left]; exact ha i)
      (fun j => by rw [Fin.append_right]; exact hb j) i

theorem blocksOf_mem_cube {N k : ℕ} (z : Fin k → Fin N → ℝ) (h : ∀ l, z l ∈ WilkiesDesign.E.cubeC N) :
    Work.WilE7.AboveAux.blocksOf k z ∈ WilkiesDesign.E.cubeC (N * k) := by
  -- `blocksOf` is defined by recursion on `k`, and the coordinate `fibBlkIdx` index of the
  -- last block sits at the end of the concatenation `blocksOf (k+1) z = append (blocksOf k z) …`.
  revert z h
  induction k with
  | zero =>
    intro z _
    rw [blocksOf.eq_1]
    intro i
    exact i.elim0
  | succ k ih =>
    intro z h
    rw [blocksOf.eq_2]
    exact (append_mem_cubeC_iff _ _).mpr
      ⟨ih (fun l => z l.castSucc) (fun l => h l.castSucc), h (Fin.last k)⟩

end Work.WilE7.AboveAux
