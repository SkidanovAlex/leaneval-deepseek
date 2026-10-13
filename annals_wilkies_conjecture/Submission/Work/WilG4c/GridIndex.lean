import Mathlib
import Submission.Work.WilG4c.LipDefs

namespace Work.WilG4c

theorem GridIndex (n K : ℕ) (hK : 1 ≤ K) (x : Fin (n + 1) → ℝ)
    (hx : x ∈ WilkiesDesign.openCube (n + 1)) :
    ∃ j : Fin (n + 1) → Fin K, ∀ i, ((j i : ℕ) : ℝ) ≤ (K : ℝ) * x i ∧
      (K : ℝ) * x i ≤ ((j i : ℕ) : ℝ) + 1 := by
  -- `K > 0` as a real number.
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    have h1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    linarith
  -- The grid index of a coordinate `i` is `⌊K * x i⌋`; it lies in `{0, …, K-1}`
  -- because `0 < x i < 1`.
  have hlt : ∀ i : Fin (n + 1), Nat.floor ((K : ℝ) * x i) < K := by
    intro i
    have hx0 : 0 < x i := (hx i).1
    have hx1 : x i < 1 := (hx i).2
    have h0 : 0 ≤ (K : ℝ) * x i := le_of_lt (mul_pos hKpos hx0)
    rw [Nat.floor_lt h0]
    calc (K : ℝ) * x i < (K : ℝ) * 1 := mul_lt_mul_of_pos_left hx1 hKpos
      _ = (K : ℝ) := mul_one _
  refine ⟨fun i => ⟨Nat.floor ((K : ℝ) * x i), hlt i⟩, fun i => ⟨?_, ?_⟩⟩
  · have hx0 : 0 < x i := (hx i).1
    have h0 : 0 ≤ (K : ℝ) * x i := le_of_lt (mul_pos hKpos hx0)
    exact Nat.floor_le h0
  · exact le_of_lt (Nat.lt_floor_add_one _)

end Work.WilG4c
