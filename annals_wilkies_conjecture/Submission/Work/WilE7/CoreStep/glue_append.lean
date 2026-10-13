import Mathlib
import Submission.Work.WilE7.PadDefs
import Submission.Work.WilE7.Defs

namespace Work.WilE7.CoreStep

theorem glue_append {n m1 m2 : ℕ} (x : Fin n → ℝ) (y1 : Fin m1 → ℝ) (y2 : Fin m2 → ℝ) :
    ∃ z : Fin (n + (m1 + m2)) → ℝ,
      (∀ i : Fin (n + m1),
          z (Fin.castLE (Nat.add_le_add_left (Nat.le_add_right m1 m2) n) i) =
            Fin.append x y1 i) ∧
      (∀ i : Fin (n + m2), z (Work.WilE7.midInj n m1 m2 i) = Fin.append x y2 i) ∧
      WilkiesDesign.E.projFirst n (m1 + m2) z = x ∧
      (Fin.append x y1 ∈ WilkiesDesign.E.cubeC (n + m1) →
        Fin.append x y2 ∈ WilkiesDesign.E.cubeC (n + m2) →
        z ∈ WilkiesDesign.E.cubeC (n + (m1 + m2))) := by
  -- Glue the three blocks `x`, `y1`, `y2` in that order.  The witness is thus
  -- `Fin.append x (Fin.append y1 y2)`, read as a point of `ℝ^{n+(m1+m2)}`.
  refine ⟨Fin.append x (Fin.append y1 y2), ?_, ?_, ?_, ?_⟩
  · -- On the first `n + m1` coordinates it agrees with `Fin.append x y1`.
    intro i
    refine Fin.addCases (m := n) (n := m1)
      (motive := fun i => Fin.append x (Fin.append y1 y2)
          (Fin.castLE (Nat.add_le_add_left (Nat.le_add_right m1 m2) n) i) = Fin.append x y1 i)
      ?_ ?_ i
    · intro a
      have h : Fin.castLE (Nat.add_le_add_left (Nat.le_add_right m1 m2) n) (Fin.castAdd m1 a)
          = Fin.castAdd (m1 + m2) a := Fin.ext rfl
      rw [h, Fin.append_left, Fin.append_left]
    · intro b
      have h : Fin.castLE (Nat.add_le_add_left (Nat.le_add_right m1 m2) n) (Fin.natAdd n b)
          = Fin.natAdd n (Fin.castAdd m2 b) := Fin.ext rfl
      rw [h, Fin.append_right, Fin.append_left, Fin.append_right]
  · -- On the coordinates selected by `midInj` (base block, then the `y2` block) it agrees
    -- with `Fin.append x y2`.
    intro i
    refine Fin.addCases (m := n) (n := m2)
      (motive := fun i => Fin.append x (Fin.append y1 y2) (Work.WilE7.midInj n m1 m2 i)
        = Fin.append x y2 i) ?_ ?_ i
    · intro a
      rw [Work.WilE7.midInj_castAdd, Fin.append_left, Fin.append_left]
    · intro b
      rw [Work.WilE7.midInj_natAdd, Fin.append_right, Fin.append_right, Fin.append_right]
  · -- The first `n` coordinates recover `x`.
    funext j
    exact Fin.append_left x (Fin.append y1 y2) j
  · -- Cube membership: each coordinate is a coordinate of one of the two given points.
    intro h1c h2c j
    refine Fin.addCases (m := n) (n := m1 + m2)
      (motive := fun j => |Fin.append x (Fin.append y1 y2) j| ≤ 1) ?_ ?_ j
    · intro a
      simpa [Fin.append_left] using h1c (Fin.castAdd m1 a)
    · intro k
      rw [Fin.append_right]
      refine Fin.addCases (m := m1) (n := m2)
        (motive := fun k => |Fin.append y1 y2 k| ≤ 1) ?_ ?_ k
      · intro b
        simpa [Fin.append_left, Fin.append_right] using h1c (Fin.natAdd n b)
      · intro b
        simpa [Fin.append_right] using h2c (Fin.natAdd n b)

end Work.WilE7.CoreStep
