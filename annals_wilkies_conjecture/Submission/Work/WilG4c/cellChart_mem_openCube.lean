import Mathlib
import Submission.Work.WilG4c.EngineDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

/-- Arithmetic core of the chart estimate.  The affine interpolation
`(a + b)/2 + (t - 1/2)·(b - a)` of the endpoints `a` and `b` at the parameter `t`
(equivalently `a + t·(b - a)`, the convex combination `(1-t)·a + t·b`) lies in `(0,1)`
whenever `0 ≤ a ≤ b ≤ 1`, `t ∈ (0,1)` and the midpoint `(a + b)/2` lies in `(0,1)`.

The midpoint hypothesis is only needed in the degenerate case `a = b`: when `a < b` the
interpolation is strictly between `a` and `b`. -/
theorem midShift_mem_Ioo (a b t : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b)
    (ht0 : 0 < t) (ht1 : t < 1) (hm0 : 0 < (a + b) / 2) (hm1 : (a + b) / 2 < 1) :
    (a + b) / 2 + (t - 1 / 2) * (b - a) ∈ Set.Ioo (0 : ℝ) 1 := by
  have heq : (a + b) / 2 + (t - 1 / 2) * (b - a) = a + t * (b - a) := by ring
  rw [Set.mem_Ioo, heq]
  rcases lt_or_eq_of_le hab with h | h
  · have hpos : (0 : ℝ) < b - a := by linarith
    constructor
    · have h1 : 0 < t * (b - a) := mul_pos ht0 hpos
      linarith
    · have h2 : t * (b - a) < 1 * (b - a) := mul_lt_mul_of_pos_right ht1 hpos
      linarith
  · subst h
    rw [sub_self, mul_zero, add_zero]
    constructor <;> linarith

theorem cellChart_mem_openCube {p n : ℕ}
    (χ ψ : (Fin p → ℝ) → (Fin n → ℝ) → (Fin n → ℝ))
    (M W : (Fin p → ℝ) → (Fin n → ℝ) → ℝ) (l : Fin p → ℝ)
    (z : Fin (n + 1) → ℝ) (hz : z ∈ WilkiesDesign.openCube (n + 1))
    (hχ : (fun j => χ l (ψ l (Fin.init z)) j) ∈ WilkiesDesign.openCube n)
    (lo hi : ℝ) (hlo0 : 0 ≤ lo) (hhi1 : hi ≤ 1) (hle : lo ≤ hi)
    (hmid0 : 0 < (lo + hi) / 2) (hmid1 : (lo + hi) / 2 < 1)
    (hM : M l (ψ l (Fin.init z)) = (lo + hi) / 2)
    (hW : 2 * W l (ψ l (Fin.init z)) - 1 / 2 = hi - lo) :
    (fun j => Work.WilG4c.cellChart χ M W ψ l z j) ∈ WilkiesDesign.openCube (n + 1) := by
  simp only [WilkiesDesign.openCube, Set.mem_ofPred_eq] at hz hχ ⊢
  intro i
  by_cases hlast : (i : ℕ) = n
  · -- the last coordinate: the interpolation of the two fibre ends
    have hcell : Work.WilG4c.cellChart χ M W ψ l z i =
        M l (ψ l (Fin.init z)) + (z (Fin.last n) - 1 / 2) *
          (2 * W l (ψ l (Fin.init z)) - 1 / 2) := by
      simp only [Work.WilG4c.cellChart]
      rw [dite_eq_left hlast]
    rw [hcell, hM, hW]
    obtain ⟨ht0, ht1⟩ := hz (Fin.last n)
    exact midShift_mem_Ioo lo hi (z (Fin.last n)) hlo0 hhi1 hle ht0 ht1 hmid0 hmid1
  · -- the first `n` coordinates: they are the coordinates of `χ` at the base point
    have hjlt : (i : ℕ) < n := by
      have := i.isLt
      omega
    have hcell : Work.WilG4c.cellChart χ M W ψ l z i =
        χ l (ψ l (Fin.init z)) ⟨(i : ℕ), hjlt⟩ := by
      simp only [Work.WilG4c.cellChart]
      rw [dite_eq_right hlast]
    rw [hcell]
    exact hχ ⟨(i : ℕ), hjlt⟩

end Work.WilG4c
