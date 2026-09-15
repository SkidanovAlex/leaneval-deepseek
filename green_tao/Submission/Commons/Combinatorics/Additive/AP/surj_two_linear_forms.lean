import Mathlib
import Submission.Commons.Combinatorics.Additive.AP.sum_phiZ_cover

namespace Commons.Combinatorics.Additive.AP

open Finset

/-- First coordinate of the solution of a nonsingular `2 × 2` linear system with
coefficient matrix `[[A, C], [B, E]]` and right-hand side `(c, d)`. -/
lemma det_solve_fst {K : Type*} [Field K] (A B C E c d : K) (h : A * E - C * B ≠ 0) :
    A * ((A * E - C * B)⁻¹ * (c * E - d * C))
      + C * ((A * E - C * B)⁻¹ * (d * A - c * B)) = c := by
  have hid : A * ((A * E - C * B)⁻¹ * (c * E - d * C))
        + C * ((A * E - C * B)⁻¹ * (d * A - c * B))
      = (A * E - C * B)⁻¹ * ((A * E - C * B) * c) := by ring
  rw [hid, ← mul_assoc, inv_mul_cancel₀ h, one_mul]

/-- Second coordinate of the solution of a nonsingular `2 × 2` linear system with
coefficient matrix `[[A, C], [B, E]]` and right-hand side `(c, d)`. -/
lemma det_solve_snd {K : Type*} [Field K] (A B C E c d : K) (h : A * E - C * B ≠ 0) :
    B * ((A * E - C * B)⁻¹ * (c * E - d * C))
      + E * ((A * E - C * B)⁻¹ * (d * A - c * B)) = d := by
  have hid : B * ((A * E - C * B)⁻¹ * (c * E - d * C))
        + E * ((A * E - C * B)⁻¹ * (d * A - c * B))
      = (A * E - C * B)⁻¹ * ((A * E - C * B) * d) := by ring
  rw [hid, ← mul_assoc, inv_mul_cancel₀ h, one_mul]

/-- The map `y ↦ (∑ i, a i * y i, ∑ i, b i * y i)` from `(Fin n → ZMod p)` onto
`ZMod p × ZMod p` is surjective as soon as the points `(a i, b i)` do not all lie
on a line through the origin, i.e. some pair of them is linearly independent. -/
theorem surj_two_linear_forms {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 2 ≤ n)
    (a b : Fin n → ZMod p) (hne : ∃ i j, a i * b j ≠ a j * b i) :
    Function.Surjective (fun y : Fin n → ZMod p => (∑ i, a i * y i, ∑ i, b i * y i)) := by
  classical
  obtain ⟨i, j, hij⟩ := hne
  have hij' : i ≠ j := by
    intro h; exact hij (by rw [h])
  have hdet : a i * b j - a j * b i ≠ 0 := sub_ne_zero.mpr hij
  intro t
  obtain ⟨c, d⟩ := t
  set yi : ZMod p := (a i * b j - a j * b i)⁻¹ * (c * b j - d * a j) with hyidef
  set yj : ZMod p := (a i * b j - a j * b i)⁻¹ * (d * a i - c * b i) with hyjdef
  refine ⟨Function.update (Function.update (0 : Fin n → ZMod p) i yi) j yj, ?_⟩
  have hA : ∑ k, a k * (Function.update (Function.update (0 : Fin n → ZMod p) i yi) j yj) k
      = a i * yi + a j * yj := sum_mul_update₂ hij' yi yj a
  have hB : ∑ k, b k * (Function.update (Function.update (0 : Fin n → ZMod p) i yi) j yj) k
      = b i * yi + b j * yj := sum_mul_update₂ hij' yi yj b
  change (∑ k, a k * (Function.update (Function.update (0 : Fin n → ZMod p) i yi) j yj) k,
        ∑ k, b k * (Function.update (Function.update (0 : Fin n → ZMod p) i yi) j yj) k) = (c, d)
  rw [hA, hB]
  refine Prod.ext ?_ ?_
  · rw [hyidef, hyjdef]
    exact det_solve_fst (a i) (b i) (a j) (b j) c d hdet
  · rw [hyidef, hyjdef]
    exact det_solve_snd (a i) (b i) (a j) (b j) c d hdet

end Commons.Combinatorics.Additive.AP
