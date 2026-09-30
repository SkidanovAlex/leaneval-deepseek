import Mathlib
import Submission.Work.BW.minkowski_defs
import Submission.Work.BW.basis_reduction_l1
import Submission.Work.BW.kummer_minkowski_second

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# BW §9's Minkowski input

Assembly of the product bound used in the Kummer reduction: BW's reduction L4
(`basis_reduction_l1`, a basis of the lattice whose weighted `ℓ¹` norms have a bounded product)
combined with Minkowski's second inequality for the weighted `ℓ¹` body
(`kummer_minkowski_second`).
-/

namespace Work.BW

open Complex

variable {n : ℕ}

/-- Minkowski's second inequality for the weighted `ℓ¹` body `F(x) = ∑ cᵢ|xᵢ|` combined with
BW L4: the lattice `A ℤⁿ` has a basis `A U` (`U ∈ GL_n(ℤ)`) with
`∏_j F(col_j) ≤ (n!)²/2^{n-1} · |det A| · ∏ cᵢ`. -/
theorem kummer_minkowski_basis {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : A.det ≠ 0) (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) :
    ∃ U : Matrix (Fin n) (Fin n) ℤ, IsUnit U.det ∧
      ∏ j, (∑ i, c i * |(((A * U) i j : ℤ) : ℝ)|) ≤
        ((n.factorial : ℝ) ^ 2 / 2 ^ (n - 1)) * |((A.det : ℤ) : ℝ)| * ∏ i, c i := by
  obtain ⟨U, hU, hUbound⟩ := basis_reduction_l1 hn A hA c hc
  refine ⟨U, hU, ?_⟩
  have hMink := kummer_minkowski_second hn A hA c hc
  have hcpos : (0 : ℝ) ≤ (n.factorial : ℝ) / (2 : ℝ) ^ (n - 1) := by positivity
  have hstep : (n.factorial : ℝ) / (2 : ℝ) ^ (n - 1) *
        ∏ j : Fin n, succMin (latOf A) (wl1 c) (j.1 + 1)
      ≤ (n.factorial : ℝ) / (2 : ℝ) ^ (n - 1) *
        ((n.factorial : ℝ) * |((A.det : ℤ) : ℝ)| * ∏ i, c i) :=
    mul_le_mul_of_nonneg_left hMink hcpos
  have h1 : ∏ j, (∑ i, c i * |(((A * U) i j : ℤ) : ℝ)|)
      = ∏ j : Fin n, wl1 c (fun i => (((A * U) i j : ℤ) : ℝ)) := rfl
  rw [h1]
  refine le_trans hUbound (le_trans hstep ?_)
  exact le_of_eq (by ring)

end Work.BW
