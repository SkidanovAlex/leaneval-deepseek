import Mathlib
import Submission.Work.BMF.vk_L_lower
import Submission.Work.BMF.V4prelim

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.N4chain

/-- **Lower bound for a Dirichlet `L`-function to the right of the line `Re s = 1`.**

For a Dirichlet character `χ` modulo `N`, a real `y` with `0 < y ≤ 1` and a complex `s` with
`1 + y ≤ Re s`, one has `y / 2 ≤ ‖L(s, χ)‖`.

The proof combines the elementary Euler-product lower bound
`1 ≤ ‖L(s, χ)‖ · ζ(Re s)` (`Work.BMF.vk_L_lower`) with the elementary upper bound
`ζ(σ) ≤ 1 + 1 / (σ - 1)` (`Work.BMF.riemannZeta_re_le_one_add_inv`): since `σ - 1 ≥ y`,
`ζ(σ) ≤ 1 + 1/y ≤ 2/y`, so `‖L(s, χ)‖ ≥ 1/ζ(σ) ≥ y/2`. -/
theorem LFunction_norm_lower_of_re {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) (hs : 1 + y ≤ s.re) :
    y / 2 ≤ ‖DirichletCharacter.LFunction χ s‖ := by
  have hs1 : 1 < s.re := by linarith
  -- Euler product: `1 ≤ ‖L(s,χ)‖ · ζ(Re s)`.
  have hlow : 1 ≤ ‖DirichletCharacter.LFunction χ s‖ * (riemannZeta (s.re : ℂ)).re :=
    Work.BMF.vk_L_lower χ hs1
  -- consequently `ζ(Re s) > 0`
  have hζpos : 0 < (riemannZeta (s.re : ℂ)).re := by
    by_contra h
    have hnonpos : (riemannZeta (s.re : ℂ)).re ≤ 0 := le_of_not_gt h
    have hle : ‖DirichletCharacter.LFunction χ s‖ * (riemannZeta (s.re : ℂ)).re ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) hnonpos
    linarith
  -- the elementary upper bound `ζ(Re s) ≤ 2 / y`
  have hζle : (riemannZeta (s.re : ℂ)).re ≤ 2 / y := by
    have h1 : (riemannZeta (s.re : ℂ)).re ≤ 1 + 1 / (s.re - 1) :=
      Work.BMF.riemannZeta_re_le_one_add_inv s.re hs1
    have h2 : 1 / (s.re - 1) ≤ 1 / y := by
      apply one_div_le_one_div_of_le hy
      linarith
    have h3 : 1 + 1 / y ≤ 2 / y := by
      rw [le_div_iff₀ hy]
      rw [add_mul, one_mul, div_mul_cancel₀ 1 hy.ne']
      linarith
    linarith
  -- hence `y/2 ≤ 1/ζ(Re s)`
  have hhalf : y / 2 ≤ 1 / (riemannZeta (s.re : ℂ)).re := by
    rw [le_div_iff₀ hζpos]
    calc y / 2 * (riemannZeta (s.re : ℂ)).re ≤ y / 2 * (2 / y) :=
          mul_le_mul_of_nonneg_left hζle (by positivity)
      _ = 1 := by field_simp
  -- and `1/ζ(Re s) ≤ ‖L(s,χ)‖` by the Euler product bound
  have hdiv : 1 / (riemannZeta (s.re : ℂ)).re ≤ ‖DirichletCharacter.LFunction χ s‖ := by
    rw [div_le_iff₀ hζpos]
    exact hlow
  linarith

end Work.BMF.N4chain
