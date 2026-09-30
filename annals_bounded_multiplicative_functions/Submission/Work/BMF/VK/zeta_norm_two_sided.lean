import Mathlib
import Submission.Work.BMF.vk_L_lower
import Submission.Work.BMF.vk_L_upper
import Submission.Work.BMF.V4prelim

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.VK

/-- **Two-sided bounds for `ζ` on the half-plane `Re s > 1`.**

For complex `s` with `1 < Re s`,
`‖ζ(s)‖ ≤ 1 + 1/(Re s - 1)` and `1/ζ(Re s) ≤ ‖ζ(s)‖`, the second written with `ζ(Re s)` in the
form `(riemannZeta (s.re : ℂ)).re` (a positive real number there).

Upper bound: `ζ(s) = ∑_n n^{-s}` on `Re s > 1`, so `‖ζ(s)‖ ≤ ∑_n n^{-Re s} = ζ(Re s)`, and
`ζ(σ) ≤ 1 + 1/(σ-1)` is `Work.BMF.riemannZeta_norm_le_one_add_inv`
(`Submission/Work/BMF/V4prelim.lean`).  Lower bound: the Euler-product comparison
`1 ≤ ‖L(s,χ)‖ * ζ(Re s)` at `N = 1`, `χ = 1` is `Work.BMF.vk_L_lower`
(`Submission/Work/BMF/vk_L_lower.lean`, sorry-free), and
`DirichletCharacter.LFunction_modOne_eq` identifies `L(·, 1 mod 1)` with `riemannZeta`;
`Work.BMF.vk_L_upper` gives the reverse comparison and can also be used for the upper bound. -/
theorem zeta_norm_two_sided {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ 1 + 1 / (s.re - 1) ∧
      ((riemannZeta (s.re : ℂ)).re)⁻¹ ≤ ‖riemannZeta s‖ := by
  constructor
  · -- Upper bound: `‖L(s, χ₀)‖ ≤ ζ(Re s)` for the trivial character `χ₀` mod `1`, whose
    -- `L`-function is `ζ`, combined with `ζ(σ) ≤ 1 + 1/(σ - 1)`.
    have h := Work.BMF.vk_L_upper (1 : DirichletCharacter ℂ 1) (s := s) hs
    rw [DirichletCharacter.LFunction_modOne_eq] at h
    have h2 := Work.BMF.riemannZeta_re_le_one_add_inv s.re hs
    linarith
  · -- Lower bound: `1 ≤ ‖L(s, χ₀)‖ * ζ(Re s)` for the trivial character `χ₀` mod `1`, and
    -- `ζ(Re s) > 0`, so dividing by `ζ(Re s)` gives `1/ζ(Re s) ≤ ‖ζ(s)‖`.
    have h := Work.BMF.vk_L_lower (1 : DirichletCharacter ℂ 1) (s := s) hs
    rw [DirichletCharacter.LFunction_modOne_eq] at h
    have hζpos : 0 < (riemannZeta (s.re : ℂ)).re := riemannZeta_re_pos_of_one_lt hs
    rw [← one_div, div_le_iff₀ hζpos]
    linarith

end Work.BMF.VK
