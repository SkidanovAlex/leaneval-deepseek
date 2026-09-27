import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.la_nnas

/-! # `not_flat_of_unNear`

A fan element `fan a h ε u` (with word `ε`, parameter `u`) is never *flat* along a regular
chain whose far end is `1/4`-near the unstable axis centre `1/2 + 2ℤ`: there is a threshold
`η > 0`, uniform in the chain, the word and the map `h`, such that whenever

* `Pₙ` is a regular chain of the equichordal relation with `P₀ = fan a h ε u`,
* `P₋N` is `UnNear a _ (1/4)`, and
* `fan a h ε u` is close to the stable-axis point `fan a h ε 0` — both in the `x`-coordinate
  (`< η`) and in the semi-projective ratio `|y| / |x - a/2|` (`< η`),

then we reach a contradiction.

The mathematics is the parity separation of `Work.EQ.LaNnas.no_near_axis_segment`: the second
and third bullets say exactly that `P₀ = fan a h ε u` is `LaNnas.SnNear a (fan a h ε 0) η`,
and `fan a h ε 0` sits on the stable coset `-1/2 + 2ℤ` by hypothesis. Walking the chain
*backwards* from `P₀` to `P₋N` multiplies the near-axis radius by at most `nnC a ^ N`
(`LaNnas.propagate_bwd`), so at index `-N` we get an `SnNear` radius `nnD a ≤ 1/4`; a point
cannot be simultaneously `UnNear` with radius `1/4` and `SnNear` with radius `nnD a`
(`LaNnas.not_un_and_sn`, the two cosets are distance `1` apart). We take
`η = nnD a / nnC a ^ N`, which also guarantees the radius stays below the threshold `nnD a`
throughout the propagation.

This is the case-`l > 0` argument of `Submission.Work.EQ.LaTB.flattening_impossible`.
-/

namespace Work.EQ.LaTB

open Work.EQ Work.EQ.LaNnas

theorem not_flat_of_unNear {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (N : ℕ) :
    ∃ η : ℝ, 0 < η ∧ ∀ {h : ℂ → ℂ} {P : ℤ → ℂ × ℂ} {u : ℂ} {ε : List Bool} {Y : ℤ},
      (∀ n : ℤ, Work.EQ.RegPair a (P n) (P (n + 1))) →
      P 0 = Work.EQ.fan a h ε u →
      Work.EQ.LaNnas.UnNear a (P (-(N : ℤ))) (1 / 4) →
      (Work.EQ.fan a h ε 0).1 = -1 / 2 + 2 * (Y : ℂ) →
      ‖(Work.EQ.fan a h ε u).1 - (Work.EQ.fan a h ε 0).1‖ < η →
      ‖(Work.EQ.fan a h ε u).2‖ < η * ‖(Work.EQ.fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ → False := by
  have hηpos : 0 < nnD a := nnD_pos ha1
  have hCpos : 0 < nnC a := nnC_pos ha0 ha1
  have hC1 : 1 ≤ nnC a := nnC_ge_one ha0 ha1
  have hDq : nnD a ≤ 1 / 4 := nnD_le_quarter ha0
  refine ⟨nnD a / nnC a ^ N, div_pos hηpos (pow_pos hCpos N), ?_⟩
  intro h P u ε Y hreg hP0 hUn hctr hx hy
  -- re-index the chain so that it runs from `-(N : ℤ)` (index `0`) to `0` (index `N`)
  set Q : ℕ → ℂ × ℂ := fun j => P (-(N : ℤ) + (j : ℤ)) with hQdef
  have hQN : Q N = P 0 := by simp [hQdef]
  have hQ0 : Q 0 = P (-(N : ℤ)) := by simp [hQdef]
  -- `SnNear` at the flat end `P 0 = fan a h ε u`, with the axis centre `-1/2 + 2Y`
  have hS0 : SnNear a (Q N) (nnD a / nnC a ^ N) := by
    rw [hQN, hP0]
    exact ⟨Y, by rw [← hctr]; exact le_of_lt hx, le_of_lt hy⟩
  have hstep : ∀ j : ℕ, j < N → RegPair a (Q j) (Q (j + 1)) := by
    intro j hj
    simp only [hQdef]
    rw [show (((j + 1 : ℕ)) : ℤ) = (j : ℤ) + 1 by push_cast; ring,
        show -(N : ℤ) + ((j : ℤ) + 1) = (-(N : ℤ) + (j : ℤ)) + 1 by ring]
    exact hreg (-(N : ℤ) + (j : ℤ))
  have hsmall : ∀ n : ℕ, n ≤ N → (nnD a / nnC a ^ N) * nnC a ^ n ≤ nnD a := by
    intro n hn
    have hpow : nnC a ^ n ≤ nnC a ^ N := pow_le_pow_right₀ hC1 hn
    rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hCpos N)]
    exact mul_le_mul_of_nonneg_left hpow (le_of_lt hηpos)
  have hprop := propagate_bwd ha0 ha1 N Q (nnD a / nnC a ^ N) hstep (by positivity) hsmall hS0
  have hSN : SnNear a (P (-(N : ℤ))) (nnD a) := by
    have h1 : (nnD a / nnC a ^ N) * nnC a ^ N = nnD a := by
      rw [div_mul_cancel₀]; exact pow_ne_zero N (ne_of_gt hCpos)
    have h2 := hprop.mono (le_of_eq h1)
    rwa [hQ0] at h2
  exact not_un_and_sn (by linarith) hUn hSN

end Work.EQ.LaTB
