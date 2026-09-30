import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.VKGrowthDefs
import Submission.Work.BMF.VKGrowth
import Submission.Work.BMF.vk_exp_sum
import Submission.Work.BMF.VKChain.hurwitz_growth_abs_vk

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! **V2 of the Matomäki–Radziwiłł–Tao–Teräväinen–Ziegler chain: growth of `L(s,χ)` near `σ = 1`.**

Route. From the Vinogradov–Korobov exponential-sum input `Work.BMF.vk_exp_sum` (node V1) the module
`Submission/Work/BMF/VKGrowth.lean` derives

* (`LFunction_growth_of_hurwitz`) `‖L(σ+it,χ)‖ ≤ 2A·N·(log(|t|+3))^{6/7}` for every character
  `χ mod N` from the Hurwitz-zeta growth bound `‖ζ(σ+it,a)‖ ≤ A(a^{-σ} + (log(|t|+3))^{6/7})`
  in the strip `σ ≥ 1 - c (log(|t|+3))^{-6/7}`;

and the delegated lemma `Work.BMF.VKChain.hurwitz_growth_abs_vk` supplies that Hurwitz bound from
the VK input (its proof decomposes the shift-difference series `ζ(s,a) - ζ(s) = Σ_m
((m+a)^{-s} - (m+1)^{-s})` into dyadic blocks: the head `m < K₀ = exp((log t/c_vk)^{6/7})`, the
VK blocks `K₀ ≤ K ≤ |t|` and the Kusmin–Landau blocks `|t| < K ≤ |t|²`, all uniformly in
`a ∈ (0,1]`, with `a = 0` handled by the Riemann-zeta case). -/

namespace Work.BMF

open scoped BigOperators

noncomputable section

theorem L_growth_VK :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (σ t : ℝ),
      3 ≤ |t| → 1 - c * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ σ → σ ≤ 2 →
        ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          A * N * Real.log (|t| + 3) ^ (6 / 7 : ℝ) := by
  obtain ⟨C, c, hC, hc, hVK⟩ := Work.BMF.vk_exp_sum
  have hcvk0 : 0 < min c 1 := lt_min hc zero_lt_one
  have hcvk1 : min c 1 ≤ 1 := min_le_right _ _
  have hVKi : VKExpInput C (min c 1) := by
    refine ⟨hC, hcvk0, ?_⟩
    intro N t hN hNt hrange u hu hu1 R hR hR2
    have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have hN1 : (1 : ℝ) ≤ N := by linarith
    have hc1le : min c 1 ≤ c := min_le_left _ _
    have hrange' : Real.log t ≤ c * Real.log N ^ (7 / 6 : ℝ) :=
      le_trans hrange (mul_le_mul_of_nonneg_right hc1le (Real.rpow_nonneg hlogN.le _))
    refine le_trans (hVK N t hN hNt hrange' u hu hu1 R hR hR2) ?_
    set θ : ℝ := (Real.log N / Real.log t) ^ 2 / Real.log (Real.log t / Real.log N + 2)
      with hθ
    have hθpos : 0 < θ := by
      rw [hθ]
      have h1 : 0 < Real.log (Real.log t / Real.log N + 2) :=
        Real.log_pos (by have := div_pos hlogt hlogN; linarith)
      positivity
    have hlogarg : 0 < Real.log (Real.log t / Real.log N + 2) :=
      Real.log_pos (by have := div_pos hlogt hlogN; linarith)
    have hexp : 1 - c * (Real.log N / Real.log t) ^ 2 / Real.log (Real.log t / Real.log N + 2) ≤
        1 - min c 1 * (Real.log N / Real.log t) ^ 2 / Real.log (Real.log t / Real.log N + 2) := by
      have h1 : min c 1 * (Real.log N / Real.log t) ^ 2 ≤ c * (Real.log N / Real.log t) ^ 2 :=
        mul_le_mul_of_nonneg_right hc1le (sq_nonneg _)
      have h2 := div_le_div_of_nonneg_right h1 hlogarg.le
      linarith
    refine mul_le_mul_of_nonneg_left ?_ hC.le
    exact Real.rpow_le_rpow_of_exponent_le hN1 hexp
  obtain ⟨A, c', hA, hc', hc4, hHur⟩ :=
    Work.BMF.VKChain.hurwitz_growth_abs_vk hVKi hcvk0 hcvk1 hC
  exact ⟨2 * A, c', by positivity, hc',
    LFunction_growth_of_hurwitz hA hc' (le_trans hc4 (by norm_num)) hHur⟩

end

end Work.BMF
