import Mathlib

namespace Work.NN.Core

open scoped ContDiff

set_option linter.unusedVariables false

/-- Taylor's theorem with a polynomial remainder bound, in the precise shape needed by the
Newlander–Nirenberg development: if `ψ : ℝ → ℂ` is `k`-times continuously differentiable and its
`k`-th iterated derivative is bounded by `Sk` on `[0, k * h]`, then on that interval `ψ` is
approximated by its Taylor polynomial of degree `k - 1` at `0` with error at most
`t ^ k / (k - 1)! * Sk`.

This is obtained from Mathlib's `taylor_mean_remainder_bound` (with the `(k-1)!` constant, which is
weaker than the sharp `k!` of the integral form of Taylor's theorem) together with the identity
`taylorWithinEval ψ (k-1) s 0 t = ∑ l ∈ range k, (l!)⁻¹ * t ^ l • ψ^{(l)}(0)`. -/
theorem taylor_remainder_bound {k : ℕ} (hk : 1 ≤ k) (ψ : ℝ → ℂ) (h : ℝ) (hh : 0 < h)
    (hψ : ContDiff ℝ k ψ) (Sk : ℝ) (hSk0 : 0 ≤ Sk)
    (hSk : ∀ t ∈ Set.Icc 0 ((k : ℝ) * h), ‖iteratedDeriv k ψ t‖ ≤ Sk) :
    ∀ t ∈ Set.Icc 0 ((k : ℝ) * h),
      ‖ψ t - ∑ l ∈ Finset.range k, ((l.factorial : ℝ)⁻¹ * t ^ l) • iteratedDeriv l ψ 0‖
        ≤ t ^ k / ((k - 1).factorial : ℝ) * Sk := by
  -- Write `k = n + 1` so that Mathlib's Taylor theorem applies with its `n + 1`-index.
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  intro t ht
  have hb : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) * h := by positivity
  have huniq : UniqueDiffOn ℝ (Set.Icc 0 (((n + 1 : ℕ) : ℝ) * h)) := uniqueDiffOn_Icc hb
  have hmem0 : (0 : ℝ) ∈ Set.Icc 0 (((n + 1 : ℕ) : ℝ) * h) := ⟨le_refl 0, hb.le⟩
  -- The Taylor polynomial of degree `n` at `0` written as the explicit finite sum.
  have hsum : (∑ l ∈ Finset.range (n + 1),
        ((l.factorial : ℝ)⁻¹ * t ^ l) • iteratedDeriv l ψ 0)
      = taylorWithinEval ψ n (Set.Icc 0 (((n + 1 : ℕ) : ℝ) * h)) 0 t := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.mem_range] at hl
    rw [iteratedDerivWithin_eq_iteratedDeriv huniq
        (hψ.contDiffAt.of_le
          (by exact_mod_cast (Nat.le_succ_of_le (Nat.le_of_lt_succ hl)))) hmem0,
      sub_zero]
  -- Mathlib's Taylor theorem with a polynomial remainder bound.
  have hbound := taylor_mean_remainder_bound (f := ψ) (a := 0)
      (b := ((n + 1 : ℕ) : ℝ) * h) (C := Sk) (x := t) (n := n) hb.le hψ.contDiffOn ht
      (fun y hy => by
        rw [iteratedDerivWithin_eq_iteratedDeriv huniq hψ.contDiffAt hy]
        exact hSk y hy)
  rw [← hsum] at hbound
  refine hbound.trans_eq ?_
  rw [sub_zero]
  norm_num [Nat.add_sub_cancel]
  ring

end Work.NN.Core
