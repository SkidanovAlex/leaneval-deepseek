/-
# ZeroFreeTables — `ksum_trigPoly_pointwise`

Pointwise (single-`n`) version of the "trigonometric polynomial is non-negative"
input.

Given `f ≥ 0`, a Chebyshev polynomial `∑ₖ cₖ Tₖ` which is non-negative on `[-1,1]`,
and a Dirichlet character `χ` of level `q`, the sum

`∑ₖ cₖ · Λ(n) · ℜ(χᵏ(n) / n^(β + i k γ)) · f(log n / L)`

is non-negative for every `n ≥ 1`.

The mathematical content is the classical observation that, for `u` a unit of
`ZMod q`, the point `w = χ(u)·n^{-iγ}` lies on the complex unit circle, and for
`w` on the unit circle `ℜ(wᵏ) = Tₖ(ℜ w)`; the splitting
`ℜ(χᵏ(n)/n^(β+i kγ)) = n^{-β} · ℜ(χᵏ(n)·n^{-i kγ})` is `re_div_cpow_eq` from
`TrigPolyPos`.  When `n` is *not* a unit of `ZMod q` every character value
`χᵏ(n)` vanishes, so every term of the sum is already zero.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.TrigPolyPos

namespace Work.ZeroFreeTables

theorem ksum_trigPoly_pointwise {q : ℕ} [NeZero q] {f : ℝ → ℝ} (hf : ∀ t : ℝ, 0 ≤ f t)
    {L β γ : ℝ} {c : ℕ → ℝ} {d : ℕ}
    (hP : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      0 ≤ ∑ k ∈ Finset.range (d + 1), c k * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval x)
    (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ ∑ k ∈ Finset.range (d + 1), c k *
      ((ArithmeticFunction.vonMangoldt n : ℝ) *
        (((χ ^ k) (n : ZMod q)) / (n : ℂ) ^ ((β : ℂ) + ((k : ℝ) * γ : ℂ) * Complex.I)).re
        * f (Real.log n / L)) := by
  by_cases hunit : IsUnit (n : ZMod q)
  · -- `n` is a unit of `ZMod q`: the point `w = χ(n) · n^{-iγ}` lies on the unit circle
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    set z : ℂ := (n : ℂ) ^ (-((γ : ℂ) * Complex.I)) with hz
    set w : ℂ := χ (n : ZMod q) * z with hw
    have hnormχ : ‖χ (n : ZMod q)‖ = 1 := by
      have hN : χ ^ Fintype.card (ZMod q)ˣ = 1 := MulChar.pow_card_eq_one χ
      have h1 : χ (n : ZMod q) ^ Fintype.card (ZMod q)ˣ = 1 := by
        rw [← IsUnit.unit_spec hunit, ← MulChar.pow_apply_coe χ _ hunit.unit, hN,
          MulChar.one_apply_coe]
      exact Complex.norm_eq_one_of_pow_eq_one h1 Fintype.card_ne_zero
    have hnormz : ‖z‖ = 1 := by
      rw [hz]
      have hcast : (n : ℂ) = ((n : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
      simp
    have hwnorm : ‖w‖ = 1 := by
      rw [hw, Complex.norm_mul, hnormχ, hnormz, one_mul]
    have hS : 0 ≤ ∑ k ∈ Finset.range (d + 1), c k * (w ^ k).re :=
      trigPoly_eval_nonneg hP hwnorm
    have hkey : ∀ k : ℕ,
        (χ ^ k) (n : ZMod q) * (n : ℂ) ^ (-(((k : ℝ) * γ : ℂ) * Complex.I)) = w ^ k := by
      intro k
      have hcp : (n : ℂ) ^ (-(((k : ℝ) * γ : ℂ) * Complex.I)) = z ^ k := by
        rw [hz]
        have harg : -(((k : ℝ) * γ : ℂ) * Complex.I) = (↑k : ℂ) * (-((γ : ℂ) * Complex.I)) := by
          push_cast; ring
        rw [harg, Complex.cpow_nat_mul]
      rw [hw, hcp, mul_pow, ← IsUnit.unit_spec hunit, MulChar.pow_apply_coe χ k hunit.unit]
    have hterm : ∀ k ∈ Finset.range (d + 1),
        c k * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          (((χ ^ k) (n : ZMod q)) / (n : ℂ) ^ ((β : ℂ) + ((k : ℝ) * γ : ℂ) * Complex.I)).re
          * f (Real.log n / L))
        = ((ArithmeticFunction.vonMangoldt n : ℝ) * f (Real.log n / L) * (n : ℝ) ^ (-β))
            * (c k * (w ^ k).re) := by
      intro k _
      rw [re_div_cpow_eq (χ ^ k) hn β (((k : ℝ) * γ : ℂ) * Complex.I), hkey k]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    exact mul_nonneg (mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hf _))
      (Real.rpow_nonneg (by positivity) _)) hS
  · -- `n` is not a unit: every character value `χᵏ(n)` vanishes, so every term is `0`
    have hzero : ∀ k : ℕ, (χ ^ k) (n : ZMod q) = 0 := fun k => MulChar.map_nonunit (χ ^ k) hunit
    rw [Finset.sum_eq_zero]
    intro k _
    rw [hzero k]
    simp

end Work.ZeroFreeTables
