import Mathlib
import Submission.Work.BMF.liouville.zeta_tw_perron

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open Finset

/-- `‖zetaTwSum u x‖ ≤ Chebyshev.psi x`: termwise, `‖Λ(n) n^{-iu}‖ = Λ(n)` for `n ≥ 1`, and
`Σ_{n ≤ ⌊x⌋₊} Λ(n) = ψ ⌊x⌋₊ = ψ x`. -/
lemma norm_zetaTwSum_le_psi (u x : ℝ) : ‖zetaTwSum u x‖ ≤ Chebyshev.psi x := by
  have hcongr : zetaTwSum u x =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * (u : ℂ))) := by
    rw [zetaTwSum]
    congr 1
  rw [hcongr, Chebyshev.psi]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro n hn
  have hnpos : 0 < n := by
    simp only [Finset.mem_Ioc] at hn; exact hn.1
  have hnorm : ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * (u : ℂ)))‖
      = ArithmeticFunction.vonMangoldt n := by
    rw [norm_mul, Complex.norm_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg)]
    rw [Complex.norm_natCast_cpow_of_pos hnpos]
    have hre : (-(Complex.I * (u : ℂ))).re = 0 := by simp
    rw [hre, Real.rpow_zero, mul_one]
  rw [hnorm]

/-- `‖x^{1-iu}/(1-iu)‖ ≤ x` for `x > 0`: the numerator has modulus `x^{Re(1-iu)} = x` and the
denominator has modulus `≥ |Re(1-iu)| = 1`. -/
lemma norm_cpow_div_le (x : ℝ) (hx : 0 < x) (u : ℝ) :
    ‖(x : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))‖ ≤ x := by
  rw [Complex.norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre : (1 - Complex.I * (u : ℂ)).re = 1 := by simp
  rw [hre, Real.rpow_one]
  have hden : 1 ≤ ‖(1 : ℂ) - Complex.I * (u : ℂ)‖ := by
    simpa [hre] using Complex.abs_re_le_norm (1 - Complex.I * (u : ℂ))
  exact div_le_self hx.le hden

/-- The crude bound `‖Σ_{n ≤ x} Λ(n) n^{-iu} − x^{1-iu}/(1-iu)‖ ≤ C x` on a bounded range of
`x`, with `C` independent of `u` (used for the small-`x` case of `zetaTwSum_sub_main_le`).

Route: `‖zetaTwSum u x‖ ≤ Σ_{n ≤ ⌊x⌋₊} Λ(n) = Chebyshev.psi ⌊x⌋₊ ≤ Chebyshev.psi x` and
`Chebyshev.psi_le_const_mul_self` gives `psi x ≤ (log 4 + 4) * x`; and
`‖x^{1-iu}/(1-iu)‖ = x/‖1-iu‖ ≤ x`. -/
lemma zetaTwSum_small_x (X : ℝ) (hX : 3 ≤ X) :
    ∃ C, 0 < C ∧ ∀ x : ℝ, 3 ≤ x → x ≤ X → ∀ u : ℝ,
      ‖zetaTwSum u x - (x : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))‖
        ≤ C * x := by
  refine ⟨Real.log 4 + 5, ?_, ?_⟩
  · have : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  · intro x hx _ u
    have hxpos : 0 < x := by linarith
    calc
      ‖zetaTwSum u x - (x : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))‖
          ≤ ‖zetaTwSum u x‖
              + ‖(x : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))‖ :=
            norm_sub_le _ _
      _ ≤ Chebyshev.psi x + x := add_le_add (norm_zetaTwSum_le_psi u x) (norm_cpow_div_le x hxpos u)
      _ ≤ (Real.log 4 + 4) * x + x :=
            add_le_add (Chebyshev.psi_le_const_mul_self hxpos.le) le_rfl
      _ = (Real.log 4 + 5) * x := by ring

end Work.BMF.liouville
