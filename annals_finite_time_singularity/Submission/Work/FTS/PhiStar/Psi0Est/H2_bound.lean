import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Psi0Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Psi0Est

/-!
# `H2_bound`: the elementary `sin 2θ`-moment estimate at the right endpoint

For `θ ∈ (π/4, π/2)` we prove

`|(5/4)·sin 2θ − 15·(∫_θ^{π/2} sin²t cos³t dt)/(2 cos³θ)| ≤ 10·sin 2θ`.

The integral is the elementary polynomial `Ψ_S θ = 2/15 − sin³θ/3 + sin⁵θ/5`
(`Work.FTS.PhiStar.PsiS_eq_integral`), so the whole statement is a polynomial inequality
in `s = sin θ`, `c = cos θ` on the range where `s² > 1/2`.

Writing `B := 15·Ψ_S θ/(2c³) = (2 − 5s³ + 3s⁵)/(2c³)` and `sin 2θ = 2sc`, the two halves of
`|A − B| ≤ C` reduce to

* `B ≤ (45/4)·(2sc)`, i.e. `2 − 5s³ + 3s⁵ ≤ 45 s c⁴`, which after `c² = 1 − s²` is the
  perfect-square identity `45sc⁴ − 2 + 5s³ − 3s⁵ = (s−1)²(42s³ + 84s² + 41s − 2) ≥ 0`
  (with `84s² > 42 > 2` supplying the constant term);
* `B ≥ 0`, i.e. `2 − 5s³ + 3s⁵ = (1−s)²(3s³ + 6s² + 4s + 2) ≥ 0`.

Both are pure polynomial positivity; the only analysis is the range restriction, which is
used exactly through `s > 0`, `c > 0` and `s² > 1/2` (the latter from `cos 2θ < 0`).
-/

theorem H2_bound {θ : ℝ} (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    |(5 / 4) * Real.sin (2 * θ)
      - 15 * (∫ t in θ..(Real.pi / 2), Real.sin t ^ 2 * Real.cos t ^ 3)
        / (2 * Real.cos θ ^ 3)| ≤ 10 * Real.sin (2 * θ) := by
  have hle : θ ≤ Real.pi / 2 := le_of_lt hθ.2
  rw [← Work.FTS.PhiStar.PsiS_eq_integral θ hle]
  set s := Real.sin θ with hs_def
  set c := Real.cos θ with hc_def
  have hs : 0 < s := by
    rw [hs_def]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos, hθ.1])
      (by linarith [Real.pi_pos, hθ.2])
  have hc : 0 < c := by
    rw [hc_def]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  have hs2 : (1 : ℝ) / 2 < s ^ 2 := by
    rw [hs_def]
    have h1 : Real.pi / 2 < 2 * θ := by linarith [hθ.1]
    have h2 : 2 * θ < Real.pi + Real.pi / 2 := by linarith [hθ.2, Real.pi_pos]
    have hcos : Real.cos (2 * θ) < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt h1 h2
    have h : Real.cos (2 * θ) = 1 - 2 * Real.sin θ ^ 2 := by
      rw [Real.cos_two_mul']
      nlinarith [Real.sin_sq_add_cos_sq θ]
    linarith
  have hsc : s ^ 2 + c ^ 2 = 1 := by
    rw [hs_def, hc_def]; exact Real.sin_sq_add_cos_sq θ
  have hPsiS : Work.FTS.PhiStar.PsiS θ = 2 / 15 - s ^ 3 / 3 + s ^ 5 / 5 := by
    simp only [Work.FTS.PhiStar.PsiS]
    rw [← hs_def]
  rw [hPsiS, Real.sin_two_mul]
  rw [← hs_def, ← hc_def]
  -- the key polynomial inequality `2 − 5s³ + 3s⁵ ≤ 45 s c⁴`
  have hkey : 2 - 5 * s ^ 3 + 3 * s ^ 5 ≤ 45 * s * c ^ 4 := by
    have hc2 : c ^ 2 = 1 - s ^ 2 := by linarith
    have hc4 : c ^ 4 = (1 - s ^ 2) ^ 2 := by
      have h1 : c ^ 4 = (c ^ 2) ^ 2 := by ring
      rw [h1, hc2]
    have hfac : 45 * s * c ^ 4 - 2 + 5 * s ^ 3 - 3 * s ^ 5
        = (s - 1) ^ 2 * (42 * s ^ 3 + 84 * s ^ 2 + 41 * s - 2) := by
      rw [hc4]; ring
    have hQ : 0 ≤ 42 * s ^ 3 + 84 * s ^ 2 + 41 * s - 2 := by
      have hs3 : 0 ≤ s ^ 3 := by positivity
      nlinarith [hs, hs2, hs3]
    have h2 := mul_nonneg (sq_nonneg (s - 1)) hQ
    linarith [hfac, h2]
  have hB : 15 * (2 / 15 - s ^ 3 / 3 + s ^ 5 / 5) / (2 * c ^ 3) ≤ (45 / 4) * (2 * s * c) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * c ^ 3)]
    nlinarith [hkey]
  have hB0 : 0 ≤ 15 * (2 / 15 - s ^ 3 / 3 + s ^ 5 / 5) / (2 * c ^ 3) := by
    apply div_nonneg _ (by positivity)
    have hfac2 : 2 - 5 * s ^ 3 + 3 * s ^ 5 = (1 - s) ^ 2 * (3 * s ^ 3 + 6 * s ^ 2 + 4 * s + 2) :=
      by ring
    have hpos : 0 < 3 * s ^ 3 + 6 * s ^ 2 + 4 * s + 2 := by positivity
    have hprod := mul_nonneg (sq_nonneg (1 - s)) (le_of_lt hpos)
    linarith [hfac2, hprod]
  rw [abs_le]
  constructor
  · nlinarith [hB]
  · have hx : 0 < 2 * s * c := by positivity
    nlinarith [hB0, hx]

end Work.FTS.PhiStar.Psi0Est
