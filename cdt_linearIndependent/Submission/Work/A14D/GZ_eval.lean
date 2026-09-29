import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.H_conv_alt
import Submission.Work.C17I.Gfun_repr

namespace Work.A14D

open Complex Metric Filter
open scoped BigOperators

/-- The coefficient bound of `H = aH_A+bH_B+cH_C` at rate `ρ = 5/6`, in the shape needed by
`Work.C17I.sympSym_tsum_eq`. -/
lemma HZ_coeff_bound_six_fifths (a b c : ℤ) (hRel : Submission.CDTPlan.ARel a b c) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
      ‖((PowerSeries.coeff k (Submission.CDTPlan.HZ a b c) : ℚ) : ℂ)‖ ≤ C * (6 / 5 : ℝ) ^ k := by
  obtain ⟨C, hC0, hb⟩ := Hcoef_bound a b c hRel (show (0 : ℝ) < 5 / 6 by norm_num)
    (show (5 / 6 : ℝ) < 1 by norm_num)
  refine ⟨C, hC0, fun k => ?_⟩
  have hk := hb k
  rw [div_eq_mul_inv, div_pow, inv_div, ← div_pow] at hk
  simpa only [Work.ALift.hcoef] using hk

/-- The symmetrised A-side series evaluated at `y = yC z = z²/(z−1)`: for `‖z‖ ≤ 39/100`,
`Σ_k [y^k](GZ a b c) · (yC z)^k = Hfun a b c z + Hfun a b c (wC z)`, i.e.
`(Sym⁺H)∘y = H + H∘w`, the substitution identity `Submission.CDT.sympSym_subst` transported to
functions.  Proof: apply the proved `Work.C17I.sympSym_tsum_eq` with `H = HZ a b c`; its hypothesis
`‖[x^k]H‖ ≤ C₀·(6/5)^k` is `Work.A14D.H_conv_alt.Hcoef_bound` with `ρ = 5/6` (whose `hcoef` is by
definition the coefficient sequence of `HZ a b c`); the two sums on the right are `Hfun a b c z`
and `Hfun a b c (z/(z−1))` by the definition of `Hfun`, and `wC z = z/(z-1)`. -/
theorem GZ_eval (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c) :
    ∀ z : ℂ, ‖z‖ ≤ (39 : ℝ) / 100 →
      (∑' n : ℕ, ((PowerSeries.coeff n (Submission.CDTPlan.GZ a b c) : ℚ) : ℂ) * (yC z) ^ n)
        = Hfun a b c z + Hfun a b c (wC z) := by
  intro z hz
  obtain ⟨C₀, hC₀pos, hP⟩ := HZ_coeff_bound_six_fifths a b c h
  have hmain := Work.C17I.sympSym_tsum_eq (H := Submission.CDTPlan.HZ a b c) hC₀pos hP hz
  simpa only [Submission.CDTPlan.GZ, Hfun, wC, Work.C17.yC, yC] using hmain

end Work.A14D
