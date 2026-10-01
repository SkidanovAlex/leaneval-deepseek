/-
# Area 7 — monotonicity of `λ ↦ e^{-aλ} / w(λ)` off the origin

Same content as `Work.A7.ExpWf_antitone`, but for the (larger) domain `ℝ \ {0}`: whenever
`x ≤ y` and both are non-zero,

  `e^{-a y}/w(y) ≤ e^{-a x}/w(x)`,   `a = 49/10`.

The key point is that the identity

  `e^{-a u}/w(u) = (e^{-(37/15)u} - e^{-(23/6)u})/u = ∫_{37/15}^{23/6} e^{-tu} dt`

holds for *every* `u ≠ 0` (the two exponentials are integrated over a range of `t ≥ 0`), and an
integral of the decreasing family `u ↦ e^{-tu}` (`t ≥ 0`) is itself decreasing on all of `ℝ`.
Everything reduces to the same elementary integral comparison as in `ExpWf_antitone`.
-/
import Mathlib
import Submission.Work.LinnikAreas.A7.Defs

namespace Work.A7

open Work.LinnikContract

/-- `∫_b^c e^{-tλ} dt = (e^{-bλ} - e^{-cλ})/λ` for `λ ≠ 0`. -/
private lemma integral_exp_neg_mul (b c lam : ℝ) (hl : lam ≠ 0) :
    ∫ t in b..c, Real.exp (-(t*lam)) = (Real.exp (-(b*lam)) - Real.exp (-(c*lam)))/lam := by
  have hderiv : ∀ t ∈ Set.uIcc b c,
      HasDerivAt (fun t : ℝ => -(1/lam) * Real.exp (-(t*lam))) (Real.exp (-(t*lam))) t := by
    intro t _
    have h : HasDerivAt (fun y : ℝ => Real.exp (-(y*lam)))
        (Real.exp (-(t*lam)) * (-lam)) t := by
      have h0 : HasDerivAt (fun y : ℝ => -(y*lam)) (-lam) t := by
        have h1 := ((hasDerivAt_id t).mul_const lam).const_mul (-1)
        simpa [neg_mul, one_mul] using h1
      simpa using h0.exp
    have h3 := h.const_mul (-(1/lam))
    have h4 : -(1/lam) * (Real.exp (-(t*lam)) * -lam) = Real.exp (-(t*lam)) := by
      field_simp
    rwa [h4] at h3
  have hint : IntervalIntegrable (fun t : ℝ => Real.exp (-(t*lam))) MeasureTheory.volume b c :=
    (by fun_prop : Continuous fun t : ℝ => Real.exp (-(t*lam))).intervalIntegrable b c
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  field_simp
  ring

/-- For `0 ≤ b ≤ c` the function `λ ↦ (e^{-bλ} - e^{-cλ})/λ` is antitone on `ℝ \ {0}`. -/
private lemma antitone_exp_neg_sub_div_nonzero {b c : ℝ} (hb : 0 ≤ b) (hbc : b ≤ c) :
    AntitoneOn (fun u : ℝ => (Real.exp (-(b*u)) - Real.exp (-(c*u)))/u) {u : ℝ | u ≠ 0} := by
  intro x hx y hy hxy
  show (Real.exp (-(b*y)) - Real.exp (-(c*y)))/y
      ≤ (Real.exp (-(b*x)) - Real.exp (-(c*x)))/x
  rw [← integral_exp_neg_mul b c y hy, ← integral_exp_neg_mul b c x hx]
  apply intervalIntegral.integral_mono_on hbc
  · exact (by fun_prop : Continuous fun t : ℝ => Real.exp (-(t*y))).intervalIntegrable b c
  · exact (by fun_prop : Continuous fun t : ℝ => Real.exp (-(t*x))).intervalIntegrable b c
  · intro t ht
    have ht0 : 0 ≤ t := le_trans hb ht.1
    apply Real.exp_le_exp.2
    nlinarith [mul_le_mul_of_nonneg_left hxy ht0]

/-- `e^{-aλ}/w(λ) = (e^{-(37/15)λ} - e^{-(23/6)λ})/λ`, with `a = 49/10`, for `λ ≠ 0`. -/
private lemma exp_neg_a_div_Wf (u : ℝ) (hu : u ≠ 0) :
    Real.exp (-((49:ℝ)/10*u)) / Work.LinnikAreas.A7.Wf u
      = (Real.exp (-((37:ℝ)/15*u)) - Real.exp (-((23:ℝ)/6*u)))/u := by
  have hexp1 : Real.exp (-((37:ℝ)/15*u))
      = Real.exp (-((49:ℝ)/10*u)) * Real.exp ((73:ℝ)/30*u) := by
    rw [← Real.exp_add]; congr 1; ring
  have hexp2 : Real.exp (-((23:ℝ)/6*u))
      = Real.exp (-((49:ℝ)/10*u)) * Real.exp ((16:ℝ)/15*u) := by
    rw [← Real.exp_add]; congr 1; ring
  have hden : Real.exp ((73:ℝ)/30*u) - Real.exp ((16:ℝ)/15*u) ≠ 0 := by
    intro h
    have h2 : Real.exp ((73:ℝ)/30*u) = Real.exp ((16:ℝ)/15*u) := sub_eq_zero.mp h
    have h3 := Real.exp_injective h2
    have : u = 0 := by linarith
    exact hu this
  simp only [Work.LinnikAreas.A7.Wf, Work.LinnikContract.wHB]
  rw [hexp1, hexp2]
  field_simp

theorem ExpWf_antitone_ne : ∀ {x y : ℝ}, x ≤ y → x ≠ 0 → y ≠ 0 →
    Real.exp (-((49:ℝ)/10 * y)) / Work.LinnikAreas.A7.Wf y
      ≤ Real.exp (-((49:ℝ)/10 * x)) / Work.LinnikAreas.A7.Wf x := by
  intro x y hxy hx hy
  rw [exp_neg_a_div_Wf y hy, exp_neg_a_div_Wf x hx]
  exact antitone_exp_neg_sub_div_nonzero (by norm_num : (0:ℝ) ≤ 37/15)
    (by norm_num : (37:ℝ)/15 ≤ 23/6) hx hy hxy

end Work.A7
