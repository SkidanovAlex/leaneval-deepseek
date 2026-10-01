/-
# Area 7 — monotonicity of `λ ↦ e^{-aλ} / w(λ)`

The density weight of HB Lemma 11.1 is `w(λ) = λ / (e^{73λ/30} - e^{16λ/15})`
(`Work.LinnikAreas.A7.Wf = Work.LinnikContract.wHB`).  The function used in the
Assembly of Area 7 is `λ ↦ e^{-aλ}/w(λ)` with `a = L - 2K = 49/10`, and it has to
be *antitone* on `(0, ∞)` (a smaller value of the least zero-parameter gives a
larger weight).

The whole content is the elementary observation

  `e^{-aλ}/w(λ) = (e^{-(37/15)λ} - e^{-(23/6)λ})/λ = ∫_b^c e^{-tλ} dt`,  `b = 37/15 ≤ c = 23/6`,

since `73/30 - 49/10 = -37/15` and `16/15 - 49/10 = -23/6`.  An integral of the
decreasing family `λ ↦ e^{-tλ}` (`t ≥ 0`) is itself decreasing, which gives the
result.  The general statement for `0 ≤ b ≤ c` is `antitone_exp_neg_sub_div`.
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

/-- For `0 ≤ b ≤ c` the function `λ ↦ (e^{-bλ} - e^{-cλ})/λ` is antitone on `(0, ∞)`. -/
private lemma antitone_exp_neg_sub_div {b c : ℝ} (hb : 0 ≤ b) (hbc : b ≤ c) :
    AntitoneOn (fun u : ℝ => (Real.exp (-(b*u)) - Real.exp (-(c*u)))/u) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := hx
  have hy0 : 0 < y := hy
  show (Real.exp (-(b*y)) - Real.exp (-(c*y)))/y
      ≤ (Real.exp (-(b*x)) - Real.exp (-(c*x)))/x
  rw [← integral_exp_neg_mul b c y (ne_of_gt hy0),
      ← integral_exp_neg_mul b c x (ne_of_gt hx0)]
  apply intervalIntegral.integral_mono_on hbc
  · exact (by fun_prop : Continuous fun t : ℝ => Real.exp (-(t*y))).intervalIntegrable b c
  · exact (by fun_prop : Continuous fun t : ℝ => Real.exp (-(t*x))).intervalIntegrable b c
  · intro t ht
    have ht0 : 0 ≤ t := le_trans hb ht.1
    apply Real.exp_le_exp.2
    nlinarith [mul_le_mul_of_nonneg_left hxy ht0]

/-- `e^{-aλ}/w(λ) = (e^{-(37/15)λ} - e^{-(23/6)λ})/λ`, with `a = 49/10`. -/
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

theorem ExpWf_antitone :
    ∀ {x y : ℝ}, 0 < x → x ≤ y →
      Real.exp (-((49:ℝ)/10*y)) / Work.LinnikAreas.A7.Wf y
        ≤ Real.exp (-((49:ℝ)/10*x)) / Work.LinnikAreas.A7.Wf x := by
  intro x y hx hxy
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  rw [exp_neg_a_div_Wf y (ne_of_gt hy), exp_neg_a_div_Wf x (ne_of_gt hx)]
  exact antitone_exp_neg_sub_div (by norm_num : (0:ℝ) ≤ 37/15)
    (by norm_num : (37:ℝ)/15 ≤ 23/6) hx hy hxy

end Work.A7
